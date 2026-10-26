import V185TrunkScan22Chunk388

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3468434 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3468434 : Nat := 118140960795 + 3468434 * 2 ^ 59
def prefixEnd_3468434 : Nat := 4983230072969 + 3 ^ 40 * 3468434 * 2
def baseEnd_3468434 : Nat := 1187315840264391979815979

theorem tailTrace_3468434 : CollatzResearch.WordTrace tailWord_3468434 prefixEnd_3468434 1187315840264391979815979 := by
  unfold tailWord_3468434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626045179115863553003089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84336120477642302808008237 31626045179115863553003089)
  ·
    refine ⟨23719533884336897664752317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31626045179115863553003089 23719533884336897664752317)
    ·
      refine ⟨8894825206626336624282119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23719533884336897664752317 8894825206626336624282119)
      ·
        refine ⟨13342237809939504936423179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8894825206626336624282119 13342237809939504936423179)
        ·
          refine ⟨20013356714909257404634769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13342237809939504936423179 20013356714909257404634769)
          ·
            refine ⟨15010017536181943053476077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20013356714909257404634769 15010017536181943053476077)
            ·
              refine ⟨5628756576068228645053529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15010017536181943053476077 5628756576068228645053529)
              ·
                refine ⟨4221567432051171483790147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5628756576068228645053529 4221567432051171483790147)
                ·
                  refine ⟨6332351148076757225685221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221567432051171483790147 6332351148076757225685221)
                  ·
                    refine ⟨1187315840264391979815979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6332351148076757225685221 1187315840264391979815979)
                    ·
                      rfl

theorem cell22_3468434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3468434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468434 prefixEnd_3468434 := by exact prefixLift 3468434
  have htrace : WordTrace (prefixWord ++ tailWord_3468434) baseStart_3468434 baseEnd_3468434 := by
    simpa [prefixWord, tailWord_3468434, baseEnd_3468434] using wordTrace_append hprefix tailTrace_3468434
  have hstable : (prefixWord ++ tailWord_3468434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468434).length < 2 ^ (prefixWord ++ tailWord_3468434).sum := by decide
  have hdescent : baseEnd_3468434 < baseStart_3468434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468466 : List Nat := [3, 2, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3468466 : Nat := 118140960795 + 3468466 * 2 ^ 59
def prefixEnd_3468466 : Nat := 4983230072969 + 3 ^ 40 * 3468466 * 2
def baseEnd_3468466 : Nat := 395775598172784854338627

theorem tailTrace_3468466 : CollatzResearch.WordTrace tailWord_3468466 prefixEnd_3468466 395775598172784854338627 := by
  unfold tailWord_3468466
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626336963086880919294313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84336898568231682451451501 31626336963086880919294313)
  ·
    refine ⟨23719752722315160689470735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31626336963086880919294313 23719752722315160689470735)
    ·
      refine ⟨35579629083472741034206103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23719752722315160689470735 35579629083472741034206103)
      ·
        refine ⟨53369443625209111551309155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35579629083472741034206103 53369443625209111551309155)
        ·
          refine ⟨80054165437813667326963733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53369443625209111551309155 80054165437813667326963733)
          ·
            refine ⟨3752539004897515655951425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80054165437813667326963733 3752539004897515655951425)
            ·
              refine ⟨2814404253673136741963569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752539004897515655951425 2814404253673136741963569)
              ·
                refine ⟨2110803190254852556472677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814404253673136741963569 2110803190254852556472677)
                ·
                  refine ⟨395775598172784854338627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110803190254852556472677 395775598172784854338627)
                  ·
                    rfl

theorem cell22_3468466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3468466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468466 prefixEnd_3468466 := by exact prefixLift 3468466
  have htrace : WordTrace (prefixWord ++ tailWord_3468466) baseStart_3468466 baseEnd_3468466 := by
    simpa [prefixWord, tailWord_3468466, baseEnd_3468466] using wordTrace_append hprefix tailTrace_3468466
  have hstable : (prefixWord ++ tailWord_3468466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468466).length < 2 ^ (prefixWord ++ tailWord_3468466).sum := by decide
  have hdescent : baseEnd_3468466 < baseStart_3468466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468481 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3468481 : Nat := 118140960795 + 3468481 * 2 ^ 59
def prefixEnd_3468481 : Nat := 4983230072969 + 3 ^ 40 * 3468481 * 2
def baseEnd_3468481 : Nat := 1187331929324899523890835

theorem tailTrace_3468481 : CollatzResearch.WordTrace tailWord_3468481 prefixEnd_3468481 1187331929324899523890835 := by
  unfold tailWord_3468481
  simp only [CollatzResearch.WordTrace]
  refine ⟨126505894947293181238973297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84337263298195454159315531 126505894947293181238973297)
  ·
    refine ⟨94879421210469885929229973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126505894947293181238973297 94879421210469885929229973)
    ·
      refine ⟨4447472869240775902932655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94879421210469885929229973 4447472869240775902932655)
      ·
        refine ⟨6671209303861163854398983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447472869240775902932655 6671209303861163854398983)
        ·
          refine ⟨10006813955791745781598475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6671209303861163854398983 10006813955791745781598475)
          ·
            refine ⟨15010220933687618672397713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10006813955791745781598475 15010220933687618672397713)
            ·
              refine ⟨11257665700265714004298285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15010220933687618672397713 11257665700265714004298285)
              ·
                refine ⟨4221624637599642751611857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11257665700265714004298285 4221624637599642751611857)
                ·
                  refine ⟨3166218478199732063708893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221624637599642751611857 3166218478199732063708893)
                  ·
                    refine ⟨1187331929324899523890835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166218478199732063708893 1187331929324899523890835)
                    ·
                      rfl

theorem cell22_3468481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3468481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468481 prefixEnd_3468481 := by exact prefixLift 3468481
  have htrace : WordTrace (prefixWord ++ tailWord_3468481) baseStart_3468481 baseEnd_3468481 := by
    simpa [prefixWord, tailWord_3468481, baseEnd_3468481] using wordTrace_append hprefix tailTrace_3468481
  have hstable : (prefixWord ++ tailWord_3468481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468481).length < 2 ^ (prefixWord ++ tailWord_3468481).sum := by decide
  have hdescent : baseEnd_3468481 < baseStart_3468481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468494 : List Nat := [4, 1, 1, 1, 5, 1, 3, 6]
def baseStart_3468494 : Nat := 118140960795 + 3468494 * 2 ^ 59
def prefixEnd_3468494 : Nat := 4983230072969 + 3 ^ 40 * 3468494 * 2
def baseEnd_3468494 : Nat := 131926264387841313701755

theorem tailTrace_3468494 : CollatzResearch.WordTrace tailWord_3468494 prefixEnd_3468494 131926264387841313701755 := by
  unfold tailWord_3468494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813296137030760557399567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84337579397497389639464357 15813296137030760557399567)
  ·
    refine ⟨23719944205546140836099351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15813296137030760557399567 23719944205546140836099351)
    ·
      refine ⟨35579916308319211254149027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23719944205546140836099351 35579916308319211254149027)
      ·
        refine ⟨53369874462478816881223541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35579916308319211254149027 53369874462478816881223541)
        ·
          refine ⟨5003425730857389082614707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53369874462478816881223541 5003425730857389082614707)
          ·
            refine ⟨7505138596286083623922061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003425730857389082614707 7505138596286083623922061)
            ·
              refine ⟨2814426973607281358970773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7505138596286083623922061 2814426973607281358970773)
              ·
                refine ⟨131926264387841313701755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2814426973607281358970773 131926264387841313701755)
                ·
                  rfl

theorem cell22_3468494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_3468494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468494 prefixEnd_3468494 := by exact prefixLift 3468494
  have htrace : WordTrace (prefixWord ++ tailWord_3468494) baseStart_3468494 baseEnd_3468494 := by
    simpa [prefixWord, tailWord_3468494, baseEnd_3468494] using wordTrace_append hprefix tailTrace_3468494
  have hstable : (prefixWord ++ tailWord_3468494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468494).length < 2 ^ (prefixWord ++ tailWord_3468494).sum := by decide
  have hdescent : baseEnd_3468494 < baseStart_3468494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468505 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 7]
def baseStart_3468505 : Nat := 118140960795 + 3468505 * 2 ^ 59
def prefixEnd_3468505 : Nat := 4983230072969 + 3 ^ 40 * 3468505 * 2
def baseEnd_3468505 : Nat := 395780048338457153763587

theorem tailTrace_3468505 : CollatzResearch.WordTrace tailWord_3468505 prefixEnd_3468505 395780048338457153763587 := by
  unfold tailWord_3468505
  simp only [CollatzResearch.WordTrace]
  refine ⟨126506770299206233337846969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84337846866137488891897979 126506770299206233337846969)
  ·
    refine ⟨94880077724404675003385227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126506770299206233337846969 94880077724404675003385227)
    ·
      refine ⟨142320116586607012505077841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94880077724404675003385227 142320116586607012505077841)
      ·
        refine ⟨106740087439955259378808381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142320116586607012505077841 106740087439955259378808381)
        ·
          refine ⟨40027532789983222267053143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106740087439955259378808381 40027532789983222267053143)
          ·
            refine ⟨60041299184974833400579715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40027532789983222267053143 60041299184974833400579715)
            ·
              refine ⟨90061948777462250100869573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60041299184974833400579715 90061948777462250100869573)
              ·
                refine ⟨16886615395774171893913045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90061948777462250100869573 16886615395774171893913045)
                ·
                  refine ⟨395780048338457153763587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16886615395774171893913045 395780048338457153763587)
                  ·
                    rfl

theorem cell22_3468505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_3468505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468505 prefixEnd_3468505 := by exact prefixLift 3468505
  have htrace : WordTrace (prefixWord ++ tailWord_3468505) baseStart_3468505 baseEnd_3468505 := by
    simpa [prefixWord, tailWord_3468505, baseEnd_3468505] using wordTrace_append hprefix tailTrace_3468505
  have hstable : (prefixWord ++ tailWord_3468505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468505).length < 2 ^ (prefixWord ++ tailWord_3468505).sum := by decide
  have hdescent : baseEnd_3468505 < baseStart_3468505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468522 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_3468522 : Nat := 118140960795 + 3468522 * 2 ^ 59
def prefixEnd_3468522 : Nat := 4983230072969 + 3 ^ 40 * 3468522 * 2
def baseEnd_3468522 : Nat := 395781988154263027871903

theorem tailTrace_3468522 : CollatzResearch.WordTrace tailWord_3468522 prefixEnd_3468522 395781988154263027871903 := by
  unfold tailWord_3468522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626847585036161310303955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84338260226763096827477213 31626847585036161310303955)
  ·
    refine ⟨47440271377554241965455933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31626847585036161310303955 47440271377554241965455933)
    ·
      refine ⟨17790101766582840737045975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47440271377554241965455933 17790101766582840737045975)
      ·
        refine ⟨26685152649874261105568963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17790101766582840737045975 26685152649874261105568963)
        ·
          refine ⟨40027728974811391658353445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26685152649874261105568963 40027728974811391658353445)
          ·
            refine ⟨7505199182777135935941271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40027728974811391658353445 7505199182777135935941271)
            ·
              refine ⟨11257798774165703903911907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7505199182777135935941271 11257798774165703903911907)
              ·
                refine ⟨16886698161248555855867861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11257798774165703903911907 16886698161248555855867861)
                ·
                  refine ⟨395781988154263027871903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16886698161248555855867861 395781988154263027871903)
                  ·
                    rfl

theorem cell22_3468522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_3468522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468522 prefixEnd_3468522 := by exact prefixLift 3468522
  have htrace : WordTrace (prefixWord ++ tailWord_3468522) baseStart_3468522 baseEnd_3468522 := by
    simpa [prefixWord, tailWord_3468522, baseEnd_3468522] using wordTrace_append hprefix tailTrace_3468522
  have hstable : (prefixWord ++ tailWord_3468522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468522).length < 2 ^ (prefixWord ++ tailWord_3468522).sum := by decide
  have hdescent : baseEnd_3468522 < baseStart_3468522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468526 : List Nat := [4, 1, 2, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3468526 : Nat := 118140960795 + 3468526 * 2 ^ 59
def prefixEnd_3468526 : Nat := 4983230072969 + 3 ^ 40 * 3468526 * 2
def baseEnd_3468526 : Nat := 1187347333744534406515697

theorem tailTrace_3468526 : CollatzResearch.WordTrace tailWord_3468526 prefixEnd_3468526 1187347333744534406515697 := by
  unfold tailWord_3468526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813442029016269240545179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84338357488086769282907621 15813442029016269240545179)
  ·
    refine ⟨23720163043524403860817769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15813442029016269240545179 23720163043524403860817769)
    ·
      refine ⟨17790122282643302895613327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23720163043524403860817769 17790122282643302895613327)
      ·
        refine ⟨26685183423964954343419991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17790122282643302895613327 26685183423964954343419991)
        ·
          refine ⟨40027775135947431515129987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26685183423964954343419991 40027775135947431515129987)
          ·
            refine ⟨60041662703921147272694981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40027775135947431515129987 60041662703921147272694981)
            ·
              refine ⟨11257811756985215113630309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60041662703921147272694981 11257811756985215113630309)
              ·
                refine ⟨2110839704434727833805683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11257811756985215113630309 2110839704434727833805683)
                ·
                  refine ⟨3166259556652091750708525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2110839704434727833805683 3166259556652091750708525)
                  ·
                    refine ⟨1187347333744534406515697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166259556652091750708525 1187347333744534406515697)
                    ·
                      rfl

theorem cell22_3468526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3468526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468526 prefixEnd_3468526 := by exact prefixLift 3468526
  have htrace : WordTrace (prefixWord ++ tailWord_3468526) baseStart_3468526 baseEnd_3468526 := by
    simpa [prefixWord, tailWord_3468526, baseEnd_3468526] using wordTrace_append hprefix tailTrace_3468526
  have hstable : (prefixWord ++ tailWord_3468526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468526).length < 2 ^ (prefixWord ++ tailWord_3468526).sum := by decide
  have hdescent : baseEnd_3468526 < baseStart_3468526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468532 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3468532 : Nat := 118140960795 + 3468532 * 2 ^ 59
def prefixEnd_3468532 : Nat := 4983230072969 + 3 ^ 40 * 3468532 * 2
def baseEnd_3468532 : Nat := 1187349387667152390865679

theorem tailTrace_3468532 : CollatzResearch.WordTrace tailWord_3468532 prefixEnd_3468532 1187349387667152390865679 := by
  unfold tailWord_3468532
  simp only [CollatzResearch.WordTrace]
  refine ⟨63253877535054208474539925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84338503380072277966053233 63253877535054208474539925)
  ·
    refine ⟨2965025509455666022244059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 63253877535054208474539925 2965025509455666022244059)
    ·
      refine ⟨4447538264183499033366089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2965025509455666022244059 4447538264183499033366089)
      ·
        refine ⟨3335653698137624275024567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4447538264183499033366089 3335653698137624275024567)
        ·
          refine ⟨5003480547206436412536851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335653698137624275024567 5003480547206436412536851)
          ·
            refine ⟨7505220820809654618805277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003480547206436412536851 7505220820809654618805277)
            ·
              refine ⟨2814457807803620482051979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7505220820809654618805277 2814457807803620482051979)
              ·
                refine ⟨4221686711705430723077969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2814457807803620482051979 4221686711705430723077969)
                ·
                  refine ⟨3166265033779073042308477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4221686711705430723077969 3166265033779073042308477)
                  ·
                    refine ⟨1187349387667152390865679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166265033779073042308477 1187349387667152390865679)
                    ·
                      rfl

theorem cell22_3468532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3468532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468532 prefixEnd_3468532 := by exact prefixLift 3468532
  have htrace : WordTrace (prefixWord ++ tailWord_3468532) baseStart_3468532 baseEnd_3468532 := by
    simpa [prefixWord, tailWord_3468532, baseEnd_3468532] using wordTrace_append hprefix tailTrace_3468532
  have hstable : (prefixWord ++ tailWord_3468532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468532).length < 2 ^ (prefixWord ++ tailWord_3468532).sum := by decide
  have hdescent : baseEnd_3468532 < baseStart_3468532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468584 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 6]
def baseStart_3468584 : Nat := 118140960795 + 3468584 * 2 ^ 59
def prefixEnd_3468584 : Nat := 4983230072969 + 3 ^ 40 * 3468584 * 2
def baseEnd_3468584 : Nat := 395789062776613862855173

theorem tailTrace_3468584 : CollatzResearch.WordTrace tailWord_3468584 prefixEnd_3468584 395789062776613862855173 := by
  unfold tailWord_3468584
  simp only [CollatzResearch.WordTrace]
  refine ⟨63254825832960014914986403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84339767777280019886648537 63254825832960014914986403)
  ·
    refine ⟨94882238749440022372479605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63254825832960014914986403 94882238749440022372479605)
    ·
      refine ⟨8895209882760002097419963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94882238749440022372479605 8895209882760002097419963)
      ·
        refine ⟨13342814824140003146129945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8895209882760002097419963 13342814824140003146129945)
        ·
          refine ⟨10007111118105002359597459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13342814824140003146129945 10007111118105002359597459)
          ·
            refine ⟨15010666677157503539396189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10007111118105002359597459 15010666677157503539396189)
            ·
              refine ⟨5629000003934063827273571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15010666677157503539396189 5629000003934063827273571)
              ·
                refine ⟨8443500005901095740910357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629000003934063827273571 8443500005901095740910357)
                ·
                  refine ⟨395789062776613862855173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8443500005901095740910357 395789062776613862855173)
                  ·
                    rfl

theorem cell22_3468584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_3468584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468584 prefixEnd_3468584 := by exact prefixLift 3468584
  have htrace : WordTrace (prefixWord ++ tailWord_3468584) baseStart_3468584 baseEnd_3468584 := by
    simpa [prefixWord, tailWord_3468584, baseEnd_3468584] using wordTrace_append hprefix tailTrace_3468584
  have hstable : (prefixWord ++ tailWord_3468584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468584).length < 2 ^ (prefixWord ++ tailWord_3468584).sum := by decide
  have hdescent : baseEnd_3468584 < baseStart_3468584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468721 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_3468721 : Nat := 118140960795 + 3468721 * 2 ^ 59
def prefixEnd_3468721 : Nat := 4983230072969 + 3 ^ 40 * 3468721 * 2
def baseEnd_3468721 : Nat := 1187414086229618897890099

theorem tailTrace_3468721 : CollatzResearch.WordTrace tailWord_3468721 prefixEnd_3468721 1187414086229618897890099 := by
  unfold tailWord_3468721
  simp only [CollatzResearch.WordTrace]
  refine ⟨126514648466423702227710017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84343098977615801485140011 126514648466423702227710017)
  ·
    refine ⟨94885986349817776670782513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126514648466423702227710017 94885986349817776670782513)
    ·
      refine ⟨71164489762363332503086885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94885986349817776670782513 71164489762363332503086885)
      ·
        refine ⟨13343341830443124844328791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71164489762363332503086885 13343341830443124844328791)
        ·
          refine ⟨20015012745664687266493187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13343341830443124844328791 20015012745664687266493187)
          ·
            refine ⟨30022519118497030899739781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20015012745664687266493187 30022519118497030899739781)
            ·
              refine ⟨5629222334718193293701209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30022519118497030899739781 5629222334718193293701209)
              ·
                refine ⟨4221916751038644970275907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5629222334718193293701209 4221916751038644970275907)
                ·
                  refine ⟨6332875126557967455413861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4221916751038644970275907 6332875126557967455413861)
                  ·
                    refine ⟨1187414086229618897890099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6332875126557967455413861 1187414086229618897890099)
                    ·
                      rfl

theorem cell22_3468721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_3468721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468721 prefixEnd_3468721 := by exact prefixLift 3468721
  have htrace : WordTrace (prefixWord ++ tailWord_3468721) baseStart_3468721 baseEnd_3468721 := by
    simpa [prefixWord, tailWord_3468721, baseEnd_3468721] using wordTrace_append hprefix tailTrace_3468721
  have hstable : (prefixWord ++ tailWord_3468721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468721).length < 2 ^ (prefixWord ++ tailWord_3468721).sum := by decide
  have hdescent : baseEnd_3468721 < baseStart_3468721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468734 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3468734 : Nat := 118140960795 + 3468734 * 2 ^ 59
def prefixEnd_3468734 : Nat := 4983230072969 + 3 ^ 40 * 3468734 * 2
def baseEnd_3468734 : Nat := 1187418536395291197315059

theorem tailTrace_3468734 : CollatzResearch.WordTrace tailWord_3468734 prefixEnd_3468734 1187418536395291197315059 := by
  unfold tailWord_3468734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814390326922075680991657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84343415076917736965288837 15814390326922075680991657)
  ·
    refine ⟨11860792745191556760743743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15814390326922075680991657 11860792745191556760743743)
    ·
      refine ⟨17791189117787335141115615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11860792745191556760743743 17791189117787335141115615)
      ·
        refine ⟨26686783676681002711673423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17791189117787335141115615 26686783676681002711673423)
        ·
          refine ⟨40030175515021504067510135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26686783676681002711673423 40030175515021504067510135)
          ·
            refine ⟨60045263272532256101265203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40030175515021504067510135 60045263272532256101265203)
            ·
              refine ⟨90067894908798384151897805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60045263272532256101265203 90067894908798384151897805)
              ·
                refine ⟨33775460590799394056961677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90067894908798384151897805 33775460590799394056961677)
                ·
                  refine ⟨12665797721549772771360629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33775460590799394056961677 12665797721549772771360629)
                  ·
                    refine ⟨1187418536395291197315059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12665797721549772771360629 1187418536395291197315059)
                    ·
                      rfl

theorem cell22_3468734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3468734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468734 prefixEnd_3468734 := by exact prefixLift 3468734
  have htrace : WordTrace (prefixWord ++ tailWord_3468734) baseStart_3468734 baseEnd_3468734 := by
    simpa [prefixWord, tailWord_3468734, baseEnd_3468734] using wordTrace_append hprefix tailTrace_3468734
  have hstable : (prefixWord ++ tailWord_3468734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468734).length < 2 ^ (prefixWord ++ tailWord_3468734).sum := by decide
  have hdescent : baseEnd_3468734 < baseStart_3468734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468736 : List Nat := [2, 1, 1, 2, 3, 1, 5, 3, 4]
def baseStart_3468736 : Nat := 118140960795 + 3468736 * 2 ^ 59
def prefixEnd_3468736 : Nat := 4983230072969 + 3 ^ 40 * 3468736 * 2
def baseEnd_3468736 : Nat := 395806407012054619588351

theorem tailTrace_3468736 : CollatzResearch.WordTrace tailWord_3468736 prefixEnd_3468736 395806407012054619588351 := by
  unfold tailWord_3468736
  simp only [CollatzResearch.WordTrace]
  refine ⟨63257597780684679894753031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84343463707579573193004041 63257597780684679894753031)
  ·
    refine ⟨94886396671027019842129547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63257597780684679894753031 94886396671027019842129547)
    ·
      refine ⟨142329595006540529763194321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94886396671027019842129547 142329595006540529763194321)
      ·
        refine ⟨106747196254905397322395741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142329595006540529763194321 106747196254905397322395741)
        ·
          refine ⟨40030198595589523995898403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106747196254905397322395741 40030198595589523995898403)
          ·
            refine ⟨60045297893384285993847605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40030198595589523995898403 60045297893384285993847605)
            ·
              refine ⟨5629246677504776811923213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60045297893384285993847605 5629246677504776811923213)
              ·
                refine ⟨2110967504064291304471205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5629246677504776811923213 2110967504064291304471205)
                ·
                  refine ⟨395806407012054619588351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110967504064291304471205 395806407012054619588351)
                  ·
                    rfl

theorem cell22_3468736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 3, 4].length) (baseStart_3468736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468736 prefixEnd_3468736 := by exact prefixLift 3468736
  have htrace : WordTrace (prefixWord ++ tailWord_3468736) baseStart_3468736 baseEnd_3468736 := by
    simpa [prefixWord, tailWord_3468736, baseEnd_3468736] using wordTrace_append hprefix tailTrace_3468736
  have hstable : (prefixWord ++ tailWord_3468736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468736).length < 2 ^ (prefixWord ++ tailWord_3468736).sum := by decide
  have hdescent : baseEnd_3468736 < baseStart_3468736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468747 : List Nat := [1, 1, 1, 1, 3, 3, 12]
def baseStart_3468747 : Nat := 118140960795 + 3468747 * 2 ^ 59
def prefixEnd_3468747 : Nat := 4983230072969 + 3 ^ 40 * 3468747 * 2
def baseEnd_3468747 : Nat := 43978629131887536916297

theorem tailTrace_3468747 : CollatzResearch.WordTrace tailWord_3468747 prefixEnd_3468747 43978629131887536916297 := by
  unfold tailWord_3468747
  simp only [CollatzResearch.WordTrace]
  refine ⟨126515596764329508668156495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84343731176219672445437663 126515596764329508668156495)
  ·
    refine ⟨189773395146494263002234743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126515596764329508668156495 189773395146494263002234743)
    ·
      refine ⟨284660092719741394503352115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189773395146494263002234743 284660092719741394503352115)
      ·
        refine ⟨426990139079612091755028173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284660092719741394503352115 426990139079612091755028173)
        ·
          refine ⟨160121302154854534408135565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426990139079612091755028173 160121302154854534408135565)
          ·
            refine ⟨60045488308070450403050837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160121302154854534408135565 60045488308070450403050837)
            ·
              refine ⟨43978629131887536916297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 60045488308070450403050837 43978629131887536916297)
              ·
                rfl

theorem cell22_3468747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 12].length) (baseStart_3468747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468747 prefixEnd_3468747 := by exact prefixLift 3468747
  have htrace : WordTrace (prefixWord ++ tailWord_3468747) baseStart_3468747 baseEnd_3468747 := by
    simpa [prefixWord, tailWord_3468747, baseEnd_3468747] using wordTrace_append hprefix tailTrace_3468747
  have hstable : (prefixWord ++ tailWord_3468747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468747).length < 2 ^ (prefixWord ++ tailWord_3468747).sum := by decide
  have hdescent : baseEnd_3468747 < baseStart_3468747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468798 : List Nat := [4, 2, 2, 3, 2, 9]
def baseStart_3468798 : Nat := 118140960795 + 3468798 * 2 ^ 59
def prefixEnd_3468798 : Nat := 4983230072969 + 3 ^ 40 * 3468798 * 2
def baseEnd_3468798 : Nat := 14659758579052053873023

theorem tailTrace_3468798 : CollatzResearch.WordTrace tailWord_3468798 prefixEnd_3468798 14659758579052053873023 := by
  unfold tailWord_3468798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814682110893093047282881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84344971258096496252175365 15814682110893093047282881)
  ·
    refine ⟨11861011583169819785462161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15814682110893093047282881 11861011583169819785462161)
    ·
      refine ⟨8895758687377364839096621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11861011583169819785462161 8895758687377364839096621)
      ·
        refine ⟨3335909507766511814661233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8895758687377364839096621 3335909507766511814661233)
        ·
          refine ⟨2501932130824883860995925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3335909507766511814661233 2501932130824883860995925)
          ·
            refine ⟨14659758579052053873023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2501932130824883860995925 14659758579052053873023)
            ·
              rfl

theorem cell22_3468798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 9].length) (baseStart_3468798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468798 prefixEnd_3468798 := by exact prefixLift 3468798
  have htrace : WordTrace (prefixWord ++ tailWord_3468798) baseStart_3468798 baseEnd_3468798 := by
    simpa [prefixWord, tailWord_3468798, baseEnd_3468798] using wordTrace_append hprefix tailTrace_3468798
  have hstable : (prefixWord ++ tailWord_3468798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468798).length < 2 ^ (prefixWord ++ tailWord_3468798).sum := by decide
  have hdescent : baseEnd_3468798 < baseStart_3468798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468860 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 5]
def baseStart_3468860 : Nat := 118140960795 + 3468860 * 2 ^ 59
def prefixEnd_3468860 : Nat := 4983230072969 + 3 ^ 40 * 3468860 * 2
def baseEnd_3468860 : Nat := 395820556256756289554891

theorem tailTrace_3468860 : CollatzResearch.WordTrace tailWord_3468860 prefixEnd_3468860 395820556256756289554891 := by
  unfold tailWord_3468860
  simp only [CollatzResearch.WordTrace]
  refine ⟨63259859106460064483510017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84346478808613419311346689 63259859106460064483510017)
  ·
    refine ⟨47444894329845048362632513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63259859106460064483510017 47444894329845048362632513)
    ·
      refine ⟨35583670747383786271974385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47444894329845048362632513 35583670747383786271974385)
      ·
        refine ⟨26687753060537839703980789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35583670747383786271974385 26687753060537839703980789)
        ·
          refine ⟨2501976849425422472248199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26687753060537839703980789 2501976849425422472248199)
          ·
            refine ⟨3752965274138133708372299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501976849425422472248199 3752965274138133708372299)
            ·
              refine ⟨5629447911207200562558449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752965274138133708372299 5629447911207200562558449)
              ·
                refine ⟨4222085933405400421918837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5629447911207200562558449 4222085933405400421918837)
                ·
                  refine ⟨395820556256756289554891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4222085933405400421918837 395820556256756289554891)
                  ·
                    rfl

theorem cell22_3468860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_3468860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468860 prefixEnd_3468860 := by exact prefixLift 3468860
  have htrace : WordTrace (prefixWord ++ tailWord_3468860) baseStart_3468860 baseEnd_3468860 := by
    simpa [prefixWord, tailWord_3468860, baseEnd_3468860] using wordTrace_append hprefix tailTrace_3468860
  have hstable : (prefixWord ++ tailWord_3468860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468860).length < 2 ^ (prefixWord ++ tailWord_3468860).sum := by decide
  have hdescent : baseEnd_3468860 < baseStart_3468860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468901 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3468901 : Nat := 118140960795 + 3468901 * 2 ^ 59
def prefixEnd_3468901 : Nat := 4983230072969 + 3 ^ 40 * 3468901 * 2
def baseEnd_3468901 : Nat := 1187475703908158428389547

theorem tailTrace_3468901 : CollatzResearch.WordTrace tailWord_3468901 prefixEnd_3468901 1187475703908158428389547 := by
  unfold tailWord_3468901
  simp only [CollatzResearch.WordTrace]
  refine ⟨126521213605771592969262557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84347475737181061979508371 126521213605771592969262557)
  ·
    refine ⟨47445455102164347363473459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126521213605771592969262557 47445455102164347363473459)
    ·
      refine ⟨71168182653246521045210189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47445455102164347363473459 71168182653246521045210189)
      ·
        refine ⟨26688068494967445391953821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71168182653246521045210189 26688068494967445391953821)
        ·
          refine ⟨10008025685612792021982683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26688068494967445391953821 10008025685612792021982683)
          ·
            refine ⟨15012038528419188032974025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10008025685612792021982683 15012038528419188032974025)
            ·
              refine ⟨11259028896314391024730519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15012038528419188032974025 11259028896314391024730519)
              ·
                refine ⟨16888543344471586537095779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11259028896314391024730519 16888543344471586537095779)
                ·
                  refine ⟨25332815016707379805643669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16888543344471586537095779 25332815016707379805643669)
                  ·
                    refine ⟨1187475703908158428389547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25332815016707379805643669 1187475703908158428389547)
                    ·
                      rfl

theorem cell22_3468901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3468901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468901 prefixEnd_3468901 := by exact prefixLift 3468901
  have htrace : WordTrace (prefixWord ++ tailWord_3468901) baseStart_3468901 baseEnd_3468901 := by
    simpa [prefixWord, tailWord_3468901, baseEnd_3468901] using wordTrace_append hprefix tailTrace_3468901
  have hstable : (prefixWord ++ tailWord_3468901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468901).length < 2 ^ (prefixWord ++ tailWord_3468901).sum := by decide
  have hdescent : baseEnd_3468901 < baseStart_3468901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468918 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3468918 : Nat := 118140960795 + 3468918 * 2 ^ 59
def prefixEnd_3468918 : Nat := 4983230072969 + 3 ^ 40 * 3468918 * 2
def baseEnd_3468918 : Nat := 1187481523355576050714495

theorem tailTrace_3468918 : CollatzResearch.WordTrace tailWord_3468918 prefixEnd_3468918 1187481523355576050714495 := by
  unfold tailWord_3468918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907614602919375304539463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84347889097806669915087605 7907614602919375304539463)
  ·
    refine ⟨11861421904379062956809195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7907614602919375304539463 11861421904379062956809195)
    ·
      refine ⟨17792132856568594435213793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11861421904379062956809195 17792132856568594435213793)
      ·
        refine ⟨13344099642426445826410345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17792132856568594435213793 13344099642426445826410345)
        ·
          refine ⟨10008074731819834369807759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13344099642426445826410345 10008074731819834369807759)
          ·
            refine ⟨15012112097729751554711639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10008074731819834369807759 15012112097729751554711639)
            ·
              refine ⟨22518168146594627332067459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15012112097729751554711639 22518168146594627332067459)
              ·
                refine ⟨33777252219891940998101189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22518168146594627332067459 33777252219891940998101189)
                ·
                  refine ⟨6333234791229738937143973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33777252219891940998101189 6333234791229738937143973)
                  ·
                    refine ⟨1187481523355576050714495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6333234791229738937143973 1187481523355576050714495)
                    ·
                      rfl

theorem cell22_3468918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3468918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468918 prefixEnd_3468918 := by exact prefixLift 3468918
  have htrace : WordTrace (prefixWord ++ tailWord_3468918) baseStart_3468918 baseEnd_3468918 := by
    simpa [prefixWord, tailWord_3468918, baseEnd_3468918] using wordTrace_append hprefix tailTrace_3468918
  have hstable : (prefixWord ++ tailWord_3468918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468918).length < 2 ^ (prefixWord ++ tailWord_3468918).sum := by decide
  have hdescent : baseEnd_3468918 < baseStart_3468918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3468991 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 5, 4]
def baseStart_3468991 : Nat := 118140960795 + 3468991 * 2 ^ 59
def prefixEnd_3468991 : Nat := 4983230072969 + 3 ^ 40 * 3468991 * 2
def baseEnd_3468991 : Nat := 1187506512747428193639271

theorem tailTrace_3468991 : CollatzResearch.WordTrace tailWord_3468991 prefixEnd_3468991 1187506512747428193639271 := by
  unfold tailWord_3468991
  simp only [CollatzResearch.WordTrace]
  refine ⟨126524496175445538340038827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84349664116963692226692551 126524496175445538340038827)
  ·
    refine ⟨189786744263168307510058241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126524496175445538340038827 189786744263168307510058241)
    ·
      refine ⟨142340058197376230632543681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189786744263168307510058241 142340058197376230632543681)
      ·
        refine ⟨106755043648032172974407761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142340058197376230632543681 106755043648032172974407761)
        ·
          refine ⟨80066282736024129730805821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106755043648032172974407761 80066282736024129730805821)
          ·
            refine ⟨30024856026009048649052183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80066282736024129730805821 30024856026009048649052183)
            ·
              refine ⟨45037284039013572973578275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30024856026009048649052183 45037284039013572973578275)
              ·
                refine ⟨67555926058520359460367413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45037284039013572973578275 67555926058520359460367413)
                ·
                  refine ⟨6333368067986283699409445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67555926058520359460367413 6333368067986283699409445)
                  ·
                    refine ⟨1187506512747428193639271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6333368067986283699409445 1187506512747428193639271)
                    ·
                      rfl

theorem cell22_3468991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_3468991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3468991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3468991 prefixEnd_3468991 := by exact prefixLift 3468991
  have htrace : WordTrace (prefixWord ++ tailWord_3468991) baseStart_3468991 baseEnd_3468991 := by
    simpa [prefixWord, tailWord_3468991, baseEnd_3468991] using wordTrace_append hprefix tailTrace_3468991
  have hstable : (prefixWord ++ tailWord_3468991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3468991).length < 2 ^ (prefixWord ++ tailWord_3468991).sum := by decide
  have hdescent : baseEnd_3468991 < baseStart_3468991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3468991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469025 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3469025 : Nat := 118140960795 + 3469025 * 2 ^ 59
def prefixEnd_3469025 : Nat := 4983230072969 + 3 ^ 40 * 3469025 * 2
def baseEnd_3469025 : Nat := 1187518151642263438289167

theorem tailTrace_3469025 : CollatzResearch.WordTrace tailWord_3469025 prefixEnd_3469025 1187518151642263438289167 := by
  unfold tailWord_3469025
  simp only [CollatzResearch.WordTrace]
  refine ⟨126525736257322362146776529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84350490838214908097851019 126525736257322362146776529)
  ·
    refine ⟨94894302192991771610082397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126525736257322362146776529 94894302192991771610082397)
    ·
      refine ⟨35585363322371914353780899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94894302192991771610082397 35585363322371914353780899)
      ·
        refine ⟨53378044983557871530671349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35585363322371914353780899 53378044983557871530671349)
        ·
          refine ⟨5004191717208550456000439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53378044983557871530671349 5004191717208550456000439)
          ·
            refine ⟨7506287575812825684000659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004191717208550456000439 7506287575812825684000659)
            ·
              refine ⟨11259431363719238526000989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7506287575812825684000659 11259431363719238526000989)
              ·
                refine ⟨4222286761394714447250371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11259431363719238526000989 4222286761394714447250371)
                ·
                  refine ⟨6333430142092071670875557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222286761394714447250371 6333430142092071670875557)
                  ·
                    refine ⟨1187518151642263438289167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6333430142092071670875557 1187518151642263438289167)
                    ·
                      rfl

theorem cell22_3469025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3469025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469025 prefixEnd_3469025 := by exact prefixLift 3469025
  have htrace : WordTrace (prefixWord ++ tailWord_3469025) baseStart_3469025 baseEnd_3469025 := by
    simpa [prefixWord, tailWord_3469025, baseEnd_3469025] using wordTrace_append hprefix tailTrace_3469025
  have hstable : (prefixWord ++ tailWord_3469025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469025).length < 2 ^ (prefixWord ++ tailWord_3469025).sum := by decide
  have hdescent : baseEnd_3469025 < baseStart_3469025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469068 : List Nat := [2, 2, 1, 2, 2, 1, 6, 6]
def baseStart_3469068 : Nat := 118140960795 + 3469068 * 2 ^ 59
def prefixEnd_3469068 : Nat := 4983230072969 + 3 ^ 40 * 3469068 * 2
def baseEnd_3469068 : Nat := 131948096824558406607115

theorem tailTrace_3469068 : CollatzResearch.WordTrace tailWord_3469068 prefixEnd_3469068 131948096824558406607115 := by
  unfold tailWord_3469068
  simp only [CollatzResearch.WordTrace]
  refine ⟨63263652298083290245295929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84351536397444386993727905 63263652298083290245295929)
  ·
    refine ⟨47447739223562467683971947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63263652298083290245295929 47447739223562467683971947)
    ·
      refine ⟨71171608835343701525957921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47447739223562467683971947 71171608835343701525957921)
      ·
        refine ⟨53378706626507776144468441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71171608835343701525957921 53378706626507776144468441)
        ·
          refine ⟨40034029969880832108351331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53378706626507776144468441 40034029969880832108351331)
          ·
            refine ⟨60051044954821248162526997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40034029969880832108351331 60051044954821248162526997)
            ·
              refine ⟨2814892732257246007618453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60051044954821248162526997 2814892732257246007618453)
              ·
                refine ⟨131948096824558406607115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2814892732257246007618453 131948096824558406607115)
                ·
                  rfl

theorem cell22_3469068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 6].length) (baseStart_3469068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469068 prefixEnd_3469068 := by exact prefixLift 3469068
  have htrace : WordTrace (prefixWord ++ tailWord_3469068) baseStart_3469068 baseEnd_3469068 := by
    simpa [prefixWord, tailWord_3469068, baseEnd_3469068] using wordTrace_append hprefix tailTrace_3469068
  have hstable : (prefixWord ++ tailWord_3469068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469068).length < 2 ^ (prefixWord ++ tailWord_3469068).sum := by decide
  have hdescent : baseEnd_3469068 < baseStart_3469068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469074 : List Nat := [3, 2, 4, 1, 1, 3, 1, 3, 4]
def baseStart_3469074 : Nat := 118140960795 + 3469074 * 2 ^ 59
def prefixEnd_3469074 : Nat := 4983230072969 + 3 ^ 40 * 3469074 * 2
def baseEnd_3469074 : Nat := 395844975114547881271339

theorem tailTrace_3469074 : CollatzResearch.WordTrace tailWord_3469074 prefixEnd_3469074 395844975114547881271339 := by
  unfold tailWord_3469074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31631880858536210878827569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84351682289429895676873517 31631880858536210878827569)
  ·
    refine ⟨23723910643902158159120677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31631880858536210878827569 23723910643902158159120677)
    ·
      refine ⟨4448233245731654654835127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23723910643902158159120677 4448233245731654654835127)
      ·
        refine ⟨6672349868597481982252691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448233245731654654835127 6672349868597481982252691)
        ·
          refine ⟨10008524802896222973379037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6672349868597481982252691 10008524802896222973379037)
          ·
            refine ⟨3753196801086083615017139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10008524802896222973379037 3753196801086083615017139)
            ·
              refine ⟨5629795201629125422525709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753196801086083615017139 5629795201629125422525709)
              ·
                refine ⟨2111173200610922033447141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5629795201629125422525709 2111173200610922033447141)
                ·
                  refine ⟨395844975114547881271339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111173200610922033447141 395844975114547881271339)
                  ·
                    rfl

theorem cell22_3469074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_3469074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469074 prefixEnd_3469074 := by exact prefixLift 3469074
  have htrace : WordTrace (prefixWord ++ tailWord_3469074) baseStart_3469074 baseEnd_3469074 := by
    simpa [prefixWord, tailWord_3469074, baseEnd_3469074] using wordTrace_append hprefix tailTrace_3469074
  have hstable : (prefixWord ++ tailWord_3469074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469074).length < 2 ^ (prefixWord ++ tailWord_3469074).sum := by decide
  have hdescent : baseEnd_3469074 < baseStart_3469074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469100 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 3, 3]
def baseStart_3469100 : Nat := 118140960795 + 3469100 * 2 ^ 59
def prefixEnd_3469100 : Nat := 4983230072969 + 3 ^ 40 * 3469100 * 2
def baseEnd_3469100 : Nat := 1187543825674988242663937

theorem tailTrace_3469100 : CollatzResearch.WordTrace tailWord_3469100 prefixEnd_3469100 1187543825674988242663937 := by
  unfold tailWord_3469100
  simp only [CollatzResearch.WordTrace]
  refine ⟨63264235866025324977878377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84352314488033766637171169 63264235866025324977878377)
  ·
    refine ⟨47448176899518993733408783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63264235866025324977878377 47448176899518993733408783)
    ·
      refine ⟨71172265349278490600113175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47448176899518993733408783 71172265349278490600113175)
      ·
        refine ⟨106758398023917735900169763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71172265349278490600113175 106758398023917735900169763)
        ·
          refine ⟨160137597035876603850254645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106758398023917735900169763 160137597035876603850254645)
          ·
            refine ⟨15012899722113431610961373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160137597035876603850254645 15012899722113431610961373)
            ·
              refine ⟨5629837395792536854110515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15012899722113431610961373 5629837395792536854110515)
              ·
                refine ⟨8444756093688805281165773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629837395792536854110515 8444756093688805281165773)
                ·
                  refine ⟨3166783535133301980437165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8444756093688805281165773 3166783535133301980437165)
                  ·
                    refine ⟨1187543825674988242663937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166783535133301980437165 1187543825674988242663937)
                    ·
                      rfl

theorem cell22_3469100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_3469100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469100 prefixEnd_3469100 := by exact prefixLift 3469100
  have htrace : WordTrace (prefixWord ++ tailWord_3469100) baseStart_3469100 baseEnd_3469100 := by
    simpa [prefixWord, tailWord_3469100, baseEnd_3469100] using wordTrace_append hprefix tailTrace_3469100
  have hstable : (prefixWord ++ tailWord_3469100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469100).length < 2 ^ (prefixWord ++ tailWord_3469100).sum := by decide
  have hdescent : baseEnd_3469100 < baseStart_3469100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469162 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_3469162 : Nat := 118140960795 + 3469162 * 2 ^ 59
def prefixEnd_3469162 : Nat := 4983230072969 + 3 ^ 40 * 3469162 * 2
def baseEnd_3469162 : Nat := 1187565049542040747613747

theorem tailTrace_3469162 : CollatzResearch.WordTrace tailWord_3469162 prefixEnd_3469162 1187565049542040747613747 := by
  unfold tailWord_3469162
  simp only [CollatzResearch.WordTrace]
  refine ⟨31632683264456508636128435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84353822038550689696342493 31632683264456508636128435)
  ·
    refine ⟨47449024896684762954192653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31632683264456508636128435 47449024896684762954192653)
    ·
      refine ⟨17793384336256786107822245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47449024896684762954192653 17793384336256786107822245)
      ·
        refine ⟨3336259563048147395216671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17793384336256786107822245 3336259563048147395216671)
        ·
          refine ⟨5004389344572221092825007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336259563048147395216671 5004389344572221092825007)
          ·
            refine ⟨7506584016858331639237511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004389344572221092825007 7506584016858331639237511)
            ·
              refine ⟨11259876025287497458856267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7506584016858331639237511 11259876025287497458856267)
              ·
                refine ⟨16889814037931246188284401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11259876025287497458856267 16889814037931246188284401)
                ·
                  refine ⟨12667360528448434641213301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16889814037931246188284401 12667360528448434641213301)
                  ·
                    refine ⟨1187565049542040747613747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12667360528448434641213301 1187565049542040747613747)
                    ·
                      rfl

theorem cell22_3469162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_3469162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469162 prefixEnd_3469162 := by exact prefixLift 3469162
  have htrace : WordTrace (prefixWord ++ tailWord_3469162) baseStart_3469162 baseEnd_3469162 := by
    simpa [prefixWord, tailWord_3469162, baseEnd_3469162] using wordTrace_append hprefix tailTrace_3469162
  have hstable : (prefixWord ++ tailWord_3469162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469162).length < 2 ^ (prefixWord ++ tailWord_3469162).sum := by decide
  have hdescent : baseEnd_3469162 < baseStart_3469162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469207 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 2, 3]
def baseStart_3469207 : Nat := 118140960795 + 3469207 * 2 ^ 59
def prefixEnd_3469207 : Nat := 4983230072969 + 3 ^ 40 * 3469207 * 2
def baseEnd_3469207 : Nat := 1187580453961675630238609

theorem tailTrace_3469207 : CollatzResearch.WordTrace tailWord_3469207 prefixEnd_3469207 1187580453961675630238609 := by
  unfold tailWord_3469207
  simp only [CollatzResearch.WordTrace]
  refine ⟨126532374342663007229901875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84354916228442004819934583 126532374342663007229901875)
  ·
    refine ⟨189798561513994510844852813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126532374342663007229901875 189798561513994510844852813)
    ·
      refine ⟨71174460567747941566819805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189798561513994510844852813 71174460567747941566819805)
      ·
        refine ⟨26690422712905478087557427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71174460567747941566819805 26690422712905478087557427)
        ·
          refine ⟨40035634069358217131336141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26690422712905478087557427 40035634069358217131336141)
          ·
            refine ⟨15013362776009331424251053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40035634069358217131336141 15013362776009331424251053)
            ·
              refine ⟨5630011041003499284094145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15013362776009331424251053 5630011041003499284094145)
              ·
                refine ⟨4222508280752624463070609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5630011041003499284094145 4222508280752624463070609)
                ·
                  refine ⟨3166881210564468347302957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4222508280752624463070609 3166881210564468347302957)
                  ·
                    refine ⟨1187580453961675630238609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166881210564468347302957 1187580453961675630238609)
                    ·
                      rfl

theorem cell22_3469207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_3469207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469207 prefixEnd_3469207 := by exact prefixLift 3469207
  have htrace : WordTrace (prefixWord ++ tailWord_3469207) baseStart_3469207 baseEnd_3469207 := by
    simpa [prefixWord, tailWord_3469207, baseEnd_3469207] using wordTrace_append hprefix tailTrace_3469207
  have hstable : (prefixWord ++ tailWord_3469207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469207).length < 2 ^ (prefixWord ++ tailWord_3469207).sum := by decide
  have hdescent : baseEnd_3469207 < baseStart_3469207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469235 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 3, 3]
def baseStart_3469235 : Nat := 118140960795 + 3469235 * 2 ^ 59
def prefixEnd_3469235 : Nat := 4983230072969 + 3 ^ 40 * 3469235 * 2
def baseEnd_3469235 : Nat := 1187590038933892890538523

theorem tailTrace_3469235 : CollatzResearch.WordTrace tailWord_3469235 prefixEnd_3469235 1187590038933892890538523 := by
  unfold tailWord_3469235
  simp only [CollatzResearch.WordTrace]
  refine ⟨126533395586561568011921159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84355597057707712007947439 126533395586561568011921159)
  ·
    refine ⟨189800093379842352017881739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126533395586561568011921159 189800093379842352017881739)
    ·
      refine ⟨284700140069763528026822609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189800093379842352017881739 284700140069763528026822609)
      ·
        refine ⟨213525105052322646020116957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284700140069763528026822609 213525105052322646020116957)
        ·
          refine ⟨80071914394620992257543859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213525105052322646020116957 80071914394620992257543859)
          ·
            refine ⟨120107871591931488386315789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80071914394620992257543859 120107871591931488386315789)
            ·
              refine ⟨45040451846974308144868421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120107871591931488386315789 45040451846974308144868421)
              ·
                refine ⟨8445084721307682777162829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45040451846974308144868421 8445084721307682777162829)
                ·
                  refine ⟨3166906770490381041436061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8445084721307682777162829 3166906770490381041436061)
                  ·
                    refine ⟨1187590038933892890538523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166906770490381041436061 1187590038933892890538523)
                    ·
                      rfl

theorem cell22_3469235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 3].length) (baseStart_3469235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469235 prefixEnd_3469235 := by exact prefixLift 3469235
  have htrace : WordTrace (prefixWord ++ tailWord_3469235) baseStart_3469235 baseEnd_3469235 := by
    simpa [prefixWord, tailWord_3469235, baseEnd_3469235] using wordTrace_append hprefix tailTrace_3469235
  have hstable : (prefixWord ++ tailWord_3469235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469235).length < 2 ^ (prefixWord ++ tailWord_3469235).sum := by decide
  have hdescent : baseEnd_3469235 < baseStart_3469235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469237 : List Nat := [1, 3, 3, 2, 1, 4, 2, 6]
def baseStart_3469237 : Nat := 118140960795 + 3469237 * 2 ^ 59
def prefixEnd_3469237 : Nat := 4983230072969 + 3 ^ 40 * 3469237 * 2
def baseEnd_3469237 : Nat := 131954524841640616887613

theorem tailTrace_3469237 : CollatzResearch.WordTrace tailWord_3469237 prefixEnd_3469237 131954524841640616887613 := by
  unfold tailWord_3469237
  simp only [CollatzResearch.WordTrace]
  refine ⟨126533468532554322353493965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84355645688369548235662643 126533468532554322353493965)
  ·
    refine ⟨47450050699707870882560237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126533468532554322353493965 47450050699707870882560237)
    ·
      refine ⟨17793769012390451580960089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47450050699707870882560237 17793769012390451580960089)
      ·
        refine ⟨13345326759292838685720067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17793769012390451580960089 13345326759292838685720067)
        ·
          refine ⟨20017990138939258028580101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13345326759292838685720067 20017990138939258028580101)
          ·
            refine ⟨3753373151051110880358769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20017990138939258028580101 3753373151051110880358769)
            ·
              refine ⟨2815029863288333160269077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753373151051110880358769 2815029863288333160269077)
              ·
                refine ⟨131954524841640616887613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2815029863288333160269077 131954524841640616887613)
                ·
                  rfl

theorem cell22_3469237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 6].length) (baseStart_3469237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469237 prefixEnd_3469237 := by exact prefixLift 3469237
  have htrace : WordTrace (prefixWord ++ tailWord_3469237) baseStart_3469237 baseEnd_3469237 := by
    simpa [prefixWord, tailWord_3469237, baseEnd_3469237] using wordTrace_append hprefix tailTrace_3469237
  have hstable : (prefixWord ++ tailWord_3469237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469237).length < 2 ^ (prefixWord ++ tailWord_3469237).sum := by decide
  have hdescent : baseEnd_3469237 < baseStart_3469237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469248 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 9]
def baseStart_3469248 : Nat := 118140960795 + 3469248 * 2 ^ 59
def prefixEnd_3469248 : Nat := 4983230072969 + 3 ^ 40 * 3469248 * 2
def baseEnd_3469248 : Nat := 395864829699855063321161

theorem tailTrace_3469248 : CollatzResearch.WordTrace tailWord_3469248 prefixEnd_3469248 395864829699855063321161 := by
  unfold tailWord_3469248
  simp only [CollatzResearch.WordTrace]
  refine ⟨63266934867757235616072199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84355913157009647488096265 63266934867757235616072199)
  ·
    refine ⟨94900402301635853424108299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63266934867757235616072199 94900402301635853424108299)
    ·
      refine ⟨142350603452453780136162449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94900402301635853424108299 142350603452453780136162449)
      ·
        refine ⟨106762952589340335102121837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142350603452453780136162449 106762952589340335102121837)
        ·
          refine ⟨40036107221002625663295689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106762952589340335102121837 40036107221002625663295689)
          ·
            refine ⟨30027080415751969247471767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40036107221002625663295689 30027080415751969247471767)
            ·
              refine ⟨45040620623627953871207651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30027080415751969247471767 45040620623627953871207651)
              ·
                refine ⟨67560930935441930806811477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45040620623627953871207651 67560930935441930806811477)
                ·
                  refine ⟨395864829699855063321161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67560930935441930806811477 395864829699855063321161)
                  ·
                    rfl

theorem cell22_3469248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_3469248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469248 prefixEnd_3469248 := by exact prefixLift 3469248
  have htrace : WordTrace (prefixWord ++ tailWord_3469248) baseStart_3469248 baseEnd_3469248 := by
    simpa [prefixWord, tailWord_3469248, baseEnd_3469248] using wordTrace_append hprefix tailTrace_3469248
  have hstable : (prefixWord ++ tailWord_3469248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469248).length < 2 ^ (prefixWord ++ tailWord_3469248).sum := by decide
  have hdescent : baseEnd_3469248 < baseStart_3469248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469269 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_3469269 : Nat := 118140960795 + 3469269 * 2 ^ 59
def prefixEnd_3469269 : Nat := 4983230072969 + 3 ^ 40 * 3469269 * 2
def baseEnd_3469269 : Nat := 1187601677828728135188419

theorem tailTrace_3469269 : CollatzResearch.WordTrace tailWord_3469269 prefixEnd_3469269 1187601677828728135188419 := by
  unfold tailWord_3469269
  simp only [CollatzResearch.WordTrace]
  refine ⟨126534635668438391818658861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84356423778958927879105907 126534635668438391818658861)
  ·
    refine ⟨47450488375664396931997073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126534635668438391818658861 47450488375664396931997073)
    ·
      refine ⟨35587866281748297698997805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47450488375664396931997073 35587866281748297698997805)
      ·
        refine ⟨13345449855655611637124177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35587866281748297698997805 13345449855655611637124177)
        ·
          refine ⟨10009087391741708727843133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13345449855655611637124177 10009087391741708727843133)
          ·
            refine ⟨3753407771903140772941175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10009087391741708727843133 3753407771903140772941175)
            ·
              refine ⟨5630111657854711159411763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753407771903140772941175 5630111657854711159411763)
              ·
                refine ⟨8445167486782066739117645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5630111657854711159411763 8445167486782066739117645)
                ·
                  refine ⟨3166937807543275027169117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8445167486782066739117645 3166937807543275027169117)
                  ·
                    refine ⟨1187601677828728135188419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3166937807543275027169117 1187601677828728135188419)
                    ·
                      rfl

theorem cell22_3469269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_3469269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469269 prefixEnd_3469269 := by exact prefixLift 3469269
  have htrace : WordTrace (prefixWord ++ tailWord_3469269) baseStart_3469269 baseEnd_3469269 := by
    simpa [prefixWord, tailWord_3469269, baseEnd_3469269] using wordTrace_append hprefix tailTrace_3469269
  have hstable : (prefixWord ++ tailWord_3469269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469269).length < 2 ^ (prefixWord ++ tailWord_3469269).sum := by decide
  have hdescent : baseEnd_3469269 < baseStart_3469269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469295 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 3, 4]
def baseStart_3469295 : Nat := 118140960795 + 3469295 * 2 ^ 59
def prefixEnd_3469295 : Nat := 4983230072969 + 3 ^ 40 * 3469295 * 2
def baseEnd_3469295 : Nat := 1187610578160072734038339

theorem tailTrace_3469295 : CollatzResearch.WordTrace tailWord_3469295 prefixEnd_3469295 1187610578160072734038339 := by
  unfold tailWord_3469295
  simp only [CollatzResearch.WordTrace]
  refine ⟨126535583966344198259105339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84357055977562798839403559 126535583966344198259105339)
  ·
    refine ⟨189803375949516297388658009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126535583966344198259105339 189803375949516297388658009)
    ·
      refine ⟨142352531962137223041493507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189803375949516297388658009 142352531962137223041493507)
      ·
        refine ⟨213528797943205834562240261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142352531962137223041493507 213528797943205834562240261)
        ·
          refine ⟨40036649614351093980420049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213528797943205834562240261 40036649614351093980420049)
          ·
            refine ⟨30027487210763320485315037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40036649614351093980420049 30027487210763320485315037)
            ·
              refine ⟨11260307704036245181993139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30027487210763320485315037 11260307704036245181993139)
              ·
                refine ⟨16890461556054367772989709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11260307704036245181993139 16890461556054367772989709)
                ·
                  refine ⟨6333923083520387914871141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16890461556054367772989709 6333923083520387914871141)
                  ·
                    refine ⟨1187610578160072734038339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6333923083520387914871141 1187610578160072734038339)
                    ·
                      rfl

theorem cell22_3469295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_3469295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469295 prefixEnd_3469295 := by exact prefixLift 3469295
  have htrace : WordTrace (prefixWord ++ tailWord_3469295) baseStart_3469295 baseEnd_3469295 := by
    simpa [prefixWord, tailWord_3469295, baseEnd_3469295] using wordTrace_append hprefix tailTrace_3469295
  have hstable : (prefixWord ++ tailWord_3469295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469295).length < 2 ^ (prefixWord ++ tailWord_3469295).sum := by decide
  have hdescent : baseEnd_3469295 < baseStart_3469295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469404 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3469404 : Nat := 118140960795 + 3469404 * 2 ^ 59
def prefixEnd_3469404 : Nat := 4983230072969 + 3 ^ 40 * 3469404 * 2
def baseEnd_3469404 : Nat := 1187647891087632783063005

theorem tailTrace_3469404 : CollatzResearch.WordTrace tailWord_3469404 prefixEnd_3469404 1187647891087632783063005 := by
  unfold tailWord_3469404
  simp only [CollatzResearch.WordTrace]
  refine ⟨63269779761474654937411633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84359706348632873249882177 63269779761474654937411633)
  ·
    refine ⟨47452334821105991203058725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63269779761474654937411633 47452334821105991203058725)
    ·
      refine ⟨8897312778957373350573511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47452334821105991203058725 8897312778957373350573511)
      ·
        refine ⟨13345969168436060025860267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8897312778957373350573511 13345969168436060025860267)
        ·
          refine ⟨20018953752654090038790401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13345969168436060025860267 20018953752654090038790401)
          ·
            refine ⟨15014215314490567529092801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20018953752654090038790401 15014215314490567529092801)
            ·
              refine ⟨11260661485867925646819601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15014215314490567529092801 11260661485867925646819601)
              ·
                refine ⟨8445496114400944235114701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11260661485867925646819601 8445496114400944235114701)
                ·
                  refine ⟨3167061042900354088168013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8445496114400944235114701 3167061042900354088168013)
                  ·
                    refine ⟨1187647891087632783063005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167061042900354088168013 1187647891087632783063005)
                    ·
                      rfl

theorem cell22_3469404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3469404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469404 prefixEnd_3469404 := by exact prefixLift 3469404
  have htrace : WordTrace (prefixWord ++ tailWord_3469404) baseStart_3469404 baseEnd_3469404 := by
    simpa [prefixWord, tailWord_3469404, baseEnd_3469404] using wordTrace_append hprefix tailTrace_3469404
  have hstable : (prefixWord ++ tailWord_3469404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469404).length < 2 ^ (prefixWord ++ tailWord_3469404).sum := by decide
  have hdescent : baseEnd_3469404 < baseStart_3469404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469406 : List Nat := [4, 4, 1, 1, 2, 1, 1, 8]
def baseStart_3469406 : Nat := 118140960795 + 3469406 * 2 ^ 59
def prefixEnd_3469406 : Nat := 4983230072969 + 3 ^ 40 * 3469406 * 2
def baseEnd_3469406 : Nat := 131960952858722827168111

theorem tailTrace_3469406 : CollatzResearch.WordTrace tailWord_3469406 prefixEnd_3469406 131960952858722827168111 := by
  unfold tailWord_3469406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15817454058617758027049509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84359754979294709477597381 15817454058617758027049509)
  ·
    refine ⟨2965772635990829630071783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15817454058617758027049509 2965772635990829630071783)
    ·
      refine ⟨4448658953986244445107675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2965772635990829630071783 4448658953986244445107675)
      ·
        refine ⟨6672988430979366667661513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448658953986244445107675 6672988430979366667661513)
        ·
          refine ⟨5004741323234525000746135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672988430979366667661513 5004741323234525000746135)
          ·
            refine ⟨7507111984851787501119203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004741323234525000746135 7507111984851787501119203)
            ·
              refine ⟨11260667977277681251678805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507111984851787501119203 11260667977277681251678805)
              ·
                refine ⟨131960952858722827168111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11260667977277681251678805 131960952858722827168111)
                ·
                  rfl

theorem cell22_3469406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_3469406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469406 prefixEnd_3469406 := by exact prefixLift 3469406
  have htrace : WordTrace (prefixWord ++ tailWord_3469406) baseStart_3469406 baseEnd_3469406 := by
    simpa [prefixWord, tailWord_3469406, baseEnd_3469406] using wordTrace_append hprefix tailTrace_3469406
  have hstable : (prefixWord ++ tailWord_3469406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469406).length < 2 ^ (prefixWord ++ tailWord_3469406).sum := by decide
  have hdescent : baseEnd_3469406 < baseStart_3469406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469464 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_3469464 : Nat := 118140960795 + 3469464 * 2 ^ 59
def prefixEnd_3469464 : Nat := 4983230072969 + 3 ^ 40 * 3469464 * 2
def baseEnd_3469464 : Nat := 1187668430313812626562821

theorem tailTrace_3469464 : CollatzResearch.WordTrace tailWord_3469464 prefixEnd_3469464 1187668430313812626562821 := by
  unfold tailWord_3469464
  simp only [CollatzResearch.WordTrace]
  refine ⟨63270873951365970061003723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84361165268487960081338297 63270873951365970061003723)
  ·
    refine ⟨94906310927048955091505585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63270873951365970061003723 94906310927048955091505585)
    ·
      refine ⟨71179733195286716318629189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94906310927048955091505585 71179733195286716318629189)
      ·
        refine ⟨13346199974116259309742973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71179733195286716318629189 13346199974116259309742973)
        ·
          refine ⟨5004824990293597241153615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13346199974116259309742973 5004824990293597241153615)
          ·
            refine ⟨7507237485440395861730423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004824990293597241153615 7507237485440395861730423)
            ·
              refine ⟨11260856228160593792595635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507237485440395861730423 11260856228160593792595635)
              ·
                refine ⟨16891284342240890688893453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11260856228160593792595635 16891284342240890688893453)
                ·
                  refine ⟨6334231628340334008335045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16891284342240890688893453 6334231628340334008335045)
                  ·
                    refine ⟨1187668430313812626562821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334231628340334008335045 1187668430313812626562821)
                    ·
                      rfl

theorem cell22_3469464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_3469464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469464 prefixEnd_3469464 := by exact prefixLift 3469464
  have htrace : WordTrace (prefixWord ++ tailWord_3469464) baseStart_3469464 baseEnd_3469464 := by
    simpa [prefixWord, tailWord_3469464, baseEnd_3469464] using wordTrace_append hprefix tailTrace_3469464
  have hstable : (prefixWord ++ tailWord_3469464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469464).length < 2 ^ (prefixWord ++ tailWord_3469464).sum := by decide
  have hdescent : baseEnd_3469464 < baseStart_3469464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469477 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3469477 : Nat := 118140960795 + 3469477 * 2 ^ 59
def prefixEnd_3469477 : Nat := 4983230072969 + 3 ^ 40 * 3469477 * 2
def baseEnd_3469477 : Nat := 1187672880479484925987781

theorem tailTrace_3469477 : CollatzResearch.WordTrace tailWord_3469477 prefixEnd_3469477 1187672880479484925987781 := by
  unfold tailWord_3469477
  simp only [CollatzResearch.WordTrace]
  refine ⟨126542222051684843342230685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84361481367789895561487123 126542222051684843342230685)
  ·
    refine ⟨47453333269381816253336507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126542222051684843342230685 47453333269381816253336507)
    ·
      refine ⟨71179999904072724380004761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47453333269381816253336507 71179999904072724380004761)
      ·
        refine ⟨53384999928054543285003571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71179999904072724380004761 53384999928054543285003571)
        ·
          refine ⟨80077499892081814927505357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53384999928054543285003571 80077499892081814927505357)
          ·
            refine ⟨30029062459530680597814509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80077499892081814927505357 30029062459530680597814509)
            ·
              refine ⟨11260898422324005224180441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30029062459530680597814509 11260898422324005224180441)
              ·
                refine ⟨8445673816743003918135331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11260898422324005224180441 8445673816743003918135331)
                ·
                  refine ⟨12668510725114505877202997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8445673816743003918135331 12668510725114505877202997)
                  ·
                    refine ⟨1187672880479484925987781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12668510725114505877202997 1187672880479484925987781)
                    ·
                      rfl

theorem cell22_3469477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3469477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469477 prefixEnd_3469477 := by exact prefixLift 3469477
  have htrace : WordTrace (prefixWord ++ tailWord_3469477) baseStart_3469477 baseEnd_3469477 := by
    simpa [prefixWord, tailWord_3469477, baseEnd_3469477] using wordTrace_append hprefix tailTrace_3469477
  have hstable : (prefixWord ++ tailWord_3469477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469477).length < 2 ^ (prefixWord ++ tailWord_3469477).sum := by decide
  have hdescent : baseEnd_3469477 < baseStart_3469477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469526 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_3469526 : Nat := 118140960795 + 3469526 * 2 ^ 59
def prefixEnd_3469526 : Nat := 4983230072969 + 3 ^ 40 * 3469526 * 2
def baseEnd_3469526 : Nat := 1187689654180865131512631

theorem tailTrace_3469526 : CollatzResearch.WordTrace tailWord_3469526 prefixEnd_3469526 1187689654180865131512631 := by
  unfold tailWord_3469526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7909000576781707794422777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84362672819004883140509621 7909000576781707794422777)
  ·
    refine ⟨5931750432586280845817083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7909000576781707794422777 5931750432586280845817083)
    ·
      refine ⟨8897625648879421268725625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5931750432586280845817083 8897625648879421268725625)
      ·
        refine ⟨6673219236659565951544219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8897625648879421268725625 6673219236659565951544219)
        ·
          refine ⟨10009828854989348927316329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6673219236659565951544219 10009828854989348927316329)
          ·
            refine ⟨7507371641242011695487247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10009828854989348927316329 7507371641242011695487247)
            ·
              refine ⟨11261057461863017543230871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507371641242011695487247 11261057461863017543230871)
              ·
                refine ⟨16891586192794526314846307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11261057461863017543230871 16891586192794526314846307)
                ·
                  refine ⟨25337379289191789472269461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16891586192794526314846307 25337379289191789472269461)
                  ·
                    refine ⟨1187689654180865131512631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25337379289191789472269461 1187689654180865131512631)
                    ·
                      rfl

theorem cell22_3469526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_3469526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469526 prefixEnd_3469526 := by exact prefixLift 3469526
  have htrace : WordTrace (prefixWord ++ tailWord_3469526) baseStart_3469526 baseEnd_3469526 := by
    simpa [prefixWord, tailWord_3469526, baseEnd_3469526] using wordTrace_append hprefix tailTrace_3469526
  have hstable : (prefixWord ++ tailWord_3469526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469526).length < 2 ^ (prefixWord ++ tailWord_3469526).sum := by decide
  have hdescent : baseEnd_3469526 < baseStart_3469526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469532 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3469532 : Nat := 118140960795 + 3469532 * 2 ^ 59
def prefixEnd_3469532 : Nat := 4983230072969 + 3 ^ 40 * 3469532 * 2
def baseEnd_3469532 : Nat := 1187691708103483115862613

theorem tailTrace_3469532 : CollatzResearch.WordTrace tailWord_3469532 prefixEnd_3469532 1187691708103483115862613 := by
  unfold tailWord_3469532
  simp only [CollatzResearch.WordTrace]
  refine ⟨63272114033242793867741425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84362818710990391823655233 63272114033242793867741425)
  ·
    refine ⟨47454085524932095400806069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63272114033242793867741425 47454085524932095400806069)
    ·
      refine ⟨4448820517962383943825569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47454085524932095400806069 4448820517962383943825569)
      ·
        refine ⟨3336615388471787957869177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4448820517962383943825569 3336615388471787957869177)
        ·
          refine ⟨2502461541353840968401883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336615388471787957869177 2502461541353840968401883)
          ·
            refine ⟨3753692312030761452602825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502461541353840968401883 3753692312030761452602825)
            ·
              refine ⟨2815269234023071089452119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3753692312030761452602825 2815269234023071089452119)
              ·
                refine ⟨4222903851034606634178179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815269234023071089452119 4222903851034606634178179)
                ·
                  refine ⟨6334355776551909951267269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4222903851034606634178179 6334355776551909951267269)
                  ·
                    refine ⟨1187691708103483115862613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334355776551909951267269 1187691708103483115862613)
                    ·
                      rfl

theorem cell22_3469532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3469532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469532 prefixEnd_3469532 := by exact prefixLift 3469532
  have htrace : WordTrace (prefixWord ++ tailWord_3469532) baseStart_3469532 baseEnd_3469532 := by
    simpa [prefixWord, tailWord_3469532, baseEnd_3469532] using wordTrace_append hprefix tailTrace_3469532
  have hstable : (prefixWord ++ tailWord_3469532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469532).length < 2 ^ (prefixWord ++ tailWord_3469532).sum := by decide
  have hdescent : baseEnd_3469532 < baseStart_3469532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469567 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 2, 5]
def baseStart_3469567 : Nat := 118140960795 + 3469567 * 2 ^ 59
def prefixEnd_3469567 : Nat := 4983230072969 + 3 ^ 40 * 3469567 * 2
def baseEnd_3469567 : Nat := 1187703689318754691237505

theorem tailTrace_3469567 : CollatzResearch.WordTrace tailWord_3469567 prefixEnd_3469567 1187703689318754691237505 := by
  unfold tailWord_3469567
  simp only [CollatzResearch.WordTrace]
  refine ⟨126545504621358788713006955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84363669747572525808671303 126545504621358788713006955)
  ·
    refine ⟨189818256932038183069510433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126545504621358788713006955 189818256932038183069510433)
    ·
      refine ⟨142363692699028637302132825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189818256932038183069510433 142363692699028637302132825)
      ·
        refine ⟨106772769524271477976599619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142363692699028637302132825 106772769524271477976599619)
        ·
          refine ⟨160159154286407216964899429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106772769524271477976599619 160159154286407216964899429)
          ·
            refine ⟨30029841428701353180918643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160159154286407216964899429 30029841428701353180918643)
            ·
              refine ⟨45044762143052029771377965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30029841428701353180918643 45044762143052029771377965)
              ·
                refine ⟨16891785803644511164266737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45044762143052029771377965 16891785803644511164266737)
                ·
                  refine ⟨12668839352733383373200053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16891785803644511164266737 12668839352733383373200053)
                  ·
                    refine ⟨1187703689318754691237505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12668839352733383373200053 1187703689318754691237505)
                    ·
                      rfl

theorem cell22_3469567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_3469567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469567 prefixEnd_3469567 := by exact prefixLift 3469567
  have htrace : WordTrace (prefixWord ++ tailWord_3469567) baseStart_3469567 baseEnd_3469567 := by
    simpa [prefixWord, tailWord_3469567, baseEnd_3469567] using wordTrace_append hprefix tailTrace_3469567
  have hstable : (prefixWord ++ tailWord_3469567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469567).length < 2 ^ (prefixWord ++ tailWord_3469567).sum := by decide
  have hdescent : baseEnd_3469567 < baseStart_3469567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469607 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3469607 : Nat := 118140960795 + 3469607 * 2 ^ 59
def prefixEnd_3469607 : Nat := 4983230072969 + 3 ^ 40 * 3469607 * 2
def baseEnd_3469607 : Nat := 1187717382136207920237383

theorem tailTrace_3469607 : CollatzResearch.WordTrace tailWord_3469607 prefixEnd_3469607 1187717382136207920237383 := by
  unfold tailWord_3469607
  simp only [CollatzResearch.WordTrace]
  refine ⟨126546963541213875544463075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84364642360809250362975383 126546963541213875544463075)
  ·
    refine ⟨189820445311820813316694613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126546963541213875544463075 189820445311820813316694613)
    ·
      refine ⟨2224458343497900156055015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 189820445311820813316694613 2224458343497900156055015)
      ·
        refine ⟨3336687515246850234082523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224458343497900156055015 3336687515246850234082523)
        ·
          refine ⟨5005031272870275351123785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336687515246850234082523 5005031272870275351123785)
          ·
            refine ⟨3753773454652706513342839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5005031272870275351123785 3753773454652706513342839)
            ·
              refine ⟨5630660181979059770014259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753773454652706513342839 5630660181979059770014259)
              ·
                refine ⟨8445990272968589655021389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5630660181979059770014259 8445990272968589655021389)
                ·
                  refine ⟨3167246352363221120633021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8445990272968589655021389 3167246352363221120633021)
                  ·
                    refine ⟨1187717382136207920237383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167246352363221120633021 1187717382136207920237383)
                    ·
                      rfl

theorem cell22_3469607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3469607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469607 prefixEnd_3469607 := by exact prefixLift 3469607
  have htrace : WordTrace (prefixWord ++ tailWord_3469607) baseStart_3469607 baseEnd_3469607 := by
    simpa [prefixWord, tailWord_3469607, baseEnd_3469607] using wordTrace_append hprefix tailTrace_3469607
  have hstable : (prefixWord ++ tailWord_3469607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469607).length < 2 ^ (prefixWord ++ tailWord_3469607).sum := by decide
  have hdescent : baseEnd_3469607 < baseStart_3469607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469676 : List Nat := [2, 2, 1, 1, 6, 2, 1, 7]
def baseStart_3469676 : Nat := 118140960795 + 3469676 * 2 ^ 59
def prefixEnd_3469676 : Nat := 4983230072969 + 3 ^ 40 * 3469676 * 2
def baseEnd_3469676 : Nat := 131971222471812748918019

theorem tailTrace_3469676 : CollatzResearch.WordTrace tailWord_3469676 prefixEnd_3469676 131971222471812748918019 := by
  unfold tailWord_3469676
  simp only [CollatzResearch.WordTrace]
  refine ⟨63274740088981950164362441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84366320118642600219149921 63274740088981950164362441)
  ·
    refine ⟨47456055066736462623271831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63274740088981950164362441 47456055066736462623271831)
    ·
      refine ⟨71184082600104693934907747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47456055066736462623271831 71184082600104693934907747)
      ·
        refine ⟨106776123900157040902361621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71184082600104693934907747 106776123900157040902361621)
        ·
          refine ⟨5005130807819861292298201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106776123900157040902361621 5005130807819861292298201)
          ·
            refine ⟨3753848105864895969223651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5005130807819861292298201 3753848105864895969223651)
            ·
              refine ⟨5630772158797343953835477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753848105864895969223651 5630772158797343953835477)
              ·
                refine ⟨131971222471812748918019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5630772158797343953835477 131971222471812748918019)
                ·
                  rfl

theorem cell22_3469676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 7].length) (baseStart_3469676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469676 prefixEnd_3469676 := by exact prefixLift 3469676
  have htrace : WordTrace (prefixWord ++ tailWord_3469676) baseStart_3469676 baseEnd_3469676 := by
    simpa [prefixWord, tailWord_3469676, baseEnd_3469676] using wordTrace_append hprefix tailTrace_3469676
  have hstable : (prefixWord ++ tailWord_3469676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469676).length < 2 ^ (prefixWord ++ tailWord_3469676).sum := by decide
  have hdescent : baseEnd_3469676 < baseStart_3469676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469691 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 3, 3]
def baseStart_3469691 : Nat := 118140960795 + 3469691 * 2 ^ 59
def prefixEnd_3469691 : Nat := 4983230072969 + 3 ^ 40 * 3469691 * 2
def baseEnd_3469691 : Nat := 1187746137052859701137125

theorem tailTrace_3469691 : CollatzResearch.WordTrace tailWord_3469691 prefixEnd_3469691 1187746137052859701137125 := by
  unfold tailWord_3469691
  simp only [CollatzResearch.WordTrace]
  refine ⟨126550027272909557890520927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84366684848606371927013951 126550027272909557890520927)
  ·
    refine ⟨189825040909364336835781391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126550027272909557890520927 189825040909364336835781391)
    ·
      refine ⟨284737561364046505253672087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189825040909364336835781391 284737561364046505253672087)
      ·
        refine ⟨427106342046069757880508131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284737561364046505253672087 427106342046069757880508131)
        ·
          refine ⟨640659513069104636820762197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427106342046069757880508131 640659513069104636820762197)
          ·
            refine ⟨7507728668778569962743307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 640659513069104636820762197 7507728668778569962743307)
            ·
              refine ⟨11261593003167854944114961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507728668778569962743307 11261593003167854944114961)
              ·
                refine ⟨8446194752375891208086221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11261593003167854944114961 8446194752375891208086221)
                ·
                  refine ⟨3167323032140959203032333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8446194752375891208086221 3167323032140959203032333)
                  ·
                    refine ⟨1187746137052859701137125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167323032140959203032333 1187746137052859701137125)
                    ·
                      rfl

theorem cell22_3469691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 3].length) (baseStart_3469691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469691 prefixEnd_3469691 := by exact prefixLift 3469691
  have htrace : WordTrace (prefixWord ++ tailWord_3469691) baseStart_3469691 baseEnd_3469691 := by
    simpa [prefixWord, tailWord_3469691, baseEnd_3469691] using wordTrace_append hprefix tailTrace_3469691
  have hstable : (prefixWord ++ tailWord_3469691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469691).length < 2 ^ (prefixWord ++ tailWord_3469691).sum := by decide
  have hdescent : baseEnd_3469691 < baseStart_3469691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469704 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 7]
def baseStart_3469704 : Nat := 118140960795 + 3469704 * 2 ^ 59
def prefixEnd_3469704 : Nat := 4983230072969 + 3 ^ 40 * 3469704 * 2
def baseEnd_3469704 : Nat := 395916862406177333520695

theorem tailTrace_3469704 : CollatzResearch.WordTrace tailWord_3469704 prefixEnd_3469704 395916862406177333520695 := by
  unfold tailWord_3469704
  simp only [CollatzResearch.WordTrace]
  refine ⟨63275250710931230555372083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84367000947908307407162777 63275250710931230555372083)
  ·
    refine ⟨94912876066396845833058125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63275250710931230555372083 94912876066396845833058125)
    ·
      refine ⟨35592328524898817187396797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94912876066396845833058125 35592328524898817187396797)
      ·
        refine ⟨13347123196837056445273799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35592328524898817187396797 13347123196837056445273799)
        ·
          refine ⟨20020684795255584667910699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13347123196837056445273799 20020684795255584667910699)
          ·
            refine ⟨30031027192883377001866049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20020684795255584667910699 30031027192883377001866049)
            ·
              refine ⟨22523270394662532751399537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30031027192883377001866049 22523270394662532751399537)
              ·
                refine ⟨16892452795996899563549653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22523270394662532751399537 16892452795996899563549653)
                ·
                  refine ⟨395916862406177333520695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16892452795996899563549653 395916862406177333520695)
                  ·
                    rfl

theorem cell22_3469704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_3469704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469704 prefixEnd_3469704 := by exact prefixLift 3469704
  have htrace : WordTrace (prefixWord ++ tailWord_3469704) baseStart_3469704 baseEnd_3469704 := by
    simpa [prefixWord, tailWord_3469704, baseEnd_3469704] using wordTrace_append hprefix tailTrace_3469704
  have hstable : (prefixWord ++ tailWord_3469704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469704).length < 2 ^ (prefixWord ++ tailWord_3469704).sum := by decide
  have hdescent : baseEnd_3469704 < baseStart_3469704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469708 : List Nat := [2, 2, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_3469708 : Nat := 118140960795 + 3469708 * 2 ^ 59
def prefixEnd_3469708 : Nat := 4983230072969 + 3 ^ 40 * 3469708 * 2
def baseEnd_3469708 : Nat := 1187751956500277323462073

theorem tailTrace_3469708 : CollatzResearch.WordTrace tailWord_3469708 prefixEnd_3469708 1187751956500277323462073 := by
  unfold tailWord_3469708
  simp only [CollatzResearch.WordTrace]
  refine ⟨63275323656923984896944889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84367098209231979862593185 63275323656923984896944889)
  ·
    refine ⟨47456492742692988672708667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63275323656923984896944889 47456492742692988672708667)
    ·
      refine ⟨71184739114039483009063001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47456492742692988672708667 71184739114039483009063001)
      ·
        refine ⟨53388554335529612256797251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71184739114039483009063001 53388554335529612256797251)
        ·
          refine ⟨80082831503294418385195877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53388554335529612256797251 80082831503294418385195877)
          ·
            refine ⟨15015530906867703447224227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80082831503294418385195877 15015530906867703447224227)
            ·
              refine ⟨22523296360301555170836341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15015530906867703447224227 22523296360301555170836341)
              ·
                refine ⟨2111559033778270797265907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22523296360301555170836341 2111559033778270797265907)
                ·
                  refine ⟨3167338550667406195898861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111559033778270797265907 3167338550667406195898861)
                  ·
                    refine ⟨1187751956500277323462073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167338550667406195898861 1187751956500277323462073)
                    ·
                      rfl

theorem cell22_3469708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_3469708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469708 prefixEnd_3469708 := by exact prefixLift 3469708
  have htrace : WordTrace (prefixWord ++ tailWord_3469708) baseStart_3469708 baseEnd_3469708 := by
    simpa [prefixWord, tailWord_3469708, baseEnd_3469708] using wordTrace_append hprefix tailTrace_3469708
  have hstable : (prefixWord ++ tailWord_3469708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469708).length < 2 ^ (prefixWord ++ tailWord_3469708).sum := by decide
  have hdescent : baseEnd_3469708 < baseStart_3469708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469719 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3469719 : Nat := 118140960795 + 3469719 * 2 ^ 59
def prefixEnd_3469719 : Nat := 4983230072969 + 3 ^ 40 * 3469719 * 2
def baseEnd_3469719 : Nat := 1187755722025076961437039

theorem tailTrace_3469719 : CollatzResearch.WordTrace tailWord_3469719 prefixEnd_3469719 1187755722025076961437039 := by
  unfold tailWord_3469719
  simp only [CollatzResearch.WordTrace]
  refine ⟨126551048516808118672540211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84367365677872079115026807 126551048516808118672540211)
  ·
    refine ⟨189826572775212178008810317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126551048516808118672540211 189826572775212178008810317)
    ·
      refine ⟨71184964790704566753303869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189826572775212178008810317 71184964790704566753303869)
      ·
        refine ⟨26694361796514212532488951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71184964790704566753303869 26694361796514212532488951)
        ·
          refine ⟨40041542694771318798733427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26694361796514212532488951 40041542694771318798733427)
          ·
            refine ⟨60062314042156978198100141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40041542694771318798733427 60062314042156978198100141)
            ·
              refine ⟨22523367765808866824287553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60062314042156978198100141 22523367765808866824287553)
              ·
                refine ⟨16892525824356650118215665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22523367765808866824287553 16892525824356650118215665)
                ·
                  refine ⟨12669394368267487588661749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16892525824356650118215665 12669394368267487588661749)
                  ·
                    refine ⟨1187755722025076961437039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12669394368267487588661749 1187755722025076961437039)
                    ·
                      rfl

theorem cell22_3469719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3469719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469719 prefixEnd_3469719 := by exact prefixLift 3469719
  have htrace : WordTrace (prefixWord ++ tailWord_3469719) baseStart_3469719 baseEnd_3469719 := by
    simpa [prefixWord, tailWord_3469719, baseEnd_3469719] using wordTrace_append hprefix tailTrace_3469719
  have hstable : (prefixWord ++ tailWord_3469719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469719).length < 2 ^ (prefixWord ++ tailWord_3469719).sum := by decide
  have hdescent : baseEnd_3469719 < baseStart_3469719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469751 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 1, 4]
def baseStart_3469751 : Nat := 118140960795 + 3469751 * 2 ^ 59
def prefixEnd_3469751 : Nat := 4983230072969 + 3 ^ 40 * 3469751 * 2
def baseEnd_3469751 : Nat := 1187766676279039544636941

theorem tailTrace_3469751 : CollatzResearch.WordTrace tailWord_3469751 prefixEnd_3469751 1187766676279039544636941 := by
  unfold tailWord_3469751
  simp only [CollatzResearch.WordTrace]
  refine ⟨126552215652692188137705107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84368143768461458758470071 126552215652692188137705107)
  ·
    refine ⟨189828323479038282206557661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126552215652692188137705107 189828323479038282206557661)
    ·
      refine ⟨71185621304639355827459123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189828323479038282206557661 71185621304639355827459123)
      ·
        refine ⟨106778431956959033741188685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71185621304639355827459123 106778431956959033741188685)
        ·
          refine ⟨40041911983859637652945757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106778431956959033741188685 40041911983859637652945757)
          ·
            refine ⟨15015716993947364119854659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40041911983859637652945757 15015716993947364119854659)
            ·
              refine ⟨22523575490921046179781989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15015716993947364119854659 22523575490921046179781989)
              ·
                refine ⟨4223170404547696158709123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22523575490921046179781989 4223170404547696158709123)
                ·
                  refine ⟨6334755606821544238063685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4223170404547696158709123 6334755606821544238063685)
                  ·
                    refine ⟨1187766676279039544636941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6334755606821544238063685 1187766676279039544636941)
                    ·
                      rfl

theorem cell22_3469751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_3469751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469751 prefixEnd_3469751 := by exact prefixLift 3469751
  have htrace : WordTrace (prefixWord ++ tailWord_3469751) baseStart_3469751 baseEnd_3469751 := by
    simpa [prefixWord, tailWord_3469751, baseEnd_3469751] using wordTrace_append hprefix tailTrace_3469751
  have hstable : (prefixWord ++ tailWord_3469751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469751).length < 2 ^ (prefixWord ++ tailWord_3469751).sum := by decide
  have hdescent : baseEnd_3469751 < baseStart_3469751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469824 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_3469824 : Nat := 118140960795 + 3469824 * 2 ^ 59
def prefixEnd_3469824 : Nat := 4983230072969 + 3 ^ 40 * 3469824 * 2
def baseEnd_3469824 : Nat := 1187791665670891687561717

theorem tailTrace_3469824 : CollatzResearch.WordTrace tailWord_3469824 prefixEnd_3469824 1187791665670891687561717 := by
  unfold tailWord_3469824
  simp only [CollatzResearch.WordTrace]
  refine ⟨63277439090713860802556263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84369918787618481070075017 63277439090713860802556263)
  ·
    refine ⟨94916158636070791203834395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63277439090713860802556263 94916158636070791203834395)
    ·
      refine ⟨142374237954106186805751593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94916158636070791203834395 142374237954106186805751593)
      ·
        refine ⟨106780678465579640104313695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142374237954106186805751593 106780678465579640104313695)
        ·
          refine ⟨160171017698369460156470543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106780678465579640104313695 160171017698369460156470543)
          ·
            refine ⟨240256526547554190234705815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160171017698369460156470543 240256526547554190234705815)
            ·
              refine ⟨360384789821331285352058723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240256526547554190234705815 360384789821331285352058723)
              ·
                refine ⟨540577184731996928028088085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360384789821331285352058723 540577184731996928028088085)
                ·
                  refine ⟨25339555534312356001316629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 540577184731996928028088085 25339555534312356001316629)
                  ·
                    refine ⟨1187791665670891687561717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25339555534312356001316629 1187791665670891687561717)
                    ·
                      rfl

theorem cell22_3469824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_3469824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469824 prefixEnd_3469824 := by exact prefixLift 3469824
  have htrace : WordTrace (prefixWord ++ tailWord_3469824) baseStart_3469824 baseEnd_3469824 := by
    simpa [prefixWord, tailWord_3469824, baseEnd_3469824] using wordTrace_append hprefix tailTrace_3469824
  have hstable : (prefixWord ++ tailWord_3469824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469824).length < 2 ^ (prefixWord ++ tailWord_3469824).sum := by decide
  have hdescent : baseEnd_3469824 < baseStart_3469824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3469894 : List Nat := [6, 1, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3469894 : Nat := 118140960795 + 3469894 * 2 ^ 59
def prefixEnd_3469894 : Nat := 4983230072969 + 3 ^ 40 * 3469894 * 2
def baseEnd_3469894 : Nat := 1187815628101434838311503

theorem tailTrace_3469894 : CollatzResearch.WordTrace tailWord_3469894 prefixEnd_3469894 1187815628101434838311503 := by
  unfold tailWord_3469894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954919727849191361255023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84371620860782749040107157 3954919727849191361255023)
  ·
    refine ⟨5932379591773787041882535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3954919727849191361255023 5932379591773787041882535)
    ·
      refine ⟨8898569387660680562823803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5932379591773787041882535 8898569387660680562823803)
      ·
        refine ⟨13347854081491020844235705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898569387660680562823803 13347854081491020844235705)
        ·
          refine ⟨10010890561118265633176779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13347854081491020844235705 10010890561118265633176779)
          ·
            refine ⟨15016335841677398449765169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10010890561118265633176779 15016335841677398449765169)
            ·
              refine ⟨11262251881258048837323877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15016335841677398449765169 11262251881258048837323877)
              ·
                refine ⟨2111672227735884156998227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11262251881258048837323877 2111672227735884156998227)
                ·
                  refine ⟨3167508341603826235497341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111672227735884156998227 3167508341603826235497341)
                  ·
                    refine ⟨1187815628101434838311503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167508341603826235497341 1187815628101434838311503)
                    ·
                      rfl

theorem cell22_3469894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3469894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3469894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3469894 prefixEnd_3469894 := by exact prefixLift 3469894
  have htrace : WordTrace (prefixWord ++ tailWord_3469894) baseStart_3469894 baseEnd_3469894 := by
    simpa [prefixWord, tailWord_3469894, baseEnd_3469894] using wordTrace_append hprefix tailTrace_3469894
  have hstable : (prefixWord ++ tailWord_3469894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3469894).length < 2 ^ (prefixWord ++ tailWord_3469894).sum := by decide
  have hdescent : baseEnd_3469894 < baseStart_3469894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3469894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470012 : List Nat := [2, 2, 2, 3, 1, 1, 3, 4, 1, 3]
def baseStart_3470012 : Nat := 118140960795 + 3470012 * 2 ^ 59
def prefixEnd_3470012 : Nat := 4983230072969 + 3 ^ 40 * 3470012 * 2
def baseEnd_3470012 : Nat := 1187856021912921863861141

theorem tailTrace_3470012 : CollatzResearch.WordTrace tailWord_3470012 prefixEnd_3470012 1187856021912921863861141 := by
  unfold tailWord_3470012
  simp only [CollatzResearch.WordTrace]
  refine ⟨63280867552373314856478145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84374490069831086475304193 63280867552373314856478145)
  ·
    refine ⟨47460650664279986142358609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63280867552373314856478145 47460650664279986142358609)
    ·
      refine ⟨35595487998209989606768957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47460650664279986142358609 35595487998209989606768957)
      ·
        refine ⟨13348307999328746102538359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35595487998209989606768957 13348307999328746102538359)
        ·
          refine ⟨20022461998993119153807539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13348307999328746102538359 20022461998993119153807539)
          ·
            refine ⟨30033692998489678730711309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20022461998993119153807539 30033692998489678730711309)
            ·
              refine ⟨11262634874433629524016741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30033692998489678730711309 11262634874433629524016741)
              ·
                refine ⟨2111744038956305535753139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11262634874433629524016741 2111744038956305535753139)
                ·
                  refine ⟨3167616058434458303629709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2111744038956305535753139 3167616058434458303629709)
                  ·
                    refine ⟨1187856021912921863861141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167616058434458303629709 1187856021912921863861141)
                    ·
                      rfl

theorem cell22_3470012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_3470012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470012 prefixEnd_3470012 := by exact prefixLift 3470012
  have htrace : WordTrace (prefixWord ++ tailWord_3470012) baseStart_3470012 baseEnd_3470012 := by
    simpa [prefixWord, tailWord_3470012, baseEnd_3470012] using wordTrace_append hprefix tailTrace_3470012
  have hstable : (prefixWord ++ tailWord_3470012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470012).length < 2 ^ (prefixWord ++ tailWord_3470012).sum := by decide
  have hdescent : baseEnd_3470012 < baseStart_3470012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470021 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3470021 : Nat := 118140960795 + 3470021 * 2 ^ 59
def prefixEnd_3470021 : Nat := 4983230072969 + 3 ^ 40 * 3470021 * 2
def baseEnd_3470021 : Nat := 1187859102796848840386113

theorem tailTrace_3470021 : CollatzResearch.WordTrace tailWord_3470021 prefixEnd_3470021 1187859102796848840386113 := by
  unfold tailWord_3470021
  simp only [CollatzResearch.WordTrace]
  refine ⟨126562063361714024250033917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84374708907809349500022611 126562063361714024250033917)
  ·
    refine ⟨47460773760642759093762719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126562063361714024250033917 47460773760642759093762719)
    ·
      refine ⟨71191160640964138640644079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47460773760642759093762719 71191160640964138640644079)
      ·
        refine ⟨106786740961446207960966119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71191160640964138640644079 106786740961446207960966119)
        ·
          refine ⟨160180111442169311941449179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106786740961446207960966119 160180111442169311941449179)
          ·
            refine ⟨240270167163253967912173769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160180111442169311941449179 240270167163253967912173769)
            ·
              refine ⟨180202625372440475934130327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240270167163253967912173769 180202625372440475934130327)
              ·
                refine ⟨270303938058660713901195491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180202625372440475934130327 270303938058660713901195491)
                ·
                  refine ⟨405455907087991070851793237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270303938058660713901195491 405455907087991070851793237)
                  ·
                    refine ⟨1187859102796848840386113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 405455907087991070851793237 1187859102796848840386113)
                    ·
                      rfl

theorem cell22_3470021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3470021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470021 prefixEnd_3470021 := by exact prefixLift 3470021
  have htrace : WordTrace (prefixWord ++ tailWord_3470021) baseStart_3470021 baseEnd_3470021 := by
    simpa [prefixWord, tailWord_3470021, baseEnd_3470021] using wordTrace_append hprefix tailTrace_3470021
  have hstable : (prefixWord ++ tailWord_3470021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470021).length < 2 ^ (prefixWord ++ tailWord_3470021).sum := by decide
  have hdescent : baseEnd_3470021 < baseStart_3470021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470029 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3470029 : Nat := 118140960795 + 3470029 * 2 ^ 59
def prefixEnd_3470029 : Nat := 4983230072969 + 3 ^ 40 * 3470029 * 2
def baseEnd_3470029 : Nat := 1187861841360339486186089

theorem tailTrace_3470029 : CollatzResearch.WordTrace tailWord_3470029 prefixEnd_3470029 1187861841360339486186089 := by
  unfold tailWord_3470029
  simp only [CollatzResearch.WordTrace]
  refine ⟨126562355145685041616325141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84374903430456694410883427 126562355145685041616325141)
  ·
    refine ⟨5932610397453986325765241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126562355145685041616325141 5932610397453986325765241)
    ·
      refine ⟨4449457798090489744323931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5932610397453986325765241 4449457798090489744323931)
      ·
        refine ⟨6674186697135734616485897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449457798090489744323931 6674186697135734616485897)
        ·
          refine ⟨5005640022851800962364423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6674186697135734616485897 5005640022851800962364423)
          ·
            refine ⟨7508460034277701443546635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005640022851800962364423 7508460034277701443546635)
            ·
              refine ⟨11262690051416552165319953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508460034277701443546635 11262690051416552165319953)
              ·
                refine ⟨8447017538562414123989965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11262690051416552165319953 8447017538562414123989965)
                ·
                  refine ⟨3167631576960905296496237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8447017538562414123989965 3167631576960905296496237)
                  ·
                    refine ⟨1187861841360339486186089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167631576960905296496237 1187861841360339486186089)
                    ·
                      rfl

theorem cell22_3470029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3470029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470029 prefixEnd_3470029 := by exact prefixLift 3470029
  have htrace : WordTrace (prefixWord ++ tailWord_3470029) baseStart_3470029 baseEnd_3470029 := by
    simpa [prefixWord, tailWord_3470029, baseEnd_3470029] using wordTrace_append hprefix tailTrace_3470029
  have hstable : (prefixWord ++ tailWord_3470029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470029).length < 2 ^ (prefixWord ++ tailWord_3470029).sum := by decide
  have hdescent : baseEnd_3470029 < baseStart_3470029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470070 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3470070 : Nat := 118140960795 + 3470070 * 2 ^ 59
def prefixEnd_3470070 : Nat := 4983230072969 + 3 ^ 40 * 3470070 * 2
def baseEnd_3470070 : Nat := 395958625499409681970321

theorem tailTrace_3470070 : CollatzResearch.WordTrace tailWord_3470070 prefixEnd_3470070 395958625499409681970321 := by
  unfold tailWord_3470070
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910240658658531601160479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84375900359024337079045109 7910240658658531601160479)
  ·
    refine ⟨11865360987987797401740719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7910240658658531601160479 11865360987987797401740719)
    ·
      refine ⟨17798041481981696102611079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11865360987987797401740719 17798041481981696102611079)
      ·
        refine ⟨26697062222972544153916619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17798041481981696102611079 26697062222972544153916619)
        ·
          refine ⟨40045593334458816230874929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26697062222972544153916619 40045593334458816230874929)
          ·
            refine ⟨30034195000844112173156197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40045593334458816230874929 30034195000844112173156197)
            ·
              refine ⟨5631411562658271032466787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30034195000844112173156197 5631411562658271032466787)
              ·
                refine ⟨8447117343987406548700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631411562658271032466787 8447117343987406548700181)
                ·
                  refine ⟨395958625499409681970321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8447117343987406548700181 395958625499409681970321)
                  ·
                    rfl

theorem cell22_3470070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3470070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470070 prefixEnd_3470070 := by exact prefixLift 3470070
  have htrace : WordTrace (prefixWord ++ tailWord_3470070) baseStart_3470070 baseEnd_3470070 := by
    simpa [prefixWord, tailWord_3470070, baseEnd_3470070] using wordTrace_append hprefix tailTrace_3470070
  have hstable : (prefixWord ++ tailWord_3470070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470070).length < 2 ^ (prefixWord ++ tailWord_3470070).sum := by decide
  have hdescent : baseEnd_3470070 < baseStart_3470070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470085 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_3470085 : Nat := 118140960795 + 3470085 * 2 ^ 59
def prefixEnd_3470085 : Nat := 4983230072969 + 3 ^ 40 * 3470085 * 2
def baseEnd_3470085 : Nat := 1187881011304774006785917

theorem tailTrace_3470085 : CollatzResearch.WordTrace tailWord_3470085 prefixEnd_3470085 1187881011304774006785917 := by
  unfold tailWord_3470085
  simp only [CollatzResearch.WordTrace]
  refine ⟨126564397633482163180363709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84376265088988108786909139 126564397633482163180363709)
  ·
    refine ⟨47461649112555811192636391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126564397633482163180363709 47461649112555811192636391)
    ·
      refine ⟨71192473668833716788954587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47461649112555811192636391 71192473668833716788954587)
      ·
        refine ⟨106788710503250575183431881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71192473668833716788954587 106788710503250575183431881)
        ·
          refine ⟨80091532877437931387573911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106788710503250575183431881 80091532877437931387573911)
          ·
            refine ⟨120137299316156897081360867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80091532877437931387573911 120137299316156897081360867)
            ·
              refine ⟨180205948974235345622041301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120137299316156897081360867 180205948974235345622041301)
              ·
                refine ⟨4223576929083640913016593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 180205948974235345622041301 4223576929083640913016593)
                ·
                  refine ⟨3167682696812730684762445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4223576929083640913016593 3167682696812730684762445)
                  ·
                    refine ⟨1187881011304774006785917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167682696812730684762445 1187881011304774006785917)
                    ·
                      rfl

theorem cell22_3470085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_3470085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470085 prefixEnd_3470085 := by exact prefixLift 3470085
  have htrace : WordTrace (prefixWord ++ tailWord_3470085) baseStart_3470085 baseEnd_3470085 := by
    simpa [prefixWord, tailWord_3470085, baseEnd_3470085] using wordTrace_append hprefix tailTrace_3470085
  have hstable : (prefixWord ++ tailWord_3470085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470085).length < 2 ^ (prefixWord ++ tailWord_3470085).sum := by decide
  have hdescent : baseEnd_3470085 < baseStart_3470085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470132 : List Nat := [2, 5, 1, 1, 3, 1, 2, 7]
def baseStart_3470132 : Nat := 118140960795 + 3470132 * 2 ^ 59
def prefixEnd_3470132 : Nat := 4983230072969 + 3 ^ 40 * 3470132 * 2
def baseEnd_3470132 : Nat := 131988566707253505651197

theorem tailTrace_3470132 : CollatzResearch.WordTrace tailWord_3470132 prefixEnd_3470132 131988566707253505651197 := by
  unfold tailWord_3470132
  simp only [CollatzResearch.WordTrace]
  refine ⟨63283055932155945103662325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84377407909541260138216433 63283055932155945103662325)
  ·
    refine ⟨5932786493639619853468343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63283055932155945103662325 5932786493639619853468343)
    ·
      refine ⟨8899179740459429780202515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5932786493639619853468343 8899179740459429780202515)
      ·
        refine ⟨13348769610689144670303773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8899179740459429780202515 13348769610689144670303773)
        ·
          refine ⟨5005788604008429251363915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13348769610689144670303773 5005788604008429251363915)
          ·
            refine ⟨7508682906012643877045873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005788604008429251363915 7508682906012643877045873)
            ·
              refine ⟨5631512179509482907784405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7508682906012643877045873 5631512179509482907784405)
              ·
                refine ⟨131988566707253505651197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5631512179509482907784405 131988566707253505651197)
                ·
                  rfl

theorem cell22_3470132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 7].length) (baseStart_3470132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470132 prefixEnd_3470132 := by exact prefixLift 3470132
  have htrace : WordTrace (prefixWord ++ tailWord_3470132) baseStart_3470132 baseEnd_3470132 := by
    simpa [prefixWord, tailWord_3470132, baseEnd_3470132] using wordTrace_append hprefix tailTrace_3470132
  have hstable : (prefixWord ++ tailWord_3470132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470132).length < 2 ^ (prefixWord ++ tailWord_3470132).sum := by decide
  have hdescent : baseEnd_3470132 < baseStart_3470132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470220 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_3470220 : Nat := 118140960795 + 3470220 * 2 ^ 59
def prefixEnd_3470220 : Nat := 4983230072969 + 3 ^ 40 * 3470220 * 2
def baseEnd_3470220 : Nat := 1187927224563678654660503

theorem tailTrace_3470220 : CollatzResearch.WordTrace tailWord_3470220 prefixEnd_3470220 1187927224563678654660503 := by
  unfold tailWord_3470220
  simp only [CollatzResearch.WordTrace]
  refine ⟨63284660743996540618264057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84379547658662054157685409 63284660743996540618264057)
  ·
    refine ⟨47463495557997405463698043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63284660743996540618264057 47463495557997405463698043)
    ·
      refine ⟨71195243336996108195547065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47463495557997405463698043 71195243336996108195547065)
      ·
        refine ⟨53396432502747081146660299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71195243336996108195547065 53396432502747081146660299)
        ·
          refine ⟨80094648754120621719990449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53396432502747081146660299 80094648754120621719990449)
          ·
            refine ⟨60070986565590466289992837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80094648754120621719990449 60070986565590466289992837)
            ·
              refine ⟨11263309981048212429373657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60070986565590466289992837 11263309981048212429373657)
              ·
                refine ⟨8447482485786159322030243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11263309981048212429373657 8447482485786159322030243)
                ·
                  refine ⟨12671223728679238983045365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8447482485786159322030243 12671223728679238983045365)
                  ·
                    refine ⟨1187927224563678654660503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12671223728679238983045365 1187927224563678654660503)
                    ·
                      rfl

theorem cell22_3470220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_3470220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470220 prefixEnd_3470220 := by exact prefixLift 3470220
  have htrace : WordTrace (prefixWord ++ tailWord_3470220) baseStart_3470220 baseEnd_3470220 := by
    simpa [prefixWord, tailWord_3470220, baseEnd_3470220] using wordTrace_append hprefix tailTrace_3470220
  have hstable : (prefixWord ++ tailWord_3470220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470220).length < 2 ^ (prefixWord ++ tailWord_3470220).sum := by decide
  have hdescent : baseEnd_3470220 < baseStart_3470220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470237 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3470237 : Nat := 118140960795 + 3470237 * 2 ^ 59
def prefixEnd_3470237 : Nat := 4983230072969 + 3 ^ 40 * 3470237 * 2
def baseEnd_3470237 : Nat := 1187933044011096276985451

theorem tailTrace_3470237 : CollatzResearch.WordTrace tailWord_3470237 prefixEnd_3470237 1187933044011096276985451 := by
  unfold tailWord_3470237
  simp only [CollatzResearch.WordTrace]
  refine ⟨126569941528931493139896965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84379961019287662093264643 126569941528931493139896965)
  ·
    refine ⟨23731864036674654963730681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126569941528931493139896965 23731864036674654963730681)
    ·
      refine ⟨17798898027505991222798011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23731864036674654963730681 17798898027505991222798011)
      ·
        refine ⟨26698347041258986834197017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17798898027505991222798011 26698347041258986834197017)
        ·
          refine ⟨20023760280944240125647763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26698347041258986834197017 20023760280944240125647763)
          ·
            refine ⟨30035640421416360188471645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20023760280944240125647763 30035640421416360188471645)
            ·
              refine ⟨11263365158031135070676867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30035640421416360188471645 11263365158031135070676867)
              ·
                refine ⟨16895047737046702606015301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11263365158031135070676867 16895047737046702606015301)
                ·
                  refine ⟨3167821450696256738627869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16895047737046702606015301 3167821450696256738627869)
                  ·
                    refine ⟨1187933044011096276985451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3167821450696256738627869 1187933044011096276985451)
                    ·
                      rfl

theorem cell22_3470237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3470237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470237 prefixEnd_3470237 := by exact prefixLift 3470237
  have htrace : WordTrace (prefixWord ++ tailWord_3470237) baseStart_3470237 baseEnd_3470237 := by
    simpa [prefixWord, tailWord_3470237, baseEnd_3470237] using wordTrace_append hprefix tailTrace_3470237
  have hstable : (prefixWord ++ tailWord_3470237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470237).length < 2 ^ (prefixWord ++ tailWord_3470237).sum := by decide
  have hdescent : baseEnd_3470237 < baseStart_3470237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470355 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 5, 5]
def baseStart_3470355 : Nat := 118140960795 + 3470355 * 2 ^ 59
def prefixEnd_3470355 : Nat := 4983230072969 + 3 ^ 40 * 3470355 * 2
def baseEnd_3470355 : Nat := 1187973437822583302535089

theorem tailTrace_3470355 : CollatzResearch.WordTrace tailWord_3470355 prefixEnd_3470355 1187973437822583302535089 := by
  unfold tailWord_3470355
  simp only [CollatzResearch.WordTrace]
  refine ⟨126574245342503999292692519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84382830228335999528461679 126574245342503999292692519)
  ·
    refine ⟨189861368013755998939038779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126574245342503999292692519 189861368013755998939038779)
    ·
      refine ⟨284792052020633998408558169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189861368013755998939038779 284792052020633998408558169)
      ·
        refine ⟨213594039015475498806418627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284792052020633998408558169 213594039015475498806418627)
        ·
          refine ⟨320391058523213248209627941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213594039015475498806418627 320391058523213248209627941)
          ·
            refine ⟨60073323473102484039305239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320391058523213248209627941 60073323473102484039305239)
            ·
              refine ⟨90109985209653726058957859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60073323473102484039305239 90109985209653726058957859)
              ·
                refine ⟨135164977814480589088436789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90109985209653726058957859 135164977814480589088436789)
                ·
                  refine ⟨12671716670107555227040949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135164977814480589088436789 12671716670107555227040949)
                  ·
                    refine ⟨1187973437822583302535089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12671716670107555227040949 1187973437822583302535089)
                    ·
                      rfl

theorem cell22_3470355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_3470355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470355 prefixEnd_3470355 := by exact prefixLift 3470355
  have htrace : WordTrace (prefixWord ++ tailWord_3470355) baseStart_3470355 baseEnd_3470355 := by
    simpa [prefixWord, tailWord_3470355, baseEnd_3470355] using wordTrace_append hprefix tailTrace_3470355
  have hstable : (prefixWord ++ tailWord_3470355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470355).length < 2 ^ (prefixWord ++ tailWord_3470355).sum := by decide
  have hdescent : baseEnd_3470355 < baseStart_3470355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470522 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_3470522 : Nat := 118140960795 + 3470522 * 2 ^ 59
def prefixEnd_3470522 : Nat := 4983230072969 + 3 ^ 40 * 3470522 * 2
def baseEnd_3470522 : Nat := 1188030605335450533609577

theorem tailTrace_3470522 : CollatzResearch.WordTrace tailWord_3470522 prefixEnd_3470522 1188030605335450533609577 := by
  unfold tailWord_3470522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31645084083224746703505455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84386890888599324542681213 31645084083224746703505455)
  ·
    refine ⟨47467626124837120055258183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31645084083224746703505455 47467626124837120055258183)
    ·
      refine ⟨71201439187255680082887275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47467626124837120055258183 71201439187255680082887275)
      ·
        refine ⟨106802158780883520124330913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71201439187255680082887275 106802158780883520124330913)
        ·
          refine ⟨80101619085662640093248185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106802158780883520124330913 80101619085662640093248185)
          ·
            refine ⟨60076214314246980069936139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80101619085662640093248185 60076214314246980069936139)
            ·
              refine ⟨90114321471370470104904209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60076214314246980069936139 90114321471370470104904209)
              ·
                refine ⟨67585741103527852578678157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90114321471370470104904209 67585741103527852578678157)
                ·
                  refine ⟨25344652913822944717004309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67585741103527852578678157 25344652913822944717004309)
                  ·
                    refine ⟨1188030605335450533609577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25344652913822944717004309 1188030605335450533609577)
                    ·
                      rfl

theorem cell22_3470522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_3470522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470522 prefixEnd_3470522 := by exact prefixLift 3470522
  have htrace : WordTrace (prefixWord ++ tailWord_3470522) baseStart_3470522 baseEnd_3470522 := by
    simpa [prefixWord, tailWord_3470522, baseEnd_3470522] using wordTrace_append hprefix tailTrace_3470522
  have hstable : (prefixWord ++ tailWord_3470522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470522).length < 2 ^ (prefixWord ++ tailWord_3470522).sum := by decide
  have hdescent : baseEnd_3470522 < baseStart_3470522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470575 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 2, 3]
def baseStart_3470575 : Nat := 118140960795 + 3470575 * 2 ^ 59
def prefixEnd_3470575 : Nat := 4983230072969 + 3 ^ 40 * 3470575 * 2
def baseEnd_3470575 : Nat := 1188048748318576062034415

theorem tailTrace_3470575 : CollatzResearch.WordTrace tailWord_3470575 prefixEnd_3470575 1188048748318576062034415 := by
  unfold tailWord_3470575
  simp only [CollatzResearch.WordTrace]
  refine ⟨126582269401706976865701179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84388179601137984577134119 126582269401706976865701179)
  ·
    refine ⟨189873404102560465298551769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126582269401706976865701179 189873404102560465298551769)
    ·
      refine ⟨142405053076920348973913827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189873404102560465298551769 142405053076920348973913827)
      ·
        refine ⟨213607579615380523460870741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142405053076920348973913827 213607579615380523460870741)
        ·
          refine ⟨2503213823617740509307079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 213607579615380523460870741 2503213823617740509307079)
          ·
            refine ⟨3754820735426610763960619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503213823617740509307079 3754820735426610763960619)
            ·
              refine ⟨5632231103139916145940929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754820735426610763960619 5632231103139916145940929)
              ·
                refine ⟨4224173327354937109455697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5632231103139916145940929 4224173327354937109455697)
                ·
                  refine ⟨3168129995516202832091773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224173327354937109455697 3168129995516202832091773)
                  ·
                    refine ⟨1188048748318576062034415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168129995516202832091773 1188048748318576062034415)
                    ·
                      rfl

theorem cell22_3470575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_3470575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470575 prefixEnd_3470575 := by exact prefixLift 3470575
  have htrace : WordTrace (prefixWord ++ tailWord_3470575) baseStart_3470575 baseEnd_3470575 := by
    simpa [prefixWord, tailWord_3470575, baseEnd_3470575] using wordTrace_append hprefix tailTrace_3470575
  have hstable : (prefixWord ++ tailWord_3470575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470575).length < 2 ^ (prefixWord ++ tailWord_3470575).sum := by decide
  have hdescent : baseEnd_3470575 < baseStart_3470575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470586 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 3, 3]
def baseStart_3470586 : Nat := 118140960795 + 3470586 * 2 ^ 59
def prefixEnd_3470586 : Nat := 4983230072969 + 3 ^ 40 * 3470586 * 2
def baseEnd_3470586 : Nat := 1188052513843375700009381

theorem tailTrace_3470586 : CollatzResearch.WordTrace tailWord_3470586 prefixEnd_3470586 1188052513843375700009381 := by
  unfold tailWord_3470586
  simp only [CollatzResearch.WordTrace]
  refine ⟨31645667651166781436087903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84388447069778083829567741 31645667651166781436087903)
  ·
    refine ⟨47468501476750172154131855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31645667651166781436087903 47468501476750172154131855)
    ·
      refine ⟨71202752215125258231197783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47468501476750172154131855 71202752215125258231197783)
      ·
        refine ⟨106804128322687887346796675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71202752215125258231197783 106804128322687887346796675)
        ·
          refine ⟨160206192484031831020195013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106804128322687887346796675 160206192484031831020195013)
          ·
            refine ⟨30038661090755968316286565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160206192484031831020195013 30038661090755968316286565)
            ·
              refine ⟨5632248954516744059303731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30038661090755968316286565 5632248954516744059303731)
              ·
                refine ⟨8448373431775116088955597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632248954516744059303731 8448373431775116088955597)
                ·
                  refine ⟨3168140036915668533358349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8448373431775116088955597 3168140036915668533358349)
                  ·
                    refine ⟨1188052513843375700009381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168140036915668533358349 1188052513843375700009381)
                    ·
                      rfl

theorem cell22_3470586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_3470586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470586 prefixEnd_3470586 := by exact prefixLift 3470586
  have htrace : WordTrace (prefixWord ++ tailWord_3470586) baseStart_3470586 baseEnd_3470586 := by
    simpa [prefixWord, tailWord_3470586, baseEnd_3470586] using wordTrace_append hprefix tailTrace_3470586
  have hstable : (prefixWord ++ tailWord_3470586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470586).length < 2 ^ (prefixWord ++ tailWord_3470586).sum := by decide
  have hdescent : baseEnd_3470586 < baseStart_3470586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470659 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 1, 5]
def baseStart_3470659 : Nat := 118140960795 + 3470659 * 2 ^ 59
def prefixEnd_3470659 : Nat := 4983230072969 + 3 ^ 40 * 3470659 * 2
def baseEnd_3470659 : Nat := 1188077503235227842934157

theorem tailTrace_3470659 : CollatzResearch.WordTrace tailWord_3470659 prefixEnd_3470659 1188077503235227842934157 := by
  unfold tailWord_3470659
  simp only [CollatzResearch.WordTrace]
  refine ⟨126585333133402659211759031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84390222088935106141172687 126585333133402659211759031)
  ·
    refine ⟨189877999700103988817638547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126585333133402659211759031 189877999700103988817638547)
    ·
      refine ⟨284816999550155983226457821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189877999700103988817638547 284816999550155983226457821)
      ·
        refine ⟨106806374831308493709921683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284816999550155983226457821 106806374831308493709921683)
        ·
          refine ⟨160209562246962740564882525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106806374831308493709921683 160209562246962740564882525)
          ·
            refine ⟨60078585842611027711830947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160209562246962740564882525 60078585842611027711830947)
            ·
              refine ⟨90117878763916541567746421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60078585842611027711830947 90117878763916541567746421)
              ·
                refine ⟨8448551134117175771976227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90117878763916541567746421 8448551134117175771976227)
                ·
                  refine ⟨12672826701175763657964341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8448551134117175771976227 12672826701175763657964341)
                  ·
                    refine ⟨1188077503235227842934157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12672826701175763657964341 1188077503235227842934157)
                    ·
                      rfl

theorem cell22_3470659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_3470659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470659 prefixEnd_3470659 := by exact prefixLift 3470659
  have htrace : WordTrace (prefixWord ++ tailWord_3470659) baseStart_3470659 baseEnd_3470659 := by
    simpa [prefixWord, tailWord_3470659, baseEnd_3470659] using wordTrace_append hprefix tailTrace_3470659
  have hstable : (prefixWord ++ tailWord_3470659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470659).length < 2 ^ (prefixWord ++ tailWord_3470659).sum := by decide
  have hdescent : baseEnd_3470659 < baseStart_3470659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470663 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 1, 4]
def baseStart_3470663 : Nat := 118140960795 + 3470663 * 2 ^ 59
def prefixEnd_3470663 : Nat := 4983230072969 + 3 ^ 40 * 3470663 * 2
def baseEnd_3470663 : Nat := 1188078872516973165834145

theorem tailTrace_3470663 : CollatzResearch.WordTrace tailWord_3470663 prefixEnd_3470663 1188078872516973165834145 := by
  unfold tailWord_3470663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126585479025388167894904643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84390319350258778596603095 126585479025388167894904643)
  ·
    refine ⟨189878218538082251842356965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126585479025388167894904643 189878218538082251842356965)
    ·
      refine ⟨35602165975890422220441931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189878218538082251842356965 35602165975890422220441931)
      ·
        refine ⟨53403248963835633330662897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35602165975890422220441931 53403248963835633330662897)
        ·
          refine ⟨40052436722876724997997173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53403248963835633330662897 40052436722876724997997173)
          ·
            refine ⟨3754915942769692968562235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40052436722876724997997173 3754915942769692968562235)
            ·
              refine ⟨5632373914154539452843353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754915942769692968562235 5632373914154539452843353)
              ·
                refine ⟨4224280435615904589632515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5632373914154539452843353 4224280435615904589632515)
                ·
                  refine ⟨6336420653423856884448773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224280435615904589632515 6336420653423856884448773)
                  ·
                    refine ⟨1188078872516973165834145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6336420653423856884448773 1188078872516973165834145)
                    ·
                      rfl

theorem cell22_3470663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_3470663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470663 prefixEnd_3470663 := by exact prefixLift 3470663
  have htrace : WordTrace (prefixWord ++ tailWord_3470663) baseStart_3470663 baseEnd_3470663 := by
    simpa [prefixWord, tailWord_3470663, baseEnd_3470663] using wordTrace_append hprefix tailTrace_3470663
  have hstable : (prefixWord ++ tailWord_3470663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470663).length < 2 ^ (prefixWord ++ tailWord_3470663).sum := by decide
  have hdescent : baseEnd_3470663 < baseStart_3470663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470676 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3470676 : Nat := 118140960795 + 3470676 * 2 ^ 59
def prefixEnd_3470676 : Nat := 4983230072969 + 3 ^ 40 * 3470676 * 2
def baseEnd_3470676 : Nat := 1188083322682645465259105

theorem tailTrace_3470676 : CollatzResearch.WordTrace tailWord_3470676 prefixEnd_3470676 1188083322682645465259105 := by
  unfold tailWord_3470676
  simp only [CollatzResearch.WordTrace]
  refine ⟨63292976587170535557563941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84390635449560714076751921 63292976587170535557563941)
  ·
    refine ⟨11867433110094475417043239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63292976587170535557563941 11867433110094475417043239)
    ·
      refine ⟨17801149665141713125564859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11867433110094475417043239 17801149665141713125564859)
      ·
        refine ⟨26701724497712569688347289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17801149665141713125564859 26701724497712569688347289)
        ·
          refine ⟨20026293373284427266260467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26701724497712569688347289 20026293373284427266260467)
          ·
            refine ⟨30039440059926640899390701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20026293373284427266260467 30039440059926640899390701)
            ·
              refine ⟨11264790022472490337271513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30039440059926640899390701 11264790022472490337271513)
              ·
                refine ⟨8448592516854367752953635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11264790022472490337271513 8448592516854367752953635)
                ·
                  refine ⟨12672888775281551629430453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8448592516854367752953635 12672888775281551629430453)
                  ·
                    refine ⟨1188083322682645465259105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12672888775281551629430453 1188083322682645465259105)
                    ·
                      rfl

theorem cell22_3470676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3470676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470676 prefixEnd_3470676 := by exact prefixLift 3470676
  have htrace : WordTrace (prefixWord ++ tailWord_3470676) baseStart_3470676 baseEnd_3470676 := by
    simpa [prefixWord, tailWord_3470676, baseEnd_3470676] using wordTrace_append hprefix tailTrace_3470676
  have hstable : (prefixWord ++ tailWord_3470676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470676).length < 2 ^ (prefixWord ++ tailWord_3470676).sum := by decide
  have hdescent : baseEnd_3470676 < baseStart_3470676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470691 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 2, 4]
def baseStart_3470691 : Nat := 118140960795 + 3470691 * 2 ^ 59
def prefixEnd_3470691 : Nat := 4983230072969 + 3 ^ 40 * 3470691 * 2
def baseEnd_3470691 : Nat := 1188088457489190426134059

theorem tailTrace_3470691 : CollatzResearch.WordTrace tailWord_3470691 prefixEnd_3470691 1188088457489190426134059 := by
  unfold tailWord_3470691
  simp only [CollatzResearch.WordTrace]
  refine ⟨126586500269286728676923927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84391000179524485784615951 126586500269286728676923927)
  ·
    refine ⟨189879750403930093015385891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126586500269286728676923927 189879750403930093015385891)
    ·
      refine ⟨284819625605895139523078837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189879750403930093015385891 284819625605895139523078837)
      ·
        refine ⟨26701839900552669330288641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284819625605895139523078837 26701839900552669330288641)
        ·
          refine ⟨20026379925414501997716481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26701839900552669330288641 20026379925414501997716481)
          ·
            refine ⟨15019784944060876498287361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20026379925414501997716481 15019784944060876498287361)
            ·
              refine ⟨11264838708045657373715521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15019784944060876498287361 11264838708045657373715521)
              ·
                refine ⟨8448629031034243030286641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11264838708045657373715521 8448629031034243030286641)
                ·
                  refine ⟨6336471773275682272714981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8448629031034243030286641 6336471773275682272714981)
                  ·
                    refine ⟨1188088457489190426134059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6336471773275682272714981 1188088457489190426134059)
                    ·
                      rfl

theorem cell22_3470691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_3470691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470691 prefixEnd_3470691 := by exact prefixLift 3470691
  have htrace : WordTrace (prefixWord ++ tailWord_3470691) baseStart_3470691 baseEnd_3470691 := by
    simpa [prefixWord, tailWord_3470691, baseEnd_3470691] using wordTrace_append hprefix tailTrace_3470691
  have hstable : (prefixWord ++ tailWord_3470691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470691).length < 2 ^ (prefixWord ++ tailWord_3470691).sum := by decide
  have hdescent : baseEnd_3470691 < baseStart_3470691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470693 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_3470693 : Nat := 118140960795 + 3470693 * 2 ^ 59
def prefixEnd_3470693 : Nat := 4983230072969 + 3 ^ 40 * 3470693 * 2
def baseEnd_3470693 : Nat := 1188089142130063087584053

theorem tailTrace_3470693 : CollatzResearch.WordTrace tailWord_3470693 prefixEnd_3470693 1188089142130063087584053 := by
  unfold tailWord_3470693
  simp only [CollatzResearch.WordTrace]
  refine ⟨126586573215279483018496733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84391048810186322012331155 126586573215279483018496733)
  ·
    refine ⟨47469964955729806131936275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126586573215279483018496733 47469964955729806131936275)
    ·
      refine ⟨71204947433594709197904413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47469964955729806131936275 71204947433594709197904413)
      ·
        refine ⟨26701855287598015949214155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71204947433594709197904413 26701855287598015949214155)
        ·
          refine ⟨40052782931397023923821233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26701855287598015949214155 40052782931397023923821233)
          ·
            refine ⟨30039587198547767942865925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40052782931397023923821233 30039587198547767942865925)
            ·
              refine ⟨5632422599727706489287361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30039587198547767942865925 5632422599727706489287361)
              ·
                refine ⟨4224316949795779866965521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5632422599727706489287361 4224316949795779866965521)
                ·
                  refine ⟨3168237712346834900224141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224316949795779866965521 3168237712346834900224141)
                  ·
                    refine ⟨1188089142130063087584053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168237712346834900224141 1188089142130063087584053)
                    ·
                      rfl

theorem cell22_3470693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_3470693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470693 prefixEnd_3470693 := by exact prefixLift 3470693
  have htrace : WordTrace (prefixWord ++ tailWord_3470693) baseStart_3470693 baseEnd_3470693 := by
    simpa [prefixWord, tailWord_3470693, baseEnd_3470693] using wordTrace_append hprefix tailTrace_3470693
  have hstable : (prefixWord ++ tailWord_3470693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470693).length < 2 ^ (prefixWord ++ tailWord_3470693).sum := by decide
  have hdescent : baseEnd_3470693 < baseStart_3470693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470751 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 7]
def baseStart_3470751 : Nat := 118140960795 + 3470751 * 2 ^ 59
def prefixEnd_3470751 : Nat := 4983230072969 + 3 ^ 40 * 3470751 * 2
def baseEnd_3470751 : Nat := 396036332238456756544625

theorem tailTrace_3470751 : CollatzResearch.WordTrace tailWord_3470751 prefixEnd_3470751 396036332238456756544625 := by
  unfold tailWord_3470751
  simp only [CollatzResearch.WordTrace]
  refine ⟨126588688649069358924108107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84392459099379572616072071 126588688649069358924108107)
  ·
    refine ⟨189883032973604038386162161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126588688649069358924108107 189883032973604038386162161)
    ·
      refine ⟨142412274730203028789621621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189883032973604038386162161 142412274730203028789621621)
      ·
        refine ⟨13351150755956533949027027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142412274730203028789621621 13351150755956533949027027)
        ·
          refine ⟨20026726133934800923540541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13351150755956533949027027 20026726133934800923540541)
          ·
            refine ⟨7510022300225550346327703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20026726133934800923540541 7510022300225550346327703)
            ·
              refine ⟨11265033450338325519491555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510022300225550346327703 11265033450338325519491555)
              ·
                refine ⟨16897550175507488279237333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11265033450338325519491555 16897550175507488279237333)
                ·
                  refine ⟨396036332238456756544625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16897550175507488279237333 396036332238456756544625)
                  ·
                    rfl

theorem cell22_3470751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 7].length) (baseStart_3470751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470751 prefixEnd_3470751 := by exact prefixLift 3470751
  have htrace : WordTrace (prefixWord ++ tailWord_3470751) baseStart_3470751 baseEnd_3470751 := by
    simpa [prefixWord, tailWord_3470751, baseEnd_3470751] using wordTrace_append hprefix tailTrace_3470751
  have hstable : (prefixWord ++ tailWord_3470751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470751).length < 2 ^ (prefixWord ++ tailWord_3470751).sum := by decide
  have hdescent : baseEnd_3470751 < baseStart_3470751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470798 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_3470798 : Nat := 118140960795 + 3470798 * 2 ^ 59
def prefixEnd_3470798 : Nat := 4983230072969 + 3 ^ 40 * 3470798 * 2
def baseEnd_3470798 : Nat := 1188125085775877813708731

theorem tailTrace_3470798 : CollatzResearch.WordTrace tailWord_3470798 prefixEnd_3470798 1188125085775877813708731 := by
  unfold tailWord_3470798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823800359987385743883631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84393601919932723967379365 15823800359987385743883631)
  ·
    refine ⟨23735700539981078615825447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15823800359987385743883631 23735700539981078615825447)
    ·
      refine ⟨35603550809971617923738171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23735700539981078615825447 35603550809971617923738171)
      ·
        refine ⟨53405326214957426885607257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35603550809971617923738171 53405326214957426885607257)
        ·
          refine ⟨40053994661218070164205443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53405326214957426885607257 40053994661218070164205443)
          ·
            refine ⟨60080991991827105246308165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40053994661218070164205443 60080991991827105246308165)
            ·
              refine ⟨11265185998467582233682781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60080991991827105246308165 11265185998467582233682781)
              ·
                refine ⟨4224444749425343337631043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11265185998467582233682781 4224444749425343337631043)
                ·
                  refine ⟨6336667124138015006446565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224444749425343337631043 6336667124138015006446565)
                  ·
                    refine ⟨1188125085775877813708731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6336667124138015006446565 1188125085775877813708731)
                    ·
                      rfl

theorem cell22_3470798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_3470798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470798 prefixEnd_3470798 := by exact prefixLift 3470798
  have htrace : WordTrace (prefixWord ++ tailWord_3470798) baseStart_3470798 baseEnd_3470798 := by
    simpa [prefixWord, tailWord_3470798, baseEnd_3470798] using wordTrace_append hprefix tailTrace_3470798
  have hstable : (prefixWord ++ tailWord_3470798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470798).length < 2 ^ (prefixWord ++ tailWord_3470798).sum := by decide
  have hdescent : baseEnd_3470798 < baseStart_3470798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470813 : List Nat := [1, 4, 3, 1, 1, 2, 3, 1, 6]
def baseStart_3470813 : Nat := 118140960795 + 3470813 * 2 ^ 59
def prefixEnd_3470813 : Nat := 4983230072969 + 3 ^ 40 * 3470813 * 2
def baseEnd_3470813 : Nat := 396043406860807591527895

theorem tailTrace_3470813 : CollatzResearch.WordTrace tailWord_3470813 prefixEnd_3470813 396043406860807591527895 := by
  unfold tailWord_3470813
  simp only [CollatzResearch.WordTrace]
  refine ⟨126590949974844743512865093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84393966649896495675243395 126590949974844743512865093)
  ·
    refine ⟨23735803120283389408662205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126590949974844743512865093 23735803120283389408662205)
    ·
      refine ⟨8900926170106271028248327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23735803120283389408662205 8900926170106271028248327)
      ·
        refine ⟨13351389255159406542372491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8900926170106271028248327 13351389255159406542372491)
        ·
          refine ⟨20027083882739109813558737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13351389255159406542372491 20027083882739109813558737)
          ·
            refine ⟨15020312912054332360169053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20027083882739109813558737 15020312912054332360169053)
            ·
              refine ⟨5632617342020374635063395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15020312912054332360169053 5632617342020374635063395)
              ·
                refine ⟨8448926013030561952595093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5632617342020374635063395 8448926013030561952595093)
                ·
                  refine ⟨396043406860807591527895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8448926013030561952595093 396043406860807591527895)
                  ·
                    rfl

theorem cell22_3470813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_3470813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470813 prefixEnd_3470813 := by exact prefixLift 3470813
  have htrace : WordTrace (prefixWord ++ tailWord_3470813) baseStart_3470813 baseEnd_3470813 := by
    simpa [prefixWord, tailWord_3470813, baseEnd_3470813] using wordTrace_append hprefix tailTrace_3470813
  have hstable : (prefixWord ++ tailWord_3470813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470813).length < 2 ^ (prefixWord ++ tailWord_3470813).sum := by decide
  have hdescent : baseEnd_3470813 < baseStart_3470813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470862 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_3470862 : Nat := 118140960795 + 3470862 * 2 ^ 59
def prefixEnd_3470862 : Nat := 4983230072969 + 3 ^ 40 * 3470862 * 2
def baseEnd_3470862 : Nat := 1188146994283802980108535

theorem tailTrace_3470862 : CollatzResearch.WordTrace tailWord_3470862 prefixEnd_3470862 1188146994283802980108535 := by
  unfold tailWord_3470862
  simp only [CollatzResearch.WordTrace]
  refine ⟨15824092143958403110174855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84395158101111483254265893 15824092143958403110174855)
  ·
    refine ⟨23736138215937604665262283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15824092143958403110174855 23736138215937604665262283)
    ·
      refine ⟨35604207323906406997893425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23736138215937604665262283 35604207323906406997893425)
      ·
        refine ⟨26703155492929805248420069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35604207323906406997893425 26703155492929805248420069)
        ·
          refine ⟨5006841654924338484078763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26703155492929805248420069 5006841654924338484078763)
          ·
            refine ⟨7510262482386507726118145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5006841654924338484078763 7510262482386507726118145)
            ·
              refine ⟨5632696861789880794588609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7510262482386507726118145 5632696861789880794588609)
              ·
                refine ⟨4224522646342410595941457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5632696861789880794588609 4224522646342410595941457)
                ·
                  refine ⟨3168391984756807946956093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224522646342410595941457 3168391984756807946956093)
                  ·
                    refine ⟨1188146994283802980108535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168391984756807946956093 1188146994283802980108535)
                    ·
                      rfl

theorem cell22_3470862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_3470862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470862 prefixEnd_3470862 := by exact prefixLift 3470862
  have htrace : WordTrace (prefixWord ++ tailWord_3470862) baseStart_3470862 baseEnd_3470862 := by
    simpa [prefixWord, tailWord_3470862, baseEnd_3470862] using wordTrace_append hprefix tailTrace_3470862
  have hstable : (prefixWord ++ tailWord_3470862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470862).length < 2 ^ (prefixWord ++ tailWord_3470862).sum := by decide
  have hdescent : baseEnd_3470862 < baseStart_3470862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470890 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3470890 : Nat := 118140960795 + 3470890 * 2 ^ 59
def prefixEnd_3470890 : Nat := 4983230072969 + 3 ^ 40 * 3470890 * 2
def baseEnd_3470890 : Nat := 1188156579256020240408449

theorem tailTrace_3470890 : CollatzResearch.WordTrace tailWord_3470890 prefixEnd_3470890 1188156579256020240408449 := by
  unfold tailWord_3470890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31648439598891446415854531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84395838930377190442278749 31648439598891446415854531)
  ·
    refine ⟨47472659398337169623781797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31648439598891446415854531 47472659398337169623781797)
    ·
      refine ⟨8901123637188219304459087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47472659398337169623781797 8901123637188219304459087)
      ·
        refine ⟨13351685455782328956688631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8901123637188219304459087 13351685455782328956688631)
        ·
          refine ⟨20027528183673493435032947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13351685455782328956688631 20027528183673493435032947)
          ·
            refine ⟨30041292275510240152549421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20027528183673493435032947 30041292275510240152549421)
            ·
              refine ⟨11265484603316340057206033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30041292275510240152549421 11265484603316340057206033)
              ·
                refine ⟨8449113452487255042904525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11265484603316340057206033 8449113452487255042904525)
                ·
                  refine ⟨3168417544682720641089197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8449113452487255042904525 3168417544682720641089197)
                  ·
                    refine ⟨1188156579256020240408449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168417544682720641089197 1188156579256020240408449)
                    ·
                      rfl

theorem cell22_3470890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3470890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470890 prefixEnd_3470890 := by exact prefixLift 3470890
  have htrace : WordTrace (prefixWord ++ tailWord_3470890) baseStart_3470890 baseEnd_3470890 := by
    simpa [prefixWord, tailWord_3470890, baseEnd_3470890] using wordTrace_append hprefix tailTrace_3470890
  have hstable : (prefixWord ++ tailWord_3470890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470890).length < 2 ^ (prefixWord ++ tailWord_3470890).sum := by decide
  have hdescent : baseEnd_3470890 < baseStart_3470890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3470948 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 6]
def baseStart_3470948 : Nat := 118140960795 + 3470948 * 2 ^ 59
def prefixEnd_3470948 : Nat := 4983230072969 + 3 ^ 40 * 3470948 * 2
def baseEnd_3470948 : Nat := 396058811280442474152757

theorem tailTrace_3470948 : CollatzResearch.WordTrace tailWord_3470948 prefixEnd_3470948 396058811280442474152757 := by
  unfold tailWord_3470948
  simp only [CollatzResearch.WordTrace]
  refine ⟨63297936914677830784514749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84397249219570441046019665 63297936914677830784514749)
  ·
    refine ⟨23736726343004186544193031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63297936914677830784514749 23736726343004186544193031)
    ·
      refine ⟨35605089514506279816289547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23736726343004186544193031 35605089514506279816289547)
      ·
        refine ⟨53407634271759419724434321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35605089514506279816289547 53407634271759419724434321)
        ·
          refine ⟨40055725703819564793325741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53407634271759419724434321 40055725703819564793325741)
          ·
            refine ⟨15020897138932336797497153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40055725703819564793325741 15020897138932336797497153)
            ·
              refine ⟨11265672854199252598122865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15020897138932336797497153 11265672854199252598122865)
              ·
                refine ⟨8449254640649439448592149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11265672854199252598122865 8449254640649439448592149)
                ·
                  refine ⟨396058811280442474152757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8449254640649439448592149 396058811280442474152757)
                  ·
                    rfl

theorem cell22_3470948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_3470948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3470948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3470948 prefixEnd_3470948 := by exact prefixLift 3470948
  have htrace : WordTrace (prefixWord ++ tailWord_3470948) baseStart_3470948 baseEnd_3470948 := by
    simpa [prefixWord, tailWord_3470948, baseEnd_3470948] using wordTrace_append hprefix tailTrace_3470948
  have hstable : (prefixWord ++ tailWord_3470948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3470948).length < 2 ^ (prefixWord ++ tailWord_3470948).sum := by decide
  have hdescent : baseEnd_3470948 < baseStart_3470948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3470948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471100 : List Nat := [2, 2, 2, 1, 3, 1, 4, 1, 6]
def baseStart_3471100 : Nat := 118140960795 + 3471100 * 2 ^ 59
def prefixEnd_3471100 : Nat := 4983230072969 + 3 ^ 40 * 3471100 * 2
def baseEnd_3471100 : Nat := 396076155515883230885935

theorem tailTrace_3471100 : CollatzResearch.WordTrace tailWord_3471100 prefixEnd_3471100 396076155515883230885935 := by
  unfold tailWord_3471100
  simp only [CollatzResearch.WordTrace]
  refine ⟨63300708862402495764281377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84400945149869994352375169 63300708862402495764281377)
  ·
    refine ⟨47475531646801871823211033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63300708862402495764281377 47475531646801871823211033)
    ·
      refine ⟨35606648735101403867408275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47475531646801871823211033 35606648735101403867408275)
      ·
        refine ⟨53409973102652105801112413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35606648735101403867408275 53409973102652105801112413)
        ·
          refine ⟨20028739913494539675417155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53409973102652105801112413 20028739913494539675417155)
          ·
            refine ⟨30043109870241809513125733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20028739913494539675417155 30043109870241809513125733)
            ·
              refine ⟨5633083100670339283711075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30043109870241809513125733 5633083100670339283711075)
              ·
                refine ⟨8449624651005508925566613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633083100670339283711075 8449624651005508925566613)
                ·
                  refine ⟨396076155515883230885935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8449624651005508925566613 396076155515883230885935)
                  ·
                    rfl

theorem cell22_3471100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_3471100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471100 prefixEnd_3471100 := by exact prefixLift 3471100
  have htrace : WordTrace (prefixWord ++ tailWord_3471100) baseStart_3471100 baseEnd_3471100 := by
    simpa [prefixWord, tailWord_3471100, baseEnd_3471100] using wordTrace_append hprefix tailTrace_3471100
  have hstable : (prefixWord ++ tailWord_3471100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471100).length < 2 ^ (prefixWord ++ tailWord_3471100).sum := by decide
  have hdescent : baseEnd_3471100 < baseStart_3471100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471115 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 1, 5]
def baseStart_3471115 : Nat := 118140960795 + 3471115 * 2 ^ 59
def prefixEnd_3471115 : Nat := 4983230072969 + 3 ^ 40 * 3471115 * 2
def baseEnd_3471115 : Nat := 1188233601354194653532759

theorem tailTrace_3471115 : CollatzResearch.WordTrace tailWord_3471115 prefixEnd_3471115 1188233601354194653532759 := by
  unfold tailWord_3471115
  simp only [CollatzResearch.WordTrace]
  refine ⟨126601964819750649090358799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84401309879833766060239199 126601964819750649090358799)
  ·
    refine ⟨189902947229625973635538199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126601964819750649090358799 189902947229625973635538199)
    ·
      refine ⟨284854420844438960453307299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189902947229625973635538199 284854420844438960453307299)
      ·
        refine ⟨427281631266658440679960949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284854420844438960453307299 427281631266658440679960949)
        ·
          refine ⟨40057652931249228813746339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 427281631266658440679960949 40057652931249228813746339)
          ·
            refine ⟨60086479396873843220619509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40057652931249228813746339 60086479396873843220619509)
            ·
              refine ⟨5633107443456922801933079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60086479396873843220619509 5633107443456922801933079)
              ·
                refine ⟨8449661165185384202899619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633107443456922801933079 8449661165185384202899619)
                ·
                  refine ⟨12674491747778076304349429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8449661165185384202899619 12674491747778076304349429)
                  ·
                    refine ⟨1188233601354194653532759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12674491747778076304349429 1188233601354194653532759)
                    ·
                      rfl

theorem cell22_3471115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5].length) (baseStart_3471115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471115 prefixEnd_3471115 := by exact prefixLift 3471115
  have htrace : WordTrace (prefixWord ++ tailWord_3471115) baseStart_3471115 baseEnd_3471115 := by
    simpa [prefixWord, tailWord_3471115, baseEnd_3471115] using wordTrace_append hprefix tailTrace_3471115
  have hstable : (prefixWord ++ tailWord_3471115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471115).length < 2 ^ (prefixWord ++ tailWord_3471115).sum := by decide
  have hdescent : baseEnd_3471115 < baseStart_3471115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471130 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_3471130 : Nat := 118140960795 + 3471130 * 2 ^ 59
def prefixEnd_3471130 : Nat := 4983230072969 + 3 ^ 40 * 3471130 * 2
def baseEnd_3471130 : Nat := 1188238736160739614407713

theorem tailTrace_3471130 : CollatzResearch.WordTrace tailWord_3471130 prefixEnd_3471130 1188238736160739614407713 := by
  unfold tailWord_3471130
  simp only [CollatzResearch.WordTrace]
  refine ⟨31650627978674076663038711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84401674609797537768103229 31650627978674076663038711)
  ·
    refine ⟨47475941968011114994558067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31650627978674076663038711 47475941968011114994558067)
    ·
      refine ⟨71213912952016672491837101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47475941968011114994558067 71213912952016672491837101)
      ·
        refine ⟨26705217357006252184438913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71213912952016672491837101 26705217357006252184438913)
        ·
          refine ⟨20028913017754689138329185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26705217357006252184438913 20028913017754689138329185)
          ·
            refine ⟨15021684763316016853746889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20028913017754689138329185 15021684763316016853746889)
            ·
              refine ⟨11266263572487012640310167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15021684763316016853746889 11266263572487012640310167)
              ·
                refine ⟨16899395358730518960465251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11266263572487012640310167 16899395358730518960465251)
                ·
                  refine ⟨25349093038095778440697877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16899395358730518960465251 25349093038095778440697877)
                  ·
                    refine ⟨1188238736160739614407713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25349093038095778440697877 1188238736160739614407713)
                    ·
                      rfl

theorem cell22_3471130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_3471130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471130 prefixEnd_3471130 := by exact prefixLift 3471130
  have htrace : WordTrace (prefixWord ++ tailWord_3471130) baseStart_3471130 baseEnd_3471130 := by
    simpa [prefixWord, tailWord_3471130, baseEnd_3471130] using wordTrace_append hprefix tailTrace_3471130
  have hstable : (prefixWord ++ tailWord_3471130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471130).length < 2 ^ (prefixWord ++ tailWord_3471130).sum := by decide
  have hdescent : baseEnd_3471130 < baseStart_3471130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471166 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_3471166 : Nat := 118140960795 + 3471166 * 2 ^ 59
def prefixEnd_3471166 : Nat := 4983230072969 + 3 ^ 40 * 3471166 * 2
def baseEnd_3471166 : Nat := 1188251059696447520507603

theorem tailTrace_3471166 : CollatzResearch.WordTrace tailWord_3471166 prefixEnd_3471166 1188251059696447520507603 := by
  unfold tailWord_3471166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825478117820735600058169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84402549961710589866976901 15825478117820735600058169)
  ·
    refine ⟨11869108588365551700043627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15825478117820735600058169 11869108588365551700043627)
    ·
      refine ⟨17803662882548327550065441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11869108588365551700043627 17803662882548327550065441)
      ·
        refine ⟨13352747161911245662549081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17803662882548327550065441 13352747161911245662549081)
        ·
          refine ⟨10014560371433434246911811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13352747161911245662549081 10014560371433434246911811)
          ·
            refine ⟨15021840557150151370367717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10014560371433434246911811 15021840557150151370367717)
            ·
              refine ⟨2816595104465653381943947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15021840557150151370367717 2816595104465653381943947)
              ·
                refine ⟨4224892656698480072915921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816595104465653381943947 4224892656698480072915921)
                ·
                  refine ⟨3168669492523860054686941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4224892656698480072915921 3168669492523860054686941)
                  ·
                    refine ⟨1188251059696447520507603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168669492523860054686941 1188251059696447520507603)
                    ·
                      rfl

theorem cell22_3471166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_3471166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471166 prefixEnd_3471166 := by exact prefixLift 3471166
  have htrace : WordTrace (prefixWord ++ tailWord_3471166) baseStart_3471166 baseEnd_3471166 := by
    simpa [prefixWord, tailWord_3471166, baseEnd_3471166] using wordTrace_append hprefix tailTrace_3471166
  have hstable : (prefixWord ++ tailWord_3471166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471166).length < 2 ^ (prefixWord ++ tailWord_3471166).sum := by decide
  have hdescent : baseEnd_3471166 < baseStart_3471166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471194 : List Nat := [3, 1, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_3471194 : Nat := 118140960795 + 3471194 * 2 ^ 59
def prefixEnd_3471194 : Nat := 4983230072969 + 3 ^ 40 * 3471194 * 2
def baseEnd_3471194 : Nat := 1188260644668664780807517

theorem tailTrace_3471194 : CollatzResearch.WordTrace tailWord_3471194 prefixEnd_3471194 1188260644668664780807517 := by
  unfold tailWord_3471194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31651211546616111395621159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84403230790976297054989757 31651211546616111395621159)
  ·
    refine ⟨47476817319924167093431739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31651211546616111395621159 47476817319924167093431739)
    ·
      refine ⟨71215225979886250640147609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47476817319924167093431739 71215225979886250640147609)
      ·
        refine ⟨53411419484914687980110707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71215225979886250640147609 53411419484914687980110707)
        ·
          refine ⟨80117129227372031970166061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53411419484914687980110707 80117129227372031970166061)
          ·
            refine ⟨30043923460264511988812273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80117129227372031970166061 30043923460264511988812273)
            ·
              refine ⟨22532942595198383991609205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30043923460264511988812273 22532942595198383991609205)
              ·
                refine ⟨2112463368299848499213363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22532942595198383991609205 2112463368299848499213363)
                ·
                  refine ⟨3168695052449772748820045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2112463368299848499213363 3168695052449772748820045)
                  ·
                    refine ⟨1188260644668664780807517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168695052449772748820045 1188260644668664780807517)
                    ·
                      rfl

theorem cell22_3471194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_3471194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471194 prefixEnd_3471194 := by exact prefixLift 3471194
  have htrace : WordTrace (prefixWord ++ tailWord_3471194) baseStart_3471194 baseEnd_3471194 := by
    simpa [prefixWord, tailWord_3471194, baseEnd_3471194] using wordTrace_append hprefix tailTrace_3471194
  have hstable : (prefixWord ++ tailWord_3471194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471194).length < 2 ^ (prefixWord ++ tailWord_3471194).sum := by decide
  have hdescent : baseEnd_3471194 < baseStart_3471194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471205 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3471205 : Nat := 118140960795 + 3471205 * 2 ^ 59
def prefixEnd_3471205 : Nat := 4983230072969 + 3 ^ 40 * 3471205 * 2
def baseEnd_3471205 : Nat := 1188264410193464418782483

theorem tailTrace_3471205 : CollatzResearch.WordTrace tailWord_3471205 prefixEnd_3471205 1188264410193464418782483 := by
  unfold tailWord_3471205
  simp only [CollatzResearch.WordTrace]
  refine ⟨126605247389424594461135069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84403498259616396307423379 126605247389424594461135069)
  ·
    refine ⟨47476967771034222922925651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126605247389424594461135069 47476967771034222922925651)
    ·
      refine ⟨71215451656551334384388477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47476967771034222922925651 71215451656551334384388477)
      ·
        refine ⟨26705794371206750394145679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71215451656551334384388477 26705794371206750394145679)
        ·
          refine ⟨40058691556810125591218519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26705794371206750394145679 40058691556810125591218519)
          ·
            refine ⟨60088037335215188386827779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40058691556810125591218519 60088037335215188386827779)
            ·
              refine ⟨90132056002822782580241669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60088037335215188386827779 90132056002822782580241669)
              ·
                refine ⟨16899760500529271733795313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90132056002822782580241669 16899760500529271733795313)
                ·
                  refine ⟨12674820375396953800346485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16899760500529271733795313 12674820375396953800346485)
                  ·
                    refine ⟨1188264410193464418782483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12674820375396953800346485 1188264410193464418782483)
                    ·
                      rfl

theorem cell22_3471205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3471205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471205 prefixEnd_3471205 := by exact prefixLift 3471205
  have htrace : WordTrace (prefixWord ++ tailWord_3471205) baseStart_3471205 baseEnd_3471205 := by
    simpa [prefixWord, tailWord_3471205, baseEnd_3471205] using wordTrace_append hprefix tailTrace_3471205
  have hstable : (prefixWord ++ tailWord_3471205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471205).length < 2 ^ (prefixWord ++ tailWord_3471205).sum := by decide
  have hdescent : baseEnd_3471205 < baseStart_3471205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471207 : List Nat := [1, 1, 5, 1, 2, 1, 4, 2, 5]
def baseStart_3471207 : Nat := 118140960795 + 3471207 * 2 ^ 59
def prefixEnd_3471207 : Nat := 4983230072969 + 3 ^ 40 * 3471207 * 2
def baseEnd_3471207 : Nat := 396088364944779026744159

theorem tailTrace_3471207 : CollatzResearch.WordTrace tailWord_3471207 prefixEnd_3471207 396088364944779026744159 := by
  unfold tailWord_3471207
  simp only [CollatzResearch.WordTrace]
  refine ⟨126605320335417348802707875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84403546890278232535138583 126605320335417348802707875)
  ·
    refine ⟨189907980503126023204061813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126605320335417348802707875 189907980503126023204061813)
    ·
      refine ⟨17803873172168064675380795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189907980503126023204061813 17803873172168064675380795)
      ·
        refine ⟨26705809758252097013071193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17803873172168064675380795 26705809758252097013071193)
        ·
          refine ⟨20029357318689072759803395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26705809758252097013071193 20029357318689072759803395)
          ·
            refine ⟨30044035978033609139705093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20029357318689072759803395 30044035978033609139705093)
            ·
              refine ⟨5633256745881301713694705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30044035978033609139705093 5633256745881301713694705)
              ·
                refine ⟨4224942559410976285271029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5633256745881301713694705 4224942559410976285271029)
                ·
                  refine ⟨396088364944779026744159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4224942559410976285271029 396088364944779026744159)
                  ·
                    rfl

theorem cell22_3471207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 2, 5].length) (baseStart_3471207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471207 prefixEnd_3471207 := by exact prefixLift 3471207
  have htrace : WordTrace (prefixWord ++ tailWord_3471207) baseStart_3471207 baseEnd_3471207 := by
    simpa [prefixWord, tailWord_3471207, baseEnd_3471207] using wordTrace_append hprefix tailTrace_3471207
  have hstable : (prefixWord ++ tailWord_3471207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471207).length < 2 ^ (prefixWord ++ tailWord_3471207).sum := by decide
  have hdescent : baseEnd_3471207 < baseStart_3471207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471235 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 8]
def baseStart_3471235 : Nat := 118140960795 + 3471235 * 2 ^ 59
def prefixEnd_3471235 : Nat := 4983230072969 + 3 ^ 40 * 3471235 * 2
def baseEnd_3471235 : Nat := 396091559935518113510797

theorem tailTrace_3471235 : CollatzResearch.WordTrace tailWord_3471235 prefixEnd_3471235 396091559935518113510797 := by
  unfold tailWord_3471235
  simp only [CollatzResearch.WordTrace]
  refine ⟨126606341579315909584727159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84404227719543939723151439 126606341579315909584727159)
  ·
    refine ⟨189909512368973864377090739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126606341579315909584727159 189909512368973864377090739)
    ·
      refine ⟨284864268553460796565636109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189909512368973864377090739 284864268553460796565636109)
      ·
        refine ⟨106824100707547798712113541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284864268553460796565636109 106824100707547798712113541)
        ·
          refine ⟨20029518882665212258521289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106824100707547798712113541 20029518882665212258521289)
          ·
            refine ⟨15022139161998909193890967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20029518882665212258521289 15022139161998909193890967)
            ·
              refine ⟨22533208742998363790836451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15022139161998909193890967 22533208742998363790836451)
              ·
                refine ⟨33799813114497545686254677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22533208742998363790836451 33799813114497545686254677)
                ·
                  refine ⟨396091559935518113510797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33799813114497545686254677 396091559935518113510797)
                  ·
                    rfl

theorem cell22_3471235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_3471235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471235 prefixEnd_3471235 := by exact prefixLift 3471235
  have htrace : WordTrace (prefixWord ++ tailWord_3471235) baseStart_3471235 baseEnd_3471235 := by
    simpa [prefixWord, tailWord_3471235, baseEnd_3471235] using wordTrace_append hprefix tailTrace_3471235
  have hstable : (prefixWord ++ tailWord_3471235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471235).length < 2 ^ (prefixWord ++ tailWord_3471235).sum := by decide
  have hdescent : baseEnd_3471235 < baseStart_3471235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471237 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_3471237 : Nat := 118140960795 + 3471237 * 2 ^ 59
def prefixEnd_3471237 : Nat := 4983230072969 + 3 ^ 40 * 3471237 * 2
def baseEnd_3471237 : Nat := 1188275364447427001982385

theorem tailTrace_3471237 : CollatzResearch.WordTrace tailWord_3471237 prefixEnd_3471237 1188275364447427001982385 := by
  unfold tailWord_3471237
  simp only [CollatzResearch.WordTrace]
  refine ⟨126606414525308663926299965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84404276350205775950866643 126606414525308663926299965)
  ·
    refine ⟨47477405446990748972362487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126606414525308663926299965 47477405446990748972362487)
    ·
      refine ⟨71216108170486123458543731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47477405446990748972362487 71216108170486123458543731)
      ·
        refine ⟨106824162255729185187815597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71216108170486123458543731 106824162255729185187815597)
        ·
          refine ⟨40059060845898444445430849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106824162255729185187815597 40059060845898444445430849)
          ·
            refine ⟨30044295634423833334073137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40059060845898444445430849 30044295634423833334073137)
            ·
              refine ⟨22533221725817875000554853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30044295634423833334073137 22533221725817875000554853)
              ·
                refine ⟨4224979073590851562604035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22533221725817875000554853 4224979073590851562604035)
                ·
                  refine ⟨6337468610386277343906053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4224979073590851562604035 6337468610386277343906053)
                  ·
                    refine ⟨1188275364447427001982385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6337468610386277343906053 1188275364447427001982385)
                    ·
                      rfl

theorem cell22_3471237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_3471237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471237 prefixEnd_3471237 := by exact prefixLift 3471237
  have htrace : WordTrace (prefixWord ++ tailWord_3471237) baseStart_3471237 baseEnd_3471237 := by
    simpa [prefixWord, tailWord_3471237, baseEnd_3471237] using wordTrace_append hprefix tailTrace_3471237
  have hstable : (prefixWord ++ tailWord_3471237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471237).length < 2 ^ (prefixWord ++ tailWord_3471237).sum := by decide
  have hdescent : baseEnd_3471237 < baseStart_3471237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471295 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 2, 7]
def baseStart_3471295 : Nat := 118140960795 + 3471295 * 2 ^ 59
def prefixEnd_3471295 : Nat := 4983230072969 + 3 ^ 40 * 3471295 * 2
def baseEnd_3471295 : Nat := 1188295219032734184032207

theorem tailTrace_3471295 : CollatzResearch.WordTrace tailWord_3471295 prefixEnd_3471295 1188295219032734184032207 := by
  unfold tailWord_3471295
  simp only [CollatzResearch.WordTrace]
  refine ⟨126608529959098539831911339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84405686639399026554607559 126608529959098539831911339)
  ·
    refine ⟨189912794938647809747867009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126608529959098539831911339 189912794938647809747867009)
    ·
      refine ⟨142434596203985857310900257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189912794938647809747867009 142434596203985857310900257)
      ·
        refine ⟨106825947152989392983175193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142434596203985857310900257 106825947152989392983175193)
        ·
          refine ⟨80119460364742044737381395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106825947152989392983175193 80119460364742044737381395)
          ·
            refine ⟨120179190547113067106072093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80119460364742044737381395 120179190547113067106072093)
            ·
              refine ⟨45067196455167400164777035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120179190547113067106072093 45067196455167400164777035)
              ·
                refine ⟨67600794682751100247165553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45067196455167400164777035 67600794682751100247165553)
                ·
                  refine ⟨50700596012063325185374165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67600794682751100247165553 50700596012063325185374165)
                  ·
                    refine ⟨1188295219032734184032207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50700596012063325185374165 1188295219032734184032207)
                    ·
                      rfl

theorem cell22_3471295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_3471295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471295 prefixEnd_3471295 := by exact prefixLift 3471295
  have htrace : WordTrace (prefixWord ++ tailWord_3471295) baseStart_3471295 baseEnd_3471295 := by
    simpa [prefixWord, tailWord_3471295, baseEnd_3471295] using wordTrace_append hprefix tailTrace_3471295
  have hstable : (prefixWord ++ tailWord_3471295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471295).length < 2 ^ (prefixWord ++ tailWord_3471295).sum := by decide
  have hdescent : baseEnd_3471295 < baseStart_3471295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471312 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 5, 3]
def baseStart_3471312 : Nat := 118140960795 + 3471312 * 2 ^ 59
def prefixEnd_3471312 : Nat := 4983230072969 + 3 ^ 40 * 3471312 * 2
def baseEnd_3471312 : Nat := 1188301038480151806357155

theorem tailTrace_3471312 : CollatzResearch.WordTrace tailWord_3471312 prefixEnd_3471312 1188301038480151806357155 := by
  unfold tailWord_3471312
  simp only [CollatzResearch.WordTrace]
  refine ⟨63304575000018475867640095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84406100000024634490186793 63304575000018475867640095)
  ·
    refine ⟨94956862500027713801460143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63304575000018475867640095 94956862500027713801460143)
    ·
      refine ⟨142435293750041570702190215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94956862500027713801460143 142435293750041570702190215)
      ·
        refine ⟨213652940625062356053285323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142435293750041570702190215 213652940625062356053285323)
        ·
          refine ⟨320479410937593534079927985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213652940625062356053285323 320479410937593534079927985)
          ·
            refine ⟨240359558203195150559945989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320479410937593534079927985 240359558203195150559945989)
            ·
              refine ⟨45067417163099090729989873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240359558203195150559945989 45067417163099090729989873)
              ·
                refine ⟨33800562872324318047492405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45067417163099090729989873 33800562872324318047492405)
                ·
                  refine ⟨3168802769280404816952413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33800562872324318047492405 3168802769280404816952413)
                  ·
                    refine ⟨1188301038480151806357155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168802769280404816952413 1188301038480151806357155)
                    ·
                      rfl

theorem cell22_3471312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 3].length) (baseStart_3471312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471312 prefixEnd_3471312 := by exact prefixLift 3471312
  have htrace : WordTrace (prefixWord ++ tailWord_3471312) baseStart_3471312 baseEnd_3471312 := by
    simpa [prefixWord, tailWord_3471312, baseEnd_3471312] using wordTrace_append hprefix tailTrace_3471312
  have hstable : (prefixWord ++ tailWord_3471312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471312).length < 2 ^ (prefixWord ++ tailWord_3471312).sum := by decide
  have hdescent : baseEnd_3471312 < baseStart_3471312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471314 : List Nat := [3, 2, 2, 3, 2, 2, 8]
def baseStart_3471314 : Nat := 118140960795 + 3471314 * 2 ^ 59
def prefixEnd_3471314 : Nat := 4983230072969 + 3 ^ 40 * 3471314 * 2
def baseEnd_3471314 : Nat := 44011174930408313622487

theorem tailTrace_3471314 : CollatzResearch.WordTrace tailWord_3471314 prefixEnd_3471314 44011174930408313622487 := by
  unfold tailWord_3471314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31652305736507426519213249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84406148630686470717901997 31652305736507426519213249)
  ·
    refine ⟨23739229302380569889409937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31652305736507426519213249 23739229302380569889409937)
    ·
      refine ⟨17804421976785427417057453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23739229302380569889409937 17804421976785427417057453)
      ·
        refine ⟨6676658241294535281396545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17804421976785427417057453 6676658241294535281396545)
        ·
          refine ⟨5007493680970901461047409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676658241294535281396545 5007493680970901461047409)
          ·
            refine ⟨3755620260728176095785557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5007493680970901461047409 3755620260728176095785557)
            ·
              refine ⟨44011174930408313622487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3755620260728176095785557 44011174930408313622487)
              ·
                rfl

theorem cell22_3471314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 8].length) (baseStart_3471314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471314 prefixEnd_3471314 := by exact prefixLift 3471314
  have htrace : WordTrace (prefixWord ++ tailWord_3471314) baseStart_3471314 baseEnd_3471314 := by
    simpa [prefixWord, tailWord_3471314, baseEnd_3471314] using wordTrace_append hprefix tailTrace_3471314
  have hstable : (prefixWord ++ tailWord_3471314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471314).length < 2 ^ (prefixWord ++ tailWord_3471314).sum := by decide
  have hdescent : baseEnd_3471314 < baseStart_3471314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471329 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 3, 3]
def baseStart_3471329 : Nat := 118140960795 + 3471329 * 2 ^ 59
def prefixEnd_3471329 : Nat := 4983230072969 + 3 ^ 40 * 3471329 * 2
def baseEnd_3471329 : Nat := 1188306857927569428682103

theorem tailTrace_3471329 : CollatzResearch.WordTrace tailWord_3471329 prefixEnd_3471329 1188306857927569428682103 := by
  unfold tailWord_3471329
  simp only [CollatzResearch.WordTrace]
  refine ⟨126609770040975363638649041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84406513360650242425766027 126609770040975363638649041)
  ·
    refine ⟨94957327530731522728986781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126609770040975363638649041 94957327530731522728986781)
    ·
      refine ⟨35608997824024321023370043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94957327530731522728986781 35608997824024321023370043)
      ·
        refine ⟨53413496736036481535055065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35608997824024321023370043 53413496736036481535055065)
        ·
          refine ⟨40060122552027361151291299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53413496736036481535055065 40060122552027361151291299)
          ·
            refine ⟨60090183828041041726936949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40060122552027361151291299 60090183828041041726936949)
            ·
              refine ⟨5633454733878847661900339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60090183828041041726936949 5633454733878847661900339)
              ·
                refine ⟨8450182100818271492850509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633454733878847661900339 8450182100818271492850509)
                ·
                  refine ⟨3168818287806851809818941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8450182100818271492850509 3168818287806851809818941)
                  ·
                    refine ⟨1188306857927569428682103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168818287806851809818941 1188306857927569428682103)
                    ·
                      rfl

theorem cell22_3471329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_3471329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471329 prefixEnd_3471329 := by exact prefixLift 3471329
  have htrace : WordTrace (prefixWord ++ tailWord_3471329) baseStart_3471329 baseEnd_3471329 := by
    simpa [prefixWord, tailWord_3471329, baseEnd_3471329] using wordTrace_append hprefix tailTrace_3471329
  have hstable : (prefixWord ++ tailWord_3471329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471329).length < 2 ^ (prefixWord ++ tailWord_3471329).sum := by decide
  have hdescent : baseEnd_3471329 < baseStart_3471329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471335 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 2, 3]
def baseStart_3471335 : Nat := 118140960795 + 3471335 * 2 ^ 59
def prefixEnd_3471335 : Nat := 4983230072969 + 3 ^ 40 * 3471335 * 2
def baseEnd_3471335 : Nat := 1188308911850187413032085

theorem tailTrace_3471335 : CollatzResearch.WordTrace tailWord_3471335 prefixEnd_3471335 1188308911850187413032085 := by
  unfold tailWord_3471335
  simp only [CollatzResearch.WordTrace]
  refine ⟨126609988878953626663367459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84406659252635751108911639 126609988878953626663367459)
  ·
    refine ⟨189914983318430439995051189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126609988878953626663367459 189914983318430439995051189)
    ·
      refine ⟨17804529686102853749536049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189914983318430439995051189 17804529686102853749536049)
      ·
        refine ⟨13353397264577140312152037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17804529686102853749536049 13353397264577140312152037)
        ·
          refine ⟨2503761987108213808528507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13353397264577140312152037 2503761987108213808528507)
          ·
            refine ⟨3755642980662320712792761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503761987108213808528507 3755642980662320712792761)
            ·
              refine ⟨2816732235496740534594571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755642980662320712792761 2816732235496740534594571)
              ·
                refine ⟨4225098353245110801891857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2816732235496740534594571 4225098353245110801891857)
                ·
                  refine ⟨3168823764933833101418893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4225098353245110801891857 3168823764933833101418893)
                  ·
                    refine ⟨1188308911850187413032085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168823764933833101418893 1188308911850187413032085)
                    ·
                      rfl

theorem cell22_3471335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_3471335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471335 prefixEnd_3471335 := by exact prefixLift 3471335
  have htrace : WordTrace (prefixWord ++ tailWord_3471335) baseStart_3471335 baseEnd_3471335 := by
    simpa [prefixWord, tailWord_3471335, baseEnd_3471335] using wordTrace_append hprefix tailTrace_3471335
  have hstable : (prefixWord ++ tailWord_3471335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471335).length < 2 ^ (prefixWord ++ tailWord_3471335).sum := by decide
  have hdescent : baseEnd_3471335 < baseStart_3471335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471389 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3471389 : Nat := 118140960795 + 3471389 * 2 ^ 59
def prefixEnd_3471389 : Nat := 4983230072969 + 3 ^ 40 * 3471389 * 2
def baseEnd_3471389 : Nat := 1188327397153749272181919

theorem tailTrace_3471389 : CollatzResearch.WordTrace tailWord_3471389 prefixEnd_3471389 1188327397153749272181919 := by
  unfold tailWord_3471389
  simp only [CollatzResearch.WordTrace]
  refine ⟨126611958420757993885833221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84407972280505329257222147 126611958420757993885833221)
  ·
    refine ⟨23739742203892123853593729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126611958420757993885833221 23739742203892123853593729)
    ·
      refine ⟨17804806652919092890195297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23739742203892123853593729 17804806652919092890195297)
      ·
        refine ⟨13353604989689319667646473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17804806652919092890195297 13353604989689319667646473)
        ·
          refine ⟨10015203742266989750734855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13353604989689319667646473 10015203742266989750734855)
          ·
            refine ⟨15022805613400484626102283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10015203742266989750734855 15022805613400484626102283)
            ·
              refine ⟨22534208420100726939153425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15022805613400484626102283 22534208420100726939153425)
              ·
                refine ⟨16900656315075545204365069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22534208420100726939153425 16900656315075545204365069)
                ·
                  refine ⟨6337746118153329451636901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16900656315075545204365069 6337746118153329451636901)
                  ·
                    refine ⟨1188327397153749272181919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6337746118153329451636901 1188327397153749272181919)
                    ·
                      rfl

theorem cell22_3471389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3471389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471389 prefixEnd_3471389 := by exact prefixLift 3471389
  have htrace : WordTrace (prefixWord ++ tailWord_3471389) baseStart_3471389 baseEnd_3471389 := by
    simpa [prefixWord, tailWord_3471389, baseEnd_3471389] using wordTrace_append hprefix tailTrace_3471389
  have hstable : (prefixWord ++ tailWord_3471389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471389).length < 2 ^ (prefixWord ++ tailWord_3471389).sum := by decide
  have hdescent : baseEnd_3471389 < baseStart_3471389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471421 : List Nat := [1, 4, 1, 3, 1, 1, 4, 3, 4]
def baseStart_3471421 : Nat := 118140960795 + 3471421 * 2 ^ 59
def prefixEnd_3471421 : Nat := 4983230072969 + 3 ^ 40 * 3471421 * 2
def baseEnd_3471421 : Nat := 396112783802570618460607

theorem tailTrace_3471421 : CollatzResearch.WordTrace tailWord_3471421 prefixEnd_3471421 396112783802570618460607 := by
  unfold tailWord_3471421
  simp only [CollatzResearch.WordTrace]
  refine ⟨126613125556642063350998117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84408750371094708900665411 126613125556642063350998117)
  ·
    refine ⟨23739961041870386878312147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126613125556642063350998117 23739961041870386878312147)
    ·
      refine ⟨35609941562805580317468221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23739961041870386878312147 35609941562805580317468221)
      ·
        refine ⟨13353728086052092619050583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35609941562805580317468221 13353728086052092619050583)
        ·
          refine ⟨20030592129078138928575875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13353728086052092619050583 20030592129078138928575875)
          ·
            refine ⟨30045888193617208392863813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20030592129078138928575875 30045888193617208392863813)
            ·
              refine ⟨5633604036303226573661965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30045888193617208392863813 5633604036303226573661965)
              ·
                refine ⟨2112601513613709965123237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5633604036303226573661965 2112601513613709965123237)
                ·
                  refine ⟨396112783802570618460607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2112601513613709965123237 396112783802570618460607)
                  ·
                    rfl

theorem cell22_3471421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_3471421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471421 prefixEnd_3471421 := by exact prefixLift 3471421
  have htrace : WordTrace (prefixWord ++ tailWord_3471421) baseStart_3471421 baseEnd_3471421 := by
    simpa [prefixWord, tailWord_3471421, baseEnd_3471421] using wordTrace_append hprefix tailTrace_3471421
  have hstable : (prefixWord ++ tailWord_3471421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471421).length < 2 ^ (prefixWord ++ tailWord_3471421).sum := by decide
  have hdescent : baseEnd_3471421 < baseStart_3471421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471436 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_3471436 : Nat := 118140960795 + 3471436 * 2 ^ 59
def prefixEnd_3471436 : Nat := 4983230072969 + 3 ^ 40 * 3471436 * 2
def baseEnd_3471436 : Nat := 1188343486214256816256775

theorem tailTrace_3471436 : CollatzResearch.WordTrace tailWord_3471436 prefixEnd_3471436 1188343486214256816256775 := by
  unfold tailWord_3471436
  simp only [CollatzResearch.WordTrace]
  refine ⟨63306836325793860456397081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84409115101058480608529441 63306836325793860456397081)
  ·
    refine ⟨47480127244345395342297811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63306836325793860456397081 47480127244345395342297811)
    ·
      refine ⟨71220190866518093013446717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47480127244345395342297811 71220190866518093013446717)
      ·
        refine ⟨26707571574944284880042519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71220190866518093013446717 26707571574944284880042519)
        ·
          refine ⟨40061357362416427320063779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26707571574944284880042519 40061357362416427320063779)
          ·
            refine ⟨60092036043624640980095669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40061357362416427320063779 60092036043624640980095669)
            ·
              refine ⟨5633628379089810091883969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60092036043624640980095669 5633628379089810091883969)
              ·
                refine ⟨4225221284317357568912977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5633628379089810091883969 4225221284317357568912977)
                ·
                  refine ⟨3168915963238018176684733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4225221284317357568912977 3168915963238018176684733)
                  ·
                    refine ⟨1188343486214256816256775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168915963238018176684733 1188343486214256816256775)
                    ·
                      rfl

theorem cell22_3471436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_3471436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471436 prefixEnd_3471436 := by exact prefixLift 3471436
  have htrace : WordTrace (prefixWord ++ tailWord_3471436) baseStart_3471436 baseEnd_3471436 := by
    simpa [prefixWord, tailWord_3471436, baseEnd_3471436] using wordTrace_append hprefix tailTrace_3471436
  have hstable : (prefixWord ++ tailWord_3471436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471436).length < 2 ^ (prefixWord ++ tailWord_3471436).sum := by decide
  have hdescent : baseEnd_3471436 < baseStart_3471436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471453 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3471453 : Nat := 118140960795 + 3471453 * 2 ^ 59
def prefixEnd_3471453 : Nat := 4983230072969 + 3 ^ 40 * 3471453 * 2
def baseEnd_3471453 : Nat := 1188349305661674438581723

theorem tailTrace_3471453 : CollatzResearch.WordTrace tailWord_3471453 prefixEnd_3471453 1188349305661674438581723 := by
  unfold tailWord_3471453
  simp only [CollatzResearch.WordTrace]
  refine ⟨126614292692526132816163013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84409528461684088544108675 126614292692526132816163013)
  ·
    refine ⟨23740179879848649903030565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126614292692526132816163013 23740179879848649903030565)
    ·
      refine ⟨4451283727471621856818231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23740179879848649903030565 4451283727471621856818231)
      ·
        refine ⟨6676925591207432785227347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451283727471621856818231 6676925591207432785227347)
        ·
          refine ⟨10015388386811149177841021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6676925591207432785227347 10015388386811149177841021)
          ·
            refine ⟨3755770645054180941690383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10015388386811149177841021 3755770645054180941690383)
            ·
              refine ⟨5633655967581271412535575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755770645054180941690383 5633655967581271412535575)
              ·
                refine ⟨8450483951371907118803363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633655967581271412535575 8450483951371907118803363)
                ·
                  refine ⟨12675725927057860678205045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8450483951371907118803363 12675725927057860678205045)
                  ·
                    refine ⟨1188349305661674438581723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12675725927057860678205045 1188349305661674438581723)
                    ·
                      rfl

theorem cell22_3471453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3471453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471453 prefixEnd_3471453 := by exact prefixLift 3471453
  have htrace : WordTrace (prefixWord ++ tailWord_3471453) baseStart_3471453 baseEnd_3471453 := by
    simpa [prefixWord, tailWord_3471453, baseEnd_3471453] using wordTrace_append hprefix tailTrace_3471453
  have hstable : (prefixWord ++ tailWord_3471453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471453).length < 2 ^ (prefixWord ++ tailWord_3471453).sum := by decide
  have hdescent : baseEnd_3471453 < baseStart_3471453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471498 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 3, 3]
def baseStart_3471498 : Nat := 118140960795 + 3471498 * 2 ^ 59
def prefixEnd_3471498 : Nat := 4983230072969 + 3 ^ 40 * 3471498 * 2
def baseEnd_3471498 : Nat := 1188364710081309321206585

theorem tailTrace_3471498 : CollatzResearch.WordTrace tailWord_3471498 prefixEnd_3471498 1188364710081309321206585 := by
  unfold tailWord_3471498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31653983494340776375387787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84410622651575403667700765 31653983494340776375387787)
  ·
    refine ⟨47480975241511164563081681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31653983494340776375387787 47480975241511164563081681)
    ·
      refine ⟨35610731431133373422311261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47480975241511164563081681 35610731431133373422311261)
      ·
        refine ⟨13354024286675015033366723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35610731431133373422311261 13354024286675015033366723)
        ·
          refine ⟨20031036430012522550050085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13354024286675015033366723 20031036430012522550050085)
          ·
            refine ⟨3755819330627347978134391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20031036430012522550050085 3755819330627347978134391)
            ·
              refine ⟨5633728995941021967201587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755819330627347978134391 5633728995941021967201587)
              ·
                refine ⟨8450593493911532950802381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5633728995941021967201587 8450593493911532950802381)
                ·
                  refine ⟨3168972560216824856550893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8450593493911532950802381 3168972560216824856550893)
                  ·
                    refine ⟨1188364710081309321206585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3168972560216824856550893 1188364710081309321206585)
                    ·
                      rfl

theorem cell22_3471498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_3471498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471498 prefixEnd_3471498 := by exact prefixLift 3471498
  have htrace : WordTrace (prefixWord ++ tailWord_3471498) baseStart_3471498 baseEnd_3471498 := by
    simpa [prefixWord, tailWord_3471498, baseEnd_3471498] using wordTrace_append hprefix tailTrace_3471498
  have hstable : (prefixWord ++ tailWord_3471498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471498).length < 2 ^ (prefixWord ++ tailWord_3471498).sum := by decide
  have hdescent : baseEnd_3471498 < baseStart_3471498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471507 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 8]
def baseStart_3471507 : Nat := 118140960795 + 3471507 * 2 ^ 59
def prefixEnd_3471507 : Nat := 4983230072969 + 3 ^ 40 * 3471507 * 2
def baseEnd_3471507 : Nat := 1188367790965236297731557

theorem tailTrace_3471507 : CollatzResearch.WordTrace tailWord_3471507 prefixEnd_3471507 1188367790965236297731557 := by
  unfold tailWord_3471507
  simp only [CollatzResearch.WordTrace]
  refine ⟨126616262234330500038628775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84410841489553666692419183 126616262234330500038628775)
  ·
    refine ⟨189924393351495750057943163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126616262234330500038628775 189924393351495750057943163)
    ·
      refine ⟨284886590027243625086914745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189924393351495750057943163 284886590027243625086914745)
      ·
        refine ⟨213664942520432718815186059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284886590027243625086914745 213664942520432718815186059)
        ·
          refine ⟨320497413780649078222779089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213664942520432718815186059 320497413780649078222779089)
          ·
            refine ⟨240373060335486808667084317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320497413780649078222779089 240373060335486808667084317)
            ·
              refine ⟨90139897625807553250156619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240373060335486808667084317 90139897625807553250156619)
              ·
                refine ⟨135209846438711329875234929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90139897625807553250156619 135209846438711329875234929)
                ·
                  refine ⟨101407384829033497406426197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135209846438711329875234929 101407384829033497406426197)
                  ·
                    refine ⟨1188367790965236297731557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101407384829033497406426197 1188367790965236297731557)
                    ·
                      rfl

theorem cell22_3471507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_3471507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471507 prefixEnd_3471507 := by exact prefixLift 3471507
  have htrace : WordTrace (prefixWord ++ tailWord_3471507) baseStart_3471507 baseEnd_3471507 := by
    simpa [prefixWord, tailWord_3471507, baseEnd_3471507] using wordTrace_append hprefix tailTrace_3471507
  have hstable : (prefixWord ++ tailWord_3471507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471507).length < 2 ^ (prefixWord ++ tailWord_3471507).sum := by decide
  have hdescent : baseEnd_3471507 < baseStart_3471507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471511 : List Nat := [1, 1, 3, 3, 4, 1, 1, 3, 5]
def baseStart_3471511 : Nat := 118140960795 + 3471511 * 2 ^ 59
def prefixEnd_3471511 : Nat := 4983230072969 + 3 ^ 40 * 3471511 * 2
def baseEnd_3471511 : Nat := 396123053415660540210515

theorem tailTrace_3471511 : CollatzResearch.WordTrace tailWord_3471511 prefixEnd_3471511 396123053415660540210515 := by
  unfold tailWord_3471511
  simp only [CollatzResearch.WordTrace]
  refine ⟨126616408126316008721774387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84410938750877339147849591 126616408126316008721774387)
  ·
    refine ⟨189924612189474013082661581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126616408126316008721774387 189924612189474013082661581)
    ·
      refine ⟨71221729571052754905998093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189924612189474013082661581 71221729571052754905998093)
      ·
        refine ⟨26708148589144783089749285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71221729571052754905998093 26708148589144783089749285)
        ·
          refine ⟨5007777860464646829327991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26708148589144783089749285 5007777860464646829327991)
          ·
            refine ⟨7511666790696970243991987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007777860464646829327991 7511666790696970243991987)
            ·
              refine ⟨11267500186045455365987981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511666790696970243991987 11267500186045455365987981)
              ·
                refine ⟨4225312569767045762245493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11267500186045455365987981 4225312569767045762245493)
                ·
                  refine ⟨396123053415660540210515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4225312569767045762245493 396123053415660540210515)
                  ·
                    rfl

theorem cell22_3471511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 3, 5].length) (baseStart_3471511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471511 prefixEnd_3471511 := by exact prefixLift 3471511
  have htrace : WordTrace (prefixWord ++ tailWord_3471511) baseStart_3471511 baseEnd_3471511 := by
    simpa [prefixWord, tailWord_3471511, baseEnd_3471511] using wordTrace_append hprefix tailTrace_3471511
  have hstable : (prefixWord ++ tailWord_3471511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471511).length < 2 ^ (prefixWord ++ tailWord_3471511).sum := by decide
  have hdescent : baseEnd_3471511 < baseStart_3471511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471569 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_3471569 : Nat := 118140960795 + 3471569 * 2 ^ 59
def prefixEnd_3471569 : Nat := 4983230072969 + 3 ^ 40 * 3471569 * 2
def baseEnd_3471569 : Nat := 1188389014832288802681367

theorem tailTrace_3471569 : CollatzResearch.WordTrace tailWord_3471569 prefixEnd_3471569 1188389014832288802681367 := by
  unfold tailWord_3471569
  simp only [CollatzResearch.WordTrace]
  refine ⟨126618523560105884627385761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84412349040070589751590507 126618523560105884627385761)
  ·
    refine ⟨94963892670079413470539321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126618523560105884627385761 94963892670079413470539321)
    ·
      refine ⟨71222919502559560102904491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94963892670079413470539321 71222919502559560102904491)
      ·
        refine ⟨106834379253839340154356737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71222919502559560102904491 106834379253839340154356737)
        ·
          refine ⟨80125784440379505115767553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106834379253839340154356737 80125784440379505115767553)
          ·
            refine ⟨60094338330284628836825665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80125784440379505115767553 60094338330284628836825665)
            ·
              refine ⟨45070753747713471627619249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60094338330284628836825665 45070753747713471627619249)
              ·
                refine ⟨33803065310785103720714437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45070753747713471627619249 33803065310785103720714437)
                ·
                  refine ⟨6338074745772206947633957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33803065310785103720714437 6338074745772206947633957)
                  ·
                    refine ⟨1188389014832288802681367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338074745772206947633957 1188389014832288802681367)
                    ·
                      rfl

theorem cell22_3471569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_3471569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471569 prefixEnd_3471569 := by exact prefixLift 3471569
  have htrace : WordTrace (prefixWord ++ tailWord_3471569) baseStart_3471569 baseEnd_3471569 := by
    simpa [prefixWord, tailWord_3471569, baseEnd_3471569] using wordTrace_append hprefix tailTrace_3471569
  have hstable : (prefixWord ++ tailWord_3471569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471569).length < 2 ^ (prefixWord ++ tailWord_3471569).sum := by decide
  have hdescent : baseEnd_3471569 < baseStart_3471569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471616 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 3, 3]
def baseStart_3471616 : Nat := 118140960795 + 3471616 * 2 ^ 59
def prefixEnd_3471616 : Nat := 4983230072969 + 3 ^ 40 * 3471616 * 2
def baseEnd_3471616 : Nat := 1188405103892796346756223

theorem tailTrace_3471616 : CollatzResearch.WordTrace tailWord_3471616 prefixEnd_3471616 1188405103892796346756223 := by
  unfold tailWord_3471616
  simp only [CollatzResearch.WordTrace]
  refine ⟨63310118895467805827173351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84413491860623741102897801 63310118895467805827173351)
  ·
    refine ⟨94965178343201708740760027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63310118895467805827173351 94965178343201708740760027)
    ·
      refine ⟨142447767514802563111140041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94965178343201708740760027 142447767514802563111140041)
      ·
        refine ⟨106835825636101922333355031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142447767514802563111140041 106835825636101922333355031)
        ·
          refine ⟨160253738454152883500032547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106835825636101922333355031 160253738454152883500032547)
          ·
            refine ⟨240380607681229325250048821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160253738454152883500032547 240380607681229325250048821)
            ·
              refine ⟨22535681970115249242192077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240380607681229325250048821 22535681970115249242192077)
              ·
                refine ⟨8450880738793218465822029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22535681970115249242192077 8450880738793218465822029)
                ·
                  refine ⟨3169080277047456924683261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8450880738793218465822029 3169080277047456924683261)
                  ·
                    refine ⟨1188405103892796346756223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3169080277047456924683261 1188405103892796346756223)
                    ·
                      rfl

theorem cell22_3471616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 3].length) (baseStart_3471616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471616 prefixEnd_3471616 := by exact prefixLift 3471616
  have htrace : WordTrace (prefixWord ++ tailWord_3471616) baseStart_3471616 baseEnd_3471616 := by
    simpa [prefixWord, tailWord_3471616, baseEnd_3471616] using wordTrace_append hprefix tailTrace_3471616
  have hstable : (prefixWord ++ tailWord_3471616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471616).length < 2 ^ (prefixWord ++ tailWord_3471616).sum := by decide
  have hdescent : baseEnd_3471616 < baseStart_3471616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471676 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_3471676 : Nat := 118140960795 + 3471676 * 2 ^ 59
def prefixEnd_3471676 : Nat := 4983230072969 + 3 ^ 40 * 3471676 * 2
def baseEnd_3471676 : Nat := 1188425643118976190256039

theorem tailTrace_3471676 : CollatzResearch.WordTrace tailWord_3471676 prefixEnd_3471676 1188425643118976190256039 := by
  unfold tailWord_3471676
  simp only [CollatzResearch.WordTrace]
  refine ⟨63311213085359120950765441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84414950780478827934353921 63311213085359120950765441)
  ·
    refine ⟨47483409814019340713074081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63311213085359120950765441 47483409814019340713074081)
    ·
      refine ⟨35612557360514505534805561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47483409814019340713074081 35612557360514505534805561)
      ·
        refine ⟨26709418020385879151104171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35612557360514505534805561 26709418020385879151104171)
        ·
          refine ⟨40064127030578818726656257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26709418020385879151104171 40064127030578818726656257)
          ·
            refine ⟨30048095272934114044992193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40064127030578818726656257 30048095272934114044992193)
            ·
              refine ⟨22536071454700585533744145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30048095272934114044992193 22536071454700585533744145)
              ·
                refine ⟨16902053591025439150308109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22536071454700585533744145 16902053591025439150308109)
                ·
                  refine ⟨6338270096634539681365541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16902053591025439150308109 6338270096634539681365541)
                  ·
                    refine ⟨1188425643118976190256039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338270096634539681365541 1188425643118976190256039)
                    ·
                      rfl

theorem cell22_3471676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_3471676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471676 prefixEnd_3471676 := by exact prefixLift 3471676
  have htrace : WordTrace (prefixWord ++ tailWord_3471676) baseStart_3471676 baseEnd_3471676 := by
    simpa [prefixWord, tailWord_3471676, baseEnd_3471676] using wordTrace_append hprefix tailTrace_3471676
  have hstable : (prefixWord ++ tailWord_3471676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471676).length < 2 ^ (prefixWord ++ tailWord_3471676).sum := by decide
  have hdescent : baseEnd_3471676 < baseStart_3471676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471721 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_3471721 : Nat := 118140960795 + 3471721 * 2 ^ 59
def prefixEnd_3471721 : Nat := 4983230072969 + 3 ^ 40 * 3471721 * 2
def baseEnd_3471721 : Nat := 1188441047538611072880901

theorem tailTrace_3471721 : CollatzResearch.WordTrace tailWord_3471721 prefixEnd_3471721 1188441047538611072880901 := by
  unfold tailWord_3471721
  simp only [CollatzResearch.WordTrace]
  refine ⟨126624067455555214586919017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84416044970370143057946011 126624067455555214586919017)
  ·
    refine ⟨94968050591666410940189263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126624067455555214586919017 94968050591666410940189263)
    ·
      refine ⟨142452075887499616410283895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94968050591666410940189263 142452075887499616410283895)
      ·
        refine ⟨213678113831249424615425843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142452075887499616410283895 213678113831249424615425843)
        ·
          refine ⟨320517170746874136923138765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213678113831249424615425843 320517170746874136923138765)
          ·
            refine ⟨120193939030077801346177037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320517170746874136923138765 120193939030077801346177037)
            ·
              refine ⟨45072727136279175504816389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120193939030077801346177037 45072727136279175504816389)
              ·
                refine ⟨8451136338052345407153073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45072727136279175504816389 8451136338052345407153073)
                ·
                  refine ⟨6338352253539259055364805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451136338052345407153073 6338352253539259055364805)
                  ·
                    refine ⟨1188441047538611072880901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338352253539259055364805 1188441047538611072880901)
                    ·
                      rfl

theorem cell22_3471721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_3471721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471721 prefixEnd_3471721 := by exact prefixLift 3471721
  have htrace : WordTrace (prefixWord ++ tailWord_3471721) baseStart_3471721 baseEnd_3471721 := by
    simpa [prefixWord, tailWord_3471721, baseEnd_3471721] using wordTrace_append hprefix tailTrace_3471721
  have hstable : (prefixWord ++ tailWord_3471721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471721).length < 2 ^ (prefixWord ++ tailWord_3471721).sum := by decide
  have hdescent : baseEnd_3471721 < baseStart_3471721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471753 : List Nat := [1, 2, 1, 1, 6, 2, 3, 6]
def baseStart_3471753 : Nat := 118140960795 + 3471753 * 2 ^ 59
def prefixEnd_3471753 : Nat := 4983230072969 + 3 ^ 40 * 3471753 * 2
def baseEnd_3471753 : Nat := 132050222421397072897867

theorem tailTrace_3471753 : CollatzResearch.WordTrace tailWord_3471753 prefixEnd_3471753 132050222421397072897867 := by
  unfold tailWord_3471753
  simp only [CollatzResearch.WordTrace]
  refine ⟨126625234591439284052083913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84416823060959522701389275 126625234591439284052083913)
  ·
    refine ⟨94968925943579463039062935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126625234591439284052083913 94968925943579463039062935)
    ·
      refine ⟨142453388915369194558594403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94968925943579463039062935 142453388915369194558594403)
      ·
        refine ⟨213680083373053791837891605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142453388915369194558594403 213680083373053791837891605)
        ·
          refine ⟨10016253908111896492401169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213680083373053791837891605 10016253908111896492401169)
          ·
            refine ⟨7512190431083922369300877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10016253908111896492401169 7512190431083922369300877)
            ·
              refine ⟨2817071411656470888487829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7512190431083922369300877 2817071411656470888487829)
              ·
                refine ⟨132050222421397072897867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2817071411656470888487829 132050222421397072897867)
                ·
                  rfl

theorem cell22_3471753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 6].length) (baseStart_3471753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471753 prefixEnd_3471753 := by exact prefixLift 3471753
  have htrace : WordTrace (prefixWord ++ tailWord_3471753) baseStart_3471753 baseEnd_3471753 := by
    simpa [prefixWord, tailWord_3471753, baseEnd_3471753] using wordTrace_append hprefix tailTrace_3471753
  have hstable : (prefixWord ++ tailWord_3471753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471753).length < 2 ^ (prefixWord ++ tailWord_3471753).sum := by decide
  have hdescent : baseEnd_3471753 < baseStart_3471753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471774 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_3471774 : Nat := 118140960795 + 3471774 * 2 ^ 59
def prefixEnd_3471774 : Nat := 4983230072969 + 3 ^ 40 * 3471774 * 2
def baseEnd_3471774 : Nat := 1188459190521736601305739

theorem tailTrace_3471774 : CollatzResearch.WordTrace tailWord_3471774 prefixEnd_3471774 1188459190521736601305739 := by
  unfold tailWord_3471774
  simp only [CollatzResearch.WordTrace]
  refine ⟨15828250065545400579824797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84417333682908803092398917 15828250065545400579824797)
  ·
    refine ⟨5935593774579525217434299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15828250065545400579824797 5935593774579525217434299)
    ·
      refine ⟨8903390661869287826151449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5935593774579525217434299 8903390661869287826151449)
      ·
        refine ⟨6677542996401965869613587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8903390661869287826151449 6677542996401965869613587)
        ·
          refine ⟨10016314494602948804420381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6677542996401965869613587 10016314494602948804420381)
          ·
            refine ⟨3756117935476105801657643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10016314494602948804420381 3756117935476105801657643)
            ·
              refine ⟨5634176903214158702486465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756117935476105801657643 5634176903214158702486465)
              ·
                refine ⟨4225632677410619026864849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5634176903214158702486465 4225632677410619026864849)
                ·
                  refine ⟨3169224508057964270148637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4225632677410619026864849 3169224508057964270148637)
                  ·
                    refine ⟨1188459190521736601305739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3169224508057964270148637 1188459190521736601305739)
                    ·
                      rfl

theorem cell22_3471774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_3471774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471774 prefixEnd_3471774 := by exact prefixLift 3471774
  have htrace : WordTrace (prefixWord ++ tailWord_3471774) baseStart_3471774 baseEnd_3471774 := by
    simpa [prefixWord, tailWord_3471774, baseEnd_3471774] using wordTrace_append hprefix tailTrace_3471774
  have hstable : (prefixWord ++ tailWord_3471774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471774).length < 2 ^ (prefixWord ++ tailWord_3471774).sum := by decide
  have hdescent : baseEnd_3471774 < baseStart_3471774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471781 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 7]
def baseStart_3471781 : Nat := 118140960795 + 3471781 * 2 ^ 59
def prefixEnd_3471781 : Nat := 4983230072969 + 3 ^ 40 * 3471781 * 2
def baseEnd_3471781 : Nat := 396153862254930305460239

theorem tailTrace_3471781 : CollatzResearch.WordTrace tailWord_3471781 prefixEnd_3471781 396153862254930305460239 := by
  unfold tailWord_3471781
  simp only [CollatzResearch.WordTrace]
  refine ⟨126626255835337844834103197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84417503890225229889402131 126626255835337844834103197)
  ·
    refine ⟨47484845938251691812788699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126626255835337844834103197 47484845938251691812788699)
    ·
      refine ⟨71227268907377537719183049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47484845938251691812788699 71227268907377537719183049)
      ·
        refine ⟨53420451680533153289387287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71227268907377537719183049 53420451680533153289387287)
        ·
          refine ⟨80130677520799729934080931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53420451680533153289387287 80130677520799729934080931)
          ·
            refine ⟨120196016281199594901121397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80130677520799729934080931 120196016281199594901121397)
            ·
              refine ⟨11268376526362462021980131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120196016281199594901121397 11268376526362462021980131)
              ·
                refine ⟨16902564789543693032970197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11268376526362462021980131 16902564789543693032970197)
                ·
                  refine ⟨396153862254930305460239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16902564789543693032970197 396153862254930305460239)
                  ·
                    rfl

theorem cell22_3471781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_3471781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471781 prefixEnd_3471781 := by exact prefixLift 3471781
  have htrace : WordTrace (prefixWord ++ tailWord_3471781) baseStart_3471781 baseEnd_3471781 := by
    simpa [prefixWord, tailWord_3471781, baseEnd_3471781] using wordTrace_append hprefix tailTrace_3471781
  have hstable : (prefixWord ++ tailWord_3471781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471781).length < 2 ^ (prefixWord ++ tailWord_3471781).sum := by decide
  have hdescent : baseEnd_3471781 < baseStart_3471781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471871 : List Nat := [1, 1, 2, 2, 1, 2, 3, 10]
def baseStart_3471871 : Nat := 118140960795 + 3471871 * 2 ^ 59
def prefixEnd_3471871 : Nat := 4983230072969 + 3 ^ 40 * 3471871 * 2
def baseEnd_3471871 : Nat := 132054710622673409070049

theorem tailTrace_3471871 : CollatzResearch.WordTrace tailWord_3471871 prefixEnd_3471871 132054710622673409070049 := by
  unfold tailWord_3471871
  simp only [CollatzResearch.WordTrace]
  refine ⟨126629538405011790204879467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84419692270007860136586311 126629538405011790204879467)
  ·
    refine ⟨189944307607517685307319201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126629538405011790204879467 189944307607517685307319201)
    ·
      refine ⟨142458230705638263980489401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189944307607517685307319201 142458230705638263980489401)
      ·
        refine ⟨106843673029228697985367051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142458230705638263980489401 106843673029228697985367051)
        ·
          refine ⟨160265509543843046978050577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106843673029228697985367051 160265509543843046978050577)
          ·
            refine ⟨120199132157882285233537933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160265509543843046978050577 120199132157882285233537933)
            ·
              refine ⟨45074674559205856962576725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120199132157882285233537933 45074674559205856962576725)
              ·
                refine ⟨132054710622673409070049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45074674559205856962576725 132054710622673409070049)
                ·
                  rfl

theorem cell22_3471871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 10].length) (baseStart_3471871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471871 prefixEnd_3471871 := by exact prefixLift 3471871
  have htrace : WordTrace (prefixWord ++ tailWord_3471871) baseStart_3471871 baseEnd_3471871 := by
    simpa [prefixWord, tailWord_3471871, baseEnd_3471871] using wordTrace_append hprefix tailTrace_3471871
  have hstable : (prefixWord ++ tailWord_3471871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471871).length < 2 ^ (prefixWord ++ tailWord_3471871).sum := by decide
  have hdescent : baseEnd_3471871 < baseStart_3471871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471948 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_3471948 : Nat := 118140960795 + 3471948 * 2 ^ 59
def prefixEnd_3471948 : Nat := 4983230072969 + 3 ^ 40 * 3471948 * 2
def baseEnd_3471948 : Nat := 1188518754277658147455205

theorem tailTrace_3471948 : CollatzResearch.WordTrace tailWord_3471948 prefixEnd_3471948 1188518754277658147455205 := by
  unfold tailWord_3471948
  simp only [CollatzResearch.WordTrace]
  refine ⟨63316173412866416177716249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84421564550488554903621665 63316173412866416177716249)
  ·
    refine ⟨47487130059649812133287187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63316173412866416177716249 47487130059649812133287187)
    ·
      refine ⟨71230695089474718199930781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47487130059649812133287187 71230695089474718199930781)
      ·
        refine ⟨26711510658553019324974043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71230695089474718199930781 26711510658553019324974043)
        ·
          refine ⟨40067265987829528987461065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26711510658553019324974043 40067265987829528987461065)
          ·
            refine ⟨30050449490872146740595799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40067265987829528987461065 30050449490872146740595799)
            ·
              refine ⟨45075674236308220110893699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30050449490872146740595799 45075674236308220110893699)
              ·
                refine ⟨67613511354462330166340549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45075674236308220110893699 67613511354462330166340549)
                ·
                  refine ⟨12677533378961686906188853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67613511354462330166340549 12677533378961686906188853)
                  ·
                    refine ⟨1188518754277658147455205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12677533378961686906188853 1188518754277658147455205)
                    ·
                      rfl

theorem cell22_3471948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_3471948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471948 prefixEnd_3471948 := by exact prefixLift 3471948
  have htrace : WordTrace (prefixWord ++ tailWord_3471948) baseStart_3471948 baseEnd_3471948 := by
    simpa [prefixWord, tailWord_3471948, baseEnd_3471948] using wordTrace_append hprefix tailTrace_3471948
  have hstable : (prefixWord ++ tailWord_3471948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471948).length < 2 ^ (prefixWord ++ tailWord_3471948).sum := by decide
  have hdescent : baseEnd_3471948 < baseStart_3471948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471950 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_3471950 : Nat := 118140960795 + 3471950 * 2 ^ 59
def prefixEnd_3471950 : Nat := 4983230072969 + 3 ^ 40 * 3471950 * 2
def baseEnd_3471950 : Nat := 396173146306176936301733

theorem tailTrace_3471950 : CollatzResearch.WordTrace tailWord_3471950 prefixEnd_3471950 396173146306176936301733 := by
  unfold tailWord_3471950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15829052471465698337125663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84421613181150391131336869 15829052471465698337125663)
  ·
    refine ⟨23743578707198547505688495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15829052471465698337125663 23743578707198547505688495)
    ·
      refine ⟨35615368060797821258532743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23743578707198547505688495 35615368060797821258532743)
      ·
        refine ⟨53423052091196731887799115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35615368060797821258532743 53423052091196731887799115)
        ·
          refine ⟨80134578136795097831698673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53423052091196731887799115 80134578136795097831698673)
          ·
            refine ⟨60100933602596323373774005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80134578136795097831698673 60100933602596323373774005)
            ·
              refine ⟨5634462525243405316291313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60100933602596323373774005 5634462525243405316291313)
              ·
                refine ⟨4225846893932553987218485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5634462525243405316291313 4225846893932553987218485)
                ·
                  refine ⟨396173146306176936301733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4225846893932553987218485 396173146306176936301733)
                  ·
                    rfl

theorem cell22_3471950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_3471950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471950 prefixEnd_3471950 := by exact prefixLift 3471950
  have htrace : WordTrace (prefixWord ++ tailWord_3471950) baseStart_3471950 baseEnd_3471950 := by
    simpa [prefixWord, tailWord_3471950, baseEnd_3471950] using wordTrace_append hprefix tailTrace_3471950
  have hstable : (prefixWord ++ tailWord_3471950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471950).length < 2 ^ (prefixWord ++ tailWord_3471950).sum := by decide
  have hdescent : baseEnd_3471950 < baseStart_3471950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471980 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_3471980 : Nat := 118140960795 + 3471980 * 2 ^ 59
def prefixEnd_3471980 : Nat := 4983230072969 + 3 ^ 40 * 3471980 * 2
def baseEnd_3471980 : Nat := 1188529708531620730655107

theorem tailTrace_3471980 : CollatzResearch.WordTrace tailWord_3471980 prefixEnd_3471980 1188529708531620730655107 := by
  unfold tailWord_3471980
  simp only [CollatzResearch.WordTrace]
  refine ⟨63316756980808450910298697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84422342641077934547064929 63316756980808450910298697)
  ·
    refine ⟨47487567735606338182724023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63316756980808450910298697 47487567735606338182724023)
    ·
      refine ⟨71231351603409507274086035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47487567735606338182724023 71231351603409507274086035)
      ·
        refine ⟨106847027405114260911129053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71231351603409507274086035 106847027405114260911129053)
        ·
          refine ⟨40067635276917847841673395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106847027405114260911129053 40067635276917847841673395)
          ·
            refine ⟨60101452915376771762510093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40067635276917847841673395 60101452915376771762510093)
            ·
              refine ⟨22538044843266289410941285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60101452915376771762510093 22538044843266289410941285)
              ·
                refine ⟨4225883408112429264551491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22538044843266289410941285 4225883408112429264551491)
                ·
                  refine ⟨6338825112168643896827237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225883408112429264551491 6338825112168643896827237)
                  ·
                    refine ⟨1188529708531620730655107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338825112168643896827237 1188529708531620730655107)
                    ·
                      rfl

theorem cell22_3471980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_3471980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471980 prefixEnd_3471980 := by exact prefixLift 3471980
  have htrace : WordTrace (prefixWord ++ tailWord_3471980) baseStart_3471980 baseEnd_3471980 := by
    simpa [prefixWord, tailWord_3471980, baseEnd_3471980] using wordTrace_append hprefix tailTrace_3471980
  have hstable : (prefixWord ++ tailWord_3471980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471980).length < 2 ^ (prefixWord ++ tailWord_3471980).sum := by decide
  have hdescent : baseEnd_3471980 < baseStart_3471980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3471995 : List Nat := [1, 1, 1, 1, 1, 4, 2, 7, 4]
def baseStart_3471995 : Nat := 118140960795 + 3471995 * 2 ^ 59
def prefixEnd_3471995 : Nat := 4983230072969 + 3 ^ 40 * 3471995 * 2
def baseEnd_3471995 : Nat := 396178281112721897176687

theorem tailTrace_3471995 : CollatzResearch.WordTrace tailWord_3471995 prefixEnd_3471995 396178281112721897176687 := by
  unfold tailWord_3471995
  simp only [CollatzResearch.WordTrace]
  refine ⟨126634061056562559382393439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84422707371041706254928959 126634061056562559382393439)
  ·
    refine ⟨189951091584843839073590159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126634061056562559382393439 189951091584843839073590159)
    ·
      refine ⟨284926637377265758610385239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189951091584843839073590159 284926637377265758610385239)
      ·
        refine ⟨427389956065898637915577859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284926637377265758610385239 427389956065898637915577859)
        ·
          refine ⟨641084934098847956873366789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427389956065898637915577859 641084934098847956873366789)
          ·
            refine ⟨120203425143533991913756273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 641084934098847956873366789 120203425143533991913756273)
            ·
              refine ⟨90152568857650493935317205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120203425143533991913756273 90152568857650493935317205)
              ·
                refine ⟨2112950832601183451608997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90152568857650493935317205 2112950832601183451608997)
                ·
                  refine ⟨396178281112721897176687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2112950832601183451608997 396178281112721897176687)
                  ·
                    rfl

theorem cell22_3471995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 7, 4].length) (baseStart_3471995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3471995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3471995 prefixEnd_3471995 := by exact prefixLift 3471995
  have htrace : WordTrace (prefixWord ++ tailWord_3471995) baseStart_3471995 baseEnd_3471995 := by
    simpa [prefixWord, tailWord_3471995, baseEnd_3471995] using wordTrace_append hprefix tailTrace_3471995
  have hstable : (prefixWord ++ tailWord_3471995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3471995).length < 2 ^ (prefixWord ++ tailWord_3471995).sum := by decide
  have hdescent : baseEnd_3471995 < baseStart_3471995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3471995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472177 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_3472177 : Nat := 118140960795 + 3472177 * 2 ^ 59
def prefixEnd_3472177 : Nat := 4983230072969 + 3 ^ 40 * 3472177 * 2
def baseEnd_3472177 : Nat := 1188597145657577883479503

theorem tailTrace_3472177 : CollatzResearch.WordTrace tailWord_3472177 prefixEnd_3472177 1188597145657577883479503 := by
  unfold tailWord_3472177
  simp only [CollatzResearch.WordTrace]
  refine ⟨126640699141903204465518785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84427132761268802977012523 126640699141903204465518785)
  ·
    refine ⟨94980524356427403349139089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126640699141903204465518785 94980524356427403349139089)
    ·
      refine ⟨71235393267320552511854317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94980524356427403349139089 71235393267320552511854317)
      ·
        refine ⟨26713272475245207191945369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71235393267320552511854317 26713272475245207191945369)
        ·
          refine ⟨20034954356433905393959027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26713272475245207191945369 20034954356433905393959027)
          ·
            refine ⟨30052431534650858090938541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20034954356433905393959027 30052431534650858090938541)
            ·
              refine ⟨11269661825494071784101953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30052431534650858090938541 11269661825494071784101953)
              ·
                refine ⟨8452246369120553838076465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11269661825494071784101953 8452246369120553838076465)
                ·
                  refine ⟨6339184776840415378557349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8452246369120553838076465 6339184776840415378557349)
                  ·
                    refine ⟨1188597145657577883479503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6339184776840415378557349 1188597145657577883479503)
                    ·
                      rfl

theorem cell22_3472177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_3472177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472177 prefixEnd_3472177 := by exact prefixLift 3472177
  have htrace : WordTrace (prefixWord ++ tailWord_3472177) baseStart_3472177 baseEnd_3472177 := by
    simpa [prefixWord, tailWord_3472177, baseEnd_3472177] using wordTrace_append hprefix tailTrace_3472177
  have hstable : (prefixWord ++ tailWord_3472177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472177).length < 2 ^ (prefixWord ++ tailWord_3472177).sum := by decide
  have hdescent : baseEnd_3472177 < baseStart_3472177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472181 : List Nat := [1, 3, 3, 1, 3, 2, 3, 2, 4]
def baseStart_3472181 : Nat := 118140960795 + 3472181 * 2 ^ 59
def prefixEnd_3472181 : Nat := 4983230072969 + 3 ^ 40 * 3472181 * 2
def baseEnd_3472181 : Nat := 396199504979774402126497

theorem tailTrace_3472181 : CollatzResearch.WordTrace tailWord_3472181 prefixEnd_3472181 396199504979774402126497 := by
  unfold tailWord_3472181
  simp only [CollatzResearch.WordTrace]
  refine ⟨126640845033888713148664397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84427230022592475432442931 126640845033888713148664397)
  ·
    refine ⟨47490316887708267430749149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126640845033888713148664397 47490316887708267430749149)
    ·
      refine ⟨17808868832890600286530931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47490316887708267430749149 17808868832890600286530931)
      ·
        refine ⟨26713303249335900429796397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17808868832890600286530931 26713303249335900429796397)
        ·
          refine ⟨10017488718500962661173649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26713303249335900429796397 10017488718500962661173649)
          ·
            refine ⟨7513116538875721995880237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10017488718500962661173649 7513116538875721995880237)
            ·
              refine ⟨2817418702078395748455089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7513116538875721995880237 2817418702078395748455089)
              ·
                refine ⟨2113064026558796811341317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2817418702078395748455089 2113064026558796811341317)
                ·
                  refine ⟨396199504979774402126497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113064026558796811341317 396199504979774402126497)
                  ·
                    rfl

theorem cell22_3472181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_3472181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472181 prefixEnd_3472181 := by exact prefixLift 3472181
  have htrace : WordTrace (prefixWord ++ tailWord_3472181) baseStart_3472181 baseEnd_3472181 := by
    simpa [prefixWord, tailWord_3472181, baseEnd_3472181] using wordTrace_append hprefix tailTrace_3472181
  have hstable : (prefixWord ++ tailWord_3472181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472181).length < 2 ^ (prefixWord ++ tailWord_3472181).sum := by decide
  have hdescent : baseEnd_3472181 < baseStart_3472181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472241 : List Nat := [1, 2, 2, 2, 1, 5, 1, 4, 1, 3]
def baseStart_3472241 : Nat := 118140960795 + 3472241 * 2 ^ 59
def prefixEnd_3472241 : Nat := 4983230072969 + 3 ^ 40 * 3472241 * 2
def baseEnd_3472241 : Nat := 1188619054165503049879307

theorem tailTrace_3472241 : CollatzResearch.WordTrace tailWord_3472241 prefixEnd_3472241 1188619054165503049879307 := by
  unfold tailWord_3472241
  simp only [CollatzResearch.WordTrace]
  refine ⟨126643033413671343395848577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84428688942447562263899051 126643033413671343395848577)
  ·
    refine ⟨94982275060253507546886433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126643033413671343395848577 94982275060253507546886433)
    ·
      refine ⟨71236706295190130660164825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94982275060253507546886433 71236706295190130660164825)
      ·
        refine ⟨53427529721392597995123619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71236706295190130660164825 53427529721392597995123619)
        ·
          refine ⟨80141294582088896992685429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53427529721392597995123619 80141294582088896992685429)
          ·
            refine ⟨7513246367070834093064259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80141294582088896992685429 7513246367070834093064259)
            ·
              refine ⟨11269869550606251139596389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7513246367070834093064259 11269869550606251139596389)
              ·
                refine ⟨2113100540738672088674323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11269869550606251139596389 2113100540738672088674323)
                ·
                  refine ⟨3169650811108008133011485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113100540738672088674323 3169650811108008133011485)
                  ·
                    refine ⟨1188619054165503049879307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3169650811108008133011485 1188619054165503049879307)
                    ·
                      rfl

theorem cell22_3472241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_3472241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472241 prefixEnd_3472241 := by exact prefixLift 3472241
  have htrace : WordTrace (prefixWord ++ tailWord_3472241) baseStart_3472241 baseEnd_3472241 := by
    simpa [prefixWord, tailWord_3472241, baseEnd_3472241] using wordTrace_append hprefix tailTrace_3472241
  have hstable : (prefixWord ++ tailWord_3472241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472241).length < 2 ^ (prefixWord ++ tailWord_3472241).sum := by decide
  have hdescent : baseEnd_3472241 < baseStart_3472241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472267 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 3, 4]
def baseStart_3472267 : Nat := 118140960795 + 3472267 * 2 ^ 59
def prefixEnd_3472267 : Nat := 4983230072969 + 3 ^ 40 * 3472267 * 2
def baseEnd_3472267 : Nat := 1188627954496847648729227

theorem tailTrace_3472267 : CollatzResearch.WordTrace tailWord_3472267 prefixEnd_3472267 1188627954496847648729227 := by
  unfold tailWord_3472267
  simp only [CollatzResearch.WordTrace]
  refine ⟨126643981711577149836295055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84429321141051433224196703 126643981711577149836295055)
  ·
    refine ⟨189965972567365724754442583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126643981711577149836295055 189965972567365724754442583)
    ·
      refine ⟨284948958851048587131663875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189965972567365724754442583 284948958851048587131663875)
      ·
        refine ⟨427423438276572880697495813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284948958851048587131663875 427423438276572880697495813)
        ·
          refine ⟨80141894676857415130780465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 427423438276572880697495813 80141894676857415130780465)
          ·
            refine ⟨60106421007643061348085349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80141894676857415130780465 60106421007643061348085349)
            ·
              refine ⟨11269953938933074002766003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60106421007643061348085349 11269953938933074002766003)
              ·
                refine ⟨16904930908399611004149005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11269953938933074002766003 16904930908399611004149005)
                ·
                  refine ⟨6339349090649854126555877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16904930908399611004149005 6339349090649854126555877)
                  ·
                    refine ⟨1188627954496847648729227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6339349090649854126555877 1188627954496847648729227)
                    ·
                      rfl

theorem cell22_3472267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_3472267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472267 prefixEnd_3472267 := by exact prefixLift 3472267
  have htrace : WordTrace (prefixWord ++ tailWord_3472267) baseStart_3472267 baseEnd_3472267 := by
    simpa [prefixWord, tailWord_3472267, baseEnd_3472267] using wordTrace_append hprefix tailTrace_3472267
  have hstable : (prefixWord ++ tailWord_3472267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472267).length < 2 ^ (prefixWord ++ tailWord_3472267).sum := by decide
  have hdescent : baseEnd_3472267 < baseStart_3472267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472312 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_3472312 : Nat := 118140960795 + 3472312 * 2 ^ 59
def prefixEnd_3472312 : Nat := 4983230072969 + 3 ^ 40 * 3472312 * 2
def baseEnd_3472312 : Nat := 1188643358916482531354089

theorem tailTrace_3472312 : CollatzResearch.WordTrace tailWord_3472312 prefixEnd_3472312 1188643358916482531354089 := by
  unfold tailWord_3472312
  simp only [CollatzResearch.WordTrace]
  refine ⟨63322811498207061260841595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84430415330942748347788793 63322811498207061260841595)
  ·
    refine ⟨94984217247310591891262393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63322811498207061260841595 94984217247310591891262393)
    ·
      refine ⟨71238162935482943918446795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94984217247310591891262393 71238162935482943918446795)
      ·
        refine ⟨106857244403224415877670193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71238162935482943918446795 106857244403224415877670193)
        ·
          refine ⟨80142933302418311908252645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106857244403224415877670193 80142933302418311908252645)
          ·
            refine ⟨15026799994203433482797371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80142933302418311908252645 15026799994203433482797371)
            ·
              refine ⟨22540199991305150224196057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15026799994203433482797371 22540199991305150224196057)
              ·
                refine ⟨16905149993478862668147043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22540199991305150224196057 16905149993478862668147043)
                ·
                  refine ⟨25357724990218294002220565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16905149993478862668147043 25357724990218294002220565)
                  ·
                    refine ⟨1188643358916482531354089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25357724990218294002220565 1188643358916482531354089)
                    ·
                      rfl

theorem cell22_3472312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_3472312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472312 prefixEnd_3472312 := by exact prefixLift 3472312
  have htrace : WordTrace (prefixWord ++ tailWord_3472312) baseStart_3472312 baseEnd_3472312 := by
    simpa [prefixWord, tailWord_3472312, baseEnd_3472312] using wordTrace_append hprefix tailTrace_3472312
  have hstable : (prefixWord ++ tailWord_3472312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472312).length < 2 ^ (prefixWord ++ tailWord_3472312).sum := by decide
  have hdescent : baseEnd_3472312 < baseStart_3472312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472326 : List Nat := [6, 1, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3472326 : Nat := 118140960795 + 3472326 * 2 ^ 59
def prefixEnd_3472326 : Nat := 4983230072969 + 3 ^ 40 * 3472326 * 2
def baseEnd_3472326 : Nat := 1188648151402591161504047

theorem tailTrace_3472326 : CollatzResearch.WordTrace tailWord_3472326 prefixEnd_3472326 1188648151402591161504047 := by
  unfold tailWord_3472326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957691675573856341021651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84430755745575601941795221 3957691675573856341021651)
  ·
    refine ⟨5936537513360784511532477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3957691675573856341021651 5936537513360784511532477)
    ·
      refine ⟨2226201567510294191824679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5936537513360784511532477 2226201567510294191824679)
      ·
        refine ⟨3339302351265441287737019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226201567510294191824679 3339302351265441287737019)
        ·
          refine ⟨5008953526898161931605529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339302351265441287737019 5008953526898161931605529)
          ·
            refine ⟨3756715145173621448704147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5008953526898161931605529 3756715145173621448704147)
            ·
              refine ⟨5635072717760432173056221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756715145173621448704147 5635072717760432173056221)
              ·
                refine ⟨2113152269160162064896083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5635072717760432173056221 2113152269160162064896083)
                ·
                  refine ⟨3169728403740243097344125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2113152269160162064896083 3169728403740243097344125)
                  ·
                    refine ⟨1188648151402591161504047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3169728403740243097344125 1188648151402591161504047)
                    ·
                      rfl

theorem cell22_3472326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3472326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472326 prefixEnd_3472326 := by exact prefixLift 3472326
  have htrace : WordTrace (prefixWord ++ tailWord_3472326) baseStart_3472326 baseEnd_3472326 := by
    simpa [prefixWord, tailWord_3472326, baseEnd_3472326] using wordTrace_append hprefix tailTrace_3472326
  have hstable : (prefixWord ++ tailWord_3472326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472326).length < 2 ^ (prefixWord ++ tailWord_3472326).sum := by decide
  have hdescent : baseEnd_3472326 < baseStart_3472326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472387 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 6, 5]
def baseStart_3472387 : Nat := 118140960795 + 3472387 * 2 ^ 59
def prefixEnd_3472387 : Nat := 4983230072969 + 3 ^ 40 * 3472387 * 2
def baseEnd_3472387 : Nat := 1188669032949207335728859

theorem tailTrace_3472387 : CollatzResearch.WordTrace tailWord_3472387 prefixEnd_3472387 1188669032949207335728859 := by
  unfold tailWord_3472387
  simp only [CollatzResearch.WordTrace]
  refine ⟨126648358471142410330663415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84432238980761606887108943 126648358471142410330663415)
  ·
    refine ⟨189972537706713615495995123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126648358471142410330663415 189972537706713615495995123)
    ·
      refine ⟨284958806560070423243992685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189972537706713615495995123 284958806560070423243992685)
      ·
        refine ⟨106859552460026408716497257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284958806560070423243992685 106859552460026408716497257)
        ·
          refine ⟨80144664345019806537372943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106859552460026408716497257 80144664345019806537372943)
          ·
            refine ⟨120216996517529709806059415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80144664345019806537372943 120216996517529709806059415)
            ·
              refine ⟨180325494776294564709089123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120216996517529709806059415 180325494776294564709089123)
              ·
                refine ⟨270488242164441847063633685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180325494776294564709089123 270488242164441847063633685)
                ·
                  refine ⟨12679136351458211581107829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270488242164441847063633685 12679136351458211581107829)
                  ·
                    refine ⟨1188669032949207335728859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12679136351458211581107829 1188669032949207335728859)
                    ·
                      rfl

theorem cell22_3472387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_3472387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472387 prefixEnd_3472387 := by exact prefixLift 3472387
  have htrace : WordTrace (prefixWord ++ tailWord_3472387) baseStart_3472387 baseEnd_3472387 := by
    simpa [prefixWord, tailWord_3472387, baseEnd_3472387] using wordTrace_append hprefix tailTrace_3472387
  have hstable : (prefixWord ++ tailWord_3472387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472387).length < 2 ^ (prefixWord ++ tailWord_3472387).sum := by decide
  have hdescent : baseEnd_3472387 < baseStart_3472387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472419 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 3, 4]
def baseStart_3472419 : Nat := 118140960795 + 3472419 * 2 ^ 59
def prefixEnd_3472419 : Nat := 4983230072969 + 3 ^ 40 * 3472419 * 2
def baseEnd_3472419 : Nat := 1188679987203169918928761

theorem tailTrace_3472419 : CollatzResearch.WordTrace tailWord_3472419 prefixEnd_3472419 1188679987203169918928761 := by
  unfold tailWord_3472419
  simp only [CollatzResearch.WordTrace]
  refine ⟨126649525607026479795828311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84433017071350986530552207 126649525607026479795828311)
  ·
    refine ⟨189974288410539719693742467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126649525607026479795828311 189974288410539719693742467)
    ·
      refine ⟨284961432615809579540613701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189974288410539719693742467 284961432615809579540613701)
      ·
        refine ⟨53430268615464296163865069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284961432615809579540613701 53430268615464296163865069)
        ·
          refine ⟨20036350730799111061449401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53430268615464296163865069 20036350730799111061449401)
          ·
            refine ⟨15027263048099333296087051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20036350730799111061449401 15027263048099333296087051)
            ·
              refine ⟨22540894572148999944130577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15027263048099333296087051 22540894572148999944130577)
              ·
                refine ⟨16905670929111749958097933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22540894572148999944130577 16905670929111749958097933)
                ·
                  refine ⟨6339626598416906234286725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16905670929111749958097933 6339626598416906234286725)
                  ·
                    refine ⟨1188679987203169918928761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6339626598416906234286725 1188679987203169918928761)
                    ·
                      rfl

theorem cell22_3472419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_3472419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472419 prefixEnd_3472419 := by exact prefixLift 3472419
  have htrace : WordTrace (prefixWord ++ tailWord_3472419) baseStart_3472419 baseEnd_3472419 := by
    simpa [prefixWord, tailWord_3472419, baseEnd_3472419] using wordTrace_append hprefix tailTrace_3472419
  have hstable : (prefixWord ++ tailWord_3472419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472419).length < 2 ^ (prefixWord ++ tailWord_3472419).sum := by decide
  have hdescent : baseEnd_3472419 < baseStart_3472419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472434 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_3472434 : Nat := 118140960795 + 3472434 * 2 ^ 59
def prefixEnd_3472434 : Nat := 4983230072969 + 3 ^ 40 * 3472434 * 2
def baseEnd_3472434 : Nat := 396228374003238293267905

theorem tailTrace_3472434 : CollatzResearch.WordTrace tailWord_3472434 prefixEnd_3472434 396228374003238293267905 := by
  unfold tailWord_3472434
  simp only [CollatzResearch.WordTrace]
  refine ⟨31662518175493034339406089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84433381801314758238416237 31662518175493034339406089)
  ·
    refine ⟨23746888631619775754554567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31662518175493034339406089 23746888631619775754554567)
    ·
      refine ⟨35620332947429663631831851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23746888631619775754554567 35620332947429663631831851)
      ·
        refine ⟨53430499421144495447747777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35620332947429663631831851 53430499421144495447747777)
        ·
          refine ⟨40072874565858371585810833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53430499421144495447747777 40072874565858371585810833)
          ·
            refine ⟨30054655924393778689358125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40072874565858371585810833 30054655924393778689358125)
            ·
              refine ⟨11270495971647667008509297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30054655924393778689358125 11270495971647667008509297)
              ·
                refine ⟨8452871978735750256381973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11270495971647667008509297 8452871978735750256381973)
                ·
                  refine ⟨396228374003238293267905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8452871978735750256381973 396228374003238293267905)
                  ·
                    rfl

theorem cell22_3472434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_3472434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472434 prefixEnd_3472434 := by exact prefixLift 3472434
  have htrace : WordTrace (prefixWord ++ tailWord_3472434) baseStart_3472434 baseEnd_3472434 := by
    simpa [prefixWord, tailWord_3472434, baseEnd_3472434] using wordTrace_append hprefix tailTrace_3472434
  have hstable : (prefixWord ++ tailWord_3472434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472434).length < 2 ^ (prefixWord ++ tailWord_3472434).sum := by decide
  have hdescent : baseEnd_3472434 < baseStart_3472434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472451 : List Nat := [1, 1, 1, 3, 1, 2, 6, 3, 4]
def baseStart_3472451 : Nat := 118140960795 + 3472451 * 2 ^ 59
def prefixEnd_3472451 : Nat := 4983230072969 + 3 ^ 40 * 3472451 * 2
def baseEnd_3472451 : Nat := 396230313819044167376221

theorem tailTrace_3472451 : CollatzResearch.WordTrace tailWord_3472451 prefixEnd_3472451 396230313819044167376221 := by
  unfold tailWord_3472451
  simp only [CollatzResearch.WordTrace]
  refine ⟨126650692742910549260993207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84433795161940366173995471 126650692742910549260993207)
  ·
    refine ⟨189976039114365823891489811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126650692742910549260993207 189976039114365823891489811)
    ·
      refine ⟨284964058671548735837234717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189976039114365823891489811 284964058671548735837234717)
      ·
        refine ⟨106861522001830775938963019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284964058671548735837234717 106861522001830775938963019)
        ·
          refine ⟨160292283002746163908444529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106861522001830775938963019 160292283002746163908444529)
          ·
            refine ⟨120219212252059622931333397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160292283002746163908444529 120219212252059622931333397)
            ·
              refine ⟨5635275574315294824906253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120219212252059622931333397 5635275574315294824906253)
              ·
                refine ⟨2113228340368235559339845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5635275574315294824906253 2113228340368235559339845)
                ·
                  refine ⟨396230313819044167376221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113228340368235559339845 396230313819044167376221)
                  ·
                    rfl

theorem cell22_3472451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 4].length) (baseStart_3472451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472451 prefixEnd_3472451 := by exact prefixLift 3472451
  have htrace : WordTrace (prefixWord ++ tailWord_3472451) baseStart_3472451 baseEnd_3472451 := by
    simpa [prefixWord, tailWord_3472451, baseEnd_3472451] using wordTrace_append hprefix tailTrace_3472451
  have hstable : (prefixWord ++ tailWord_3472451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472451).length < 2 ^ (prefixWord ++ tailWord_3472451).sum := by decide
  have hdescent : baseEnd_3472451 < baseStart_3472451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472464 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 2, 4]
def baseStart_3472464 : Nat := 118140960795 + 3472464 * 2 ^ 59
def prefixEnd_3472464 : Nat := 4983230072969 + 3 ^ 40 * 3472464 * 2
def baseEnd_3472464 : Nat := 1188695391622804801553623

theorem tailTrace_3472464 : CollatzResearch.WordTrace tailWord_3472464 prefixEnd_3472464 1188695391622804801553623 := by
  unfold tailWord_3472464
  simp only [CollatzResearch.WordTrace]
  refine ⟨63325583445931726240608223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84434111261242301654144297 63325583445931726240608223)
  ·
    refine ⟨94988375168897589360912335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63325583445931726240608223 94988375168897589360912335)
    ·
      refine ⟨142482562753346384041368503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94988375168897589360912335 142482562753346384041368503)
      ·
        refine ⟨213723844130019576062052755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142482562753346384041368503 213723844130019576062052755)
        ·
          refine ⟨320585766195029364093079133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213723844130019576062052755 320585766195029364093079133)
          ·
            refine ⟨120219662323136011534904675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320585766195029364093079133 120219662323136011534904675)
            ·
              refine ⟨180329493484704017302357013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120219662323136011534904675 180329493484704017302357013)
              ·
                refine ⟨8452945007095500811047985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180329493484704017302357013 8452945007095500811047985)
                ·
                  refine ⟨6339708755321625608285989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8452945007095500811047985 6339708755321625608285989)
                  ·
                    refine ⟨1188695391622804801553623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6339708755321625608285989 1188695391622804801553623)
                    ·
                      rfl

theorem cell22_3472464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_3472464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472464 prefixEnd_3472464 := by exact prefixLift 3472464
  have htrace : WordTrace (prefixWord ++ tailWord_3472464) baseStart_3472464 baseEnd_3472464 := by
    simpa [prefixWord, tailWord_3472464, baseEnd_3472464] using wordTrace_append hprefix tailTrace_3472464
  have hstable : (prefixWord ++ tailWord_3472464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472464).length < 2 ^ (prefixWord ++ tailWord_3472464).sum := by decide
  have hdescent : baseEnd_3472464 < baseStart_3472464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472541 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 5]
def baseStart_3472541 : Nat := 118140960795 + 3472541 * 2 ^ 59
def prefixEnd_3472541 : Nat := 4983230072969 + 3 ^ 40 * 3472541 * 2
def baseEnd_3472541 : Nat := 396240583432134089126129

theorem tailTrace_3472541 : CollatzResearch.WordTrace tailWord_3472541 prefixEnd_3472541 396240583432134089126129 := by
  unfold tailWord_3472541
  simp only [CollatzResearch.WordTrace]
  refine ⟨126653975312584494631769477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84435983541722996421179651 126653975312584494631769477)
  ·
    refine ⟨23747620371109592743456777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126653975312584494631769477 23747620371109592743456777)
    ·
      refine ⟨17810715278332194557592583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23747620371109592743456777 17810715278332194557592583)
      ·
        refine ⟨26716072917498291836388875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17810715278332194557592583 26716072917498291836388875)
        ·
          refine ⟨40074109376247437754583313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26716072917498291836388875 40074109376247437754583313)
          ·
            refine ⟨30055582032185578315937485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40074109376247437754583313 30055582032185578315937485)
            ·
              refine ⟨11270843262069591868476557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30055582032185578315937485 11270843262069591868476557)
              ·
                refine ⟨4226566223276096950678709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11270843262069591868476557 4226566223276096950678709)
                ·
                  refine ⟨396240583432134089126129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4226566223276096950678709 396240583432134089126129)
                  ·
                    rfl

theorem cell22_3472541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_3472541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472541 prefixEnd_3472541 := by exact prefixLift 3472541
  have htrace : WordTrace (prefixWord ++ tailWord_3472541) baseStart_3472541 baseEnd_3472541 := by
    simpa [prefixWord, tailWord_3472541, baseEnd_3472541] using wordTrace_append hprefix tailTrace_3472541
  have hstable : (prefixWord ++ tailWord_3472541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472541).length < 2 ^ (prefixWord ++ tailWord_3472541).sum := by decide
  have hdescent : baseEnd_3472541 < baseStart_3472541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472601 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 6, 3]
def baseStart_3472601 : Nat := 118140960795 + 3472601 * 2 ^ 59
def prefixEnd_3472601 : Nat := 4983230072969 + 3 ^ 40 * 3472601 * 2
def baseEnd_3472601 : Nat := 1188742289522582110878203

theorem tailTrace_3472601 : CollatzResearch.WordTrace tailWord_3472601 prefixEnd_3472601 1188742289522582110878203 := by
  unfold tailWord_3472601
  simp only [CollatzResearch.WordTrace]
  refine ⟨126656163692367124878953657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84437442461578083252635771 126656163692367124878953657)
  ·
    refine ⟨94992122769275343659215243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126656163692367124878953657 94992122769275343659215243)
    ·
      refine ⟨142488184153913015488822865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94992122769275343659215243 142488184153913015488822865)
      ·
        refine ⟨106866138115434761616617149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142488184153913015488822865 106866138115434761616617149)
        ·
          refine ⟨40074801793288035606231431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106866138115434761616617149 40074801793288035606231431)
          ·
            refine ⟨60112202689932053409347147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40074801793288035606231431 60112202689932053409347147)
            ·
              refine ⟨90168304034898080114020721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60112202689932053409347147 90168304034898080114020721)
              ·
                refine ⟨67626228026173560085515541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90168304034898080114020721 67626228026173560085515541)
                ·
                  refine ⟨3169979438726885629008541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 67626228026173560085515541 3169979438726885629008541)
                  ·
                    refine ⟨1188742289522582110878203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3169979438726885629008541 1188742289522582110878203)
                    ·
                      rfl

theorem cell22_3472601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_3472601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472601 prefixEnd_3472601 := by exact prefixLift 3472601
  have htrace : WordTrace (prefixWord ++ tailWord_3472601) baseStart_3472601 baseEnd_3472601 := by
    simpa [prefixWord, tailWord_3472601, baseEnd_3472601] using wordTrace_append hprefix tailTrace_3472601
  have hstable : (prefixWord ++ tailWord_3472601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472601).length < 2 ^ (prefixWord ++ tailWord_3472601).sum := by decide
  have hdescent : baseEnd_3472601 < baseStart_3472601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472616 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3472616 : Nat := 118140960795 + 3472616 * 2 ^ 59
def prefixEnd_3472616 : Nat := 4983230072969 + 3 ^ 40 * 3472616 * 2
def baseEnd_3472616 : Nat := 1188747424329127071753157

theorem tailTrace_3472616 : CollatzResearch.WordTrace tailWord_3472616 prefixEnd_3472616 1188747424329127071753157 := by
  unfold tailWord_3472616
  simp only [CollatzResearch.WordTrace]
  refine ⟨63328355393656391220374851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84437807191541854960499801 63328355393656391220374851)
  ·
    refine ⟨94992533090484586830562277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63328355393656391220374851 94992533090484586830562277)
    ·
      refine ⟨17811099954465860030730427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94992533090484586830562277 17811099954465860030730427)
      ·
        refine ⟨26716649931698790046095641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17811099954465860030730427 26716649931698790046095641)
        ·
          refine ⟨20037487448774092534571731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26716649931698790046095641 20037487448774092534571731)
          ·
            refine ⟨30056231173161138801857597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20037487448774092534571731 30056231173161138801857597)
            ·
              refine ⟨11271086689935427050696599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30056231173161138801857597 11271086689935427050696599)
              ·
                refine ⟨16906630034903140576044899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271086689935427050696599 16906630034903140576044899)
                ·
                  refine ⟨25359945052354710864067349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16906630034903140576044899 25359945052354710864067349)
                  ·
                    refine ⟨1188747424329127071753157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25359945052354710864067349 1188747424329127071753157)
                    ·
                      rfl

theorem cell22_3472616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3472616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472616 prefixEnd_3472616 := by exact prefixLift 3472616
  have htrace : WordTrace (prefixWord ++ tailWord_3472616) baseStart_3472616 baseEnd_3472616 := by
    simpa [prefixWord, tailWord_3472616, baseEnd_3472616] using wordTrace_append hprefix tailTrace_3472616
  have hstable : (prefixWord ++ tailWord_3472616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472616).length < 2 ^ (prefixWord ++ tailWord_3472616).sum := by decide
  have hdescent : baseEnd_3472616 < baseStart_3472616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472663 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 3, 3]
def baseStart_3472663 : Nat := 118140960795 + 3472663 * 2 ^ 59
def prefixEnd_3472663 : Nat := 4983230072969 + 3 ^ 40 * 3472663 * 2
def baseEnd_3472663 : Nat := 1188763513389634615828013

theorem tailTrace_3472663 : CollatzResearch.WordTrace tailWord_3472663 prefixEnd_3472663 1188763513389634615828013 := by
  unfold tailWord_3472663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126658425018142509467710643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84438950012095006311807095 126658425018142509467710643)
  ·
    refine ⟨189987637527213764201565965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126658425018142509467710643 189987637527213764201565965)
    ·
      refine ⟨71245364072705161575587237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189987637527213764201565965 71245364072705161575587237)
      ·
        refine ⟨13358505763632217795422607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71245364072705161575587237 13358505763632217795422607)
        ·
          refine ⟨20037758645448326693133911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358505763632217795422607 20037758645448326693133911)
          ·
            refine ⟨30056637968172490039700867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20037758645448326693133911 30056637968172490039700867)
            ·
              refine ⟨45084956952258735059551301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30056637968172490039700867 45084956952258735059551301)
              ·
                refine ⟨8453429428548512823665869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45084956952258735059551301 8453429428548512823665869)
                ·
                  refine ⟨3170036035705692308874701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8453429428548512823665869 3170036035705692308874701)
                  ·
                    refine ⟨1188763513389634615828013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3170036035705692308874701 1188763513389634615828013)
                    ·
                      rfl

theorem cell22_3472663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_3472663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472663 prefixEnd_3472663 := by exact prefixLift 3472663
  have htrace : WordTrace (prefixWord ++ tailWord_3472663) baseStart_3472663 baseEnd_3472663 := by
    simpa [prefixWord, tailWord_3472663, baseEnd_3472663] using wordTrace_append hprefix tailTrace_3472663
  have hstable : (prefixWord ++ tailWord_3472663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472663).length < 2 ^ (prefixWord ++ tailWord_3472663).sum := by decide
  have hdescent : baseEnd_3472663 < baseStart_3472663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472676 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 9]
def baseStart_3472676 : Nat := 118140960795 + 3472676 * 2 ^ 59
def prefixEnd_3472676 : Nat := 4983230072969 + 3 ^ 40 * 3472676 * 2
def baseEnd_3472676 : Nat := 396255987851768971750991

theorem tailTrace_3472676 : CollatzResearch.WordTrace tailWord_3472676 prefixEnd_3472676 396255987851768971750991 := by
  unfold tailWord_3472676
  simp only [CollatzResearch.WordTrace]
  refine ⟨63329449583547706343966941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84439266111396941791955921 63329449583547706343966941)
  ·
    refine ⟨23748543593830389878987603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63329449583547706343966941 23748543593830389878987603)
    ·
      refine ⟨35622815390745584818481405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23748543593830389878987603 35622815390745584818481405)
      ·
        refine ⟨13358555771529594306930527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35622815390745584818481405 13358555771529594306930527)
        ·
          refine ⟨20037833657294391460395791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358555771529594306930527 20037833657294391460395791)
          ·
            refine ⟨30056750485941587190593687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20037833657294391460395791 30056750485941587190593687)
            ·
              refine ⟨45085125728912380785890531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30056750485941587190593687 45085125728912380785890531)
              ·
                refine ⟨67627688593368571178835797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45085125728912380785890531 67627688593368571178835797)
                ·
                  refine ⟨396255987851768971750991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67627688593368571178835797 396255987851768971750991)
                  ·
                    rfl

theorem cell22_3472676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_3472676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472676 prefixEnd_3472676 := by exact prefixLift 3472676
  have htrace : WordTrace (prefixWord ++ tailWord_3472676) baseStart_3472676 baseEnd_3472676 := by
    simpa [prefixWord, tailWord_3472676, baseEnd_3472676] using wordTrace_append hprefix tailTrace_3472676
  have hstable : (prefixWord ++ tailWord_3472676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472676).length < 2 ^ (prefixWord ++ tailWord_3472676).sum := by decide
  have hdescent : baseEnd_3472676 < baseStart_3472676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472697 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 3, 3]
def baseStart_3472697 : Nat := 118140960795 + 3472697 * 2 ^ 59
def prefixEnd_3472697 : Nat := 4983230072969 + 3 ^ 40 * 3472697 * 2
def baseEnd_3472697 : Nat := 1188775152284469860477909

theorem tailTrace_3472697 : CollatzResearch.WordTrace tailWord_3472697 prefixEnd_3472697 1188775152284469860477909 := by
  unfold tailWord_3472697
  simp only [CollatzResearch.WordTrace]
  refine ⟨126659665100019333274448345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84439776733346222182965563 126659665100019333274448345)
  ·
    refine ⟨94994748825014499955836259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126659665100019333274448345 94994748825014499955836259)
    ·
      refine ⟨142492123237521749933754389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94994748825014499955836259 142492123237521749933754389)
      ·
        refine ⟨6679318276758832028144737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142492123237521749933754389 6679318276758832028144737)
        ·
          refine ⟨5009488707569124021108553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6679318276758832028144737 5009488707569124021108553)
          ·
            refine ⟨3757116530676843015831415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5009488707569124021108553 3757116530676843015831415)
            ·
              refine ⟨5635674796015264523747123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757116530676843015831415 5635674796015264523747123)
              ·
                refine ⟨8453512194022896785620685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5635674796015264523747123 8453512194022896785620685)
                ·
                  refine ⟨3170067072758586294607757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8453512194022896785620685 3170067072758586294607757)
                  ·
                    refine ⟨1188775152284469860477909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3170067072758586294607757 1188775152284469860477909)
                    ·
                      rfl

theorem cell22_3472697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_3472697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472697 prefixEnd_3472697 := by exact prefixLift 3472697
  have htrace : WordTrace (prefixWord ++ tailWord_3472697) baseStart_3472697 baseEnd_3472697 := by
    simpa [prefixWord, tailWord_3472697, baseEnd_3472697] using wordTrace_append hprefix tailTrace_3472697
  have hstable : (prefixWord ++ tailWord_3472697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472697).length < 2 ^ (prefixWord ++ tailWord_3472697).sum := by decide
  have hdescent : baseEnd_3472697 < baseStart_3472697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472721 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 8]
def baseStart_3472721 : Nat := 118140960795 + 3472721 * 2 ^ 59
def prefixEnd_3472721 : Nat := 4983230072969 + 3 ^ 40 * 3472721 * 2
def baseEnd_3472721 : Nat := 396261122658313932625945

theorem tailTrace_3472721 : CollatzResearch.WordTrace tailWord_3472721 prefixEnd_3472721 396261122658313932625945 := by
  unfold tailWord_3472721
  simp only [CollatzResearch.WordTrace]
  refine ⟨126660540451932385373322017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84440360301288256915548011 126660540451932385373322017)
  ·
    refine ⟨94995405338949289029991513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126660540451932385373322017 94995405338949289029991513)
    ·
      refine ⟨71246554004211966772493635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94995405338949289029991513 71246554004211966772493635)
      ·
        refine ⟨106869831006317950158740453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71246554004211966772493635 106869831006317950158740453)
        ·
          refine ⟨20038093313684615654763835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106869831006317950158740453 20038093313684615654763835)
          ·
            refine ⟨30057139970526923482145753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20038093313684615654763835 30057139970526923482145753)
            ·
              refine ⟨22542854977895192611609315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30057139970526923482145753 22542854977895192611609315)
              ·
                refine ⟨33814282466842788917413973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22542854977895192611609315 33814282466842788917413973)
                ·
                  refine ⟨396261122658313932625945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33814282466842788917413973 396261122658313932625945)
                  ·
                    rfl

theorem cell22_3472721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_3472721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472721 prefixEnd_3472721 := by exact prefixLift 3472721
  have htrace : WordTrace (prefixWord ++ tailWord_3472721) baseStart_3472721 baseEnd_3472721 := by
    simpa [prefixWord, tailWord_3472721, baseEnd_3472721] using wordTrace_append hprefix tailTrace_3472721
  have hstable : (prefixWord ++ tailWord_3472721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472721).length < 2 ^ (prefixWord ++ tailWord_3472721).sum := by decide
  have hdescent : baseEnd_3472721 < baseStart_3472721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472753 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 4, 3]
def baseStart_3472753 : Nat := 118140960795 + 3472753 * 2 ^ 59
def prefixEnd_3472753 : Nat := 4983230072969 + 3 ^ 40 * 3472753 * 2
def baseEnd_3472753 : Nat := 1188794322228904381077737

theorem tailTrace_3472753 : CollatzResearch.WordTrace tailWord_3472753 prefixEnd_3472753 1188794322228904381077737 := by
  unfold tailWord_3472753
  simp only [CollatzResearch.WordTrace]
  refine ⟨126661707587816454838486913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84441138391877636558991275 126661707587816454838486913)
  ·
    refine ⟨94996280690862341128865185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126661707587816454838486913 94996280690862341128865185)
    ·
      refine ⟨71247210518146755846648889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94996280690862341128865185 71247210518146755846648889)
      ·
        refine ⟨53435407888610066884986667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71247210518146755846648889 53435407888610066884986667)
        ·
          refine ⟨80153111832915100327480001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53435407888610066884986667 80153111832915100327480001)
          ·
            refine ⟨60114833874686325245610001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80153111832915100327480001 60114833874686325245610001)
            ·
              refine ⟨45086125406014743934207501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60114833874686325245610001 45086125406014743934207501)
              ·
                refine ⟨16907297027255528975327813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45086125406014743934207501 16907297027255528975327813)
                ·
                  refine ⟨3170118192610411682873965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16907297027255528975327813 3170118192610411682873965)
                  ·
                    refine ⟨1188794322228904381077737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3170118192610411682873965 1188794322228904381077737)
                    ·
                      rfl

theorem cell22_3472753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_3472753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472753 prefixEnd_3472753 := by exact prefixLift 3472753
  have htrace : WordTrace (prefixWord ++ tailWord_3472753) baseStart_3472753 baseEnd_3472753 := by
    simpa [prefixWord, tailWord_3472753, baseEnd_3472753] using wordTrace_append hprefix tailTrace_3472753
  have hstable : (prefixWord ++ tailWord_3472753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472753).length < 2 ^ (prefixWord ++ tailWord_3472753).sum := by decide
  have hdescent : baseEnd_3472753 < baseStart_3472753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472933 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3472933 : Nat := 118140960795 + 3472933 * 2 ^ 59
def prefixEnd_3472933 : Nat := 4983230072969 + 3 ^ 40 * 3472933 * 2
def baseEnd_3472933 : Nat := 1188855939907443911577185

theorem tailTrace_3472933 : CollatzResearch.WordTrace tailWord_3472933 prefixEnd_3472933 1188855939907443911577185 := by
  unfold tailWord_3472933
  simp only [CollatzResearch.WordTrace]
  refine ⟨126668272727164345580039453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84445515151442897053359635 126668272727164345580039453)
  ·
    refine ⟨47500602272686629592514795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126668272727164345580039453 47500602272686629592514795)
    ·
      refine ⟨71250903409029944388772193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47500602272686629592514795 71250903409029944388772193)
      ·
        refine ⟨53438177556772458291579145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71250903409029944388772193 53438177556772458291579145)
        ·
          refine ⟨40078633167579343718684359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53438177556772458291579145 40078633167579343718684359)
          ·
            refine ⟨60117949751369015578026539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40078633167579343718684359 60117949751369015578026539)
            ·
              refine ⟨90176924627053523367039809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60117949751369015578026539 90176924627053523367039809)
              ·
                refine ⟨67632693470290142525279857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90176924627053523367039809 67632693470290142525279857)
                ·
                  refine ⟨50724520102717606893959893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67632693470290142525279857 50724520102717606893959893)
                  ·
                    refine ⟨1188855939907443911577185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50724520102717606893959893 1188855939907443911577185)
                    ·
                      rfl

theorem cell22_3472933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3472933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472933 prefixEnd_3472933 := by exact prefixLift 3472933
  have htrace : WordTrace (prefixWord ++ tailWord_3472933) baseStart_3472933 baseEnd_3472933 := by
    simpa [prefixWord, tailWord_3472933, baseEnd_3472933] using wordTrace_append hprefix tailTrace_3472933
  have hstable : (prefixWord ++ tailWord_3472933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472933).length < 2 ^ (prefixWord ++ tailWord_3472933).sum := by decide
  have hdescent : baseEnd_3472933 < baseStart_3472933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472973 : List Nat := [1, 6, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3472973 : Nat := 118140960795 + 3472973 * 2 ^ 59
def prefixEnd_3472973 : Nat := 4983230072969 + 3 ^ 40 * 3472973 * 2
def baseEnd_3472973 : Nat := 1188869632724897140577063

theorem tailTrace_3472973 : CollatzResearch.WordTrace tailWord_3472973 prefixEnd_3472973 1188869632724897140577063 := by
  unfold tailWord_3472973
  simp only [CollatzResearch.WordTrace]
  refine ⟨126669731647019432411495573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84446487764679621607663715 126669731647019432411495573)
  ·
    refine ⟨5937643670954035894288855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126669731647019432411495573 5937643670954035894288855)
    ·
      refine ⟨8906465506431053841433283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5937643670954035894288855 8906465506431053841433283)
      ·
        refine ⟨13359698259646580762149925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8906465506431053841433283 13359698259646580762149925)
        ·
          refine ⟨2504943423683733892903111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13359698259646580762149925 2504943423683733892903111)
          ·
            refine ⟨3757415135525600839354667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504943423683733892903111 3757415135525600839354667)
            ·
              refine ⟨5636122703288401259032001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757415135525600839354667 5636122703288401259032001)
              ·
                refine ⟨4227092027466300944274001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5636122703288401259032001 4227092027466300944274001)
                ·
                  refine ⟨3170319020599725708205501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4227092027466300944274001 3170319020599725708205501)
                  ·
                    refine ⟨1188869632724897140577063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3170319020599725708205501 1188869632724897140577063)
                    ·
                      rfl

theorem cell22_3472973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3472973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472973 prefixEnd_3472973 := by exact prefixLift 3472973
  have htrace : WordTrace (prefixWord ++ tailWord_3472973) baseStart_3472973 baseEnd_3472973 := by
    simpa [prefixWord, tailWord_3472973, baseEnd_3472973] using wordTrace_append hprefix tailTrace_3472973
  have hstable : (prefixWord ++ tailWord_3472973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472973).length < 2 ^ (prefixWord ++ tailWord_3472973).sum := by decide
  have hdescent : baseEnd_3472973 < baseStart_3472973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472980 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 7]
def baseStart_3472980 : Nat := 118140960795 + 3472980 * 2 ^ 59
def prefixEnd_3472980 : Nat := 4983230072969 + 3 ^ 40 * 3472980 * 2
def baseEnd_3472980 : Nat := 396290676322650485217347

theorem tailTrace_3472980 : CollatzResearch.WordTrace tailWord_3472980 prefixEnd_3472980 396290676322650485217347 := by
  unfold tailWord_3472980
  simp only [CollatzResearch.WordTrace]
  refine ⟨63334993478997036303500197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84446657971996048404666929 63334993478997036303500197)
  ·
    refine ⟨11875311277311944306906287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63334993478997036303500197 11875311277311944306906287)
    ·
      refine ⟨17812966915967916460359431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11875311277311944306906287 17812966915967916460359431)
      ·
        refine ⟨26719450373951874690539147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17812966915967916460359431 26719450373951874690539147)
        ·
          refine ⟨40079175560927812035808721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26719450373951874690539147 40079175560927812035808721)
          ·
            refine ⟨30059381670695859026856541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40079175560927812035808721 30059381670695859026856541)
            ·
              refine ⟨11272268126510947135071203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30059381670695859026856541 11272268126510947135071203)
              ·
                refine ⟨16908402189766420702606805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11272268126510947135071203 16908402189766420702606805)
                ·
                  refine ⟨396290676322650485217347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16908402189766420702606805 396290676322650485217347)
                  ·
                    rfl

theorem cell22_3472980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_3472980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472980 prefixEnd_3472980 := by exact prefixLift 3472980
  have htrace : WordTrace (prefixWord ++ tailWord_3472980) baseStart_3472980 baseEnd_3472980 := by
    simpa [prefixWord, tailWord_3472980, baseEnd_3472980] using wordTrace_append hprefix tailTrace_3472980
  have hstable : (prefixWord ++ tailWord_3472980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472980).length < 2 ^ (prefixWord ++ tailWord_3472980).sum := by decide
  have hdescent : baseEnd_3472980 < baseStart_3472980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3472995 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 2, 5]
def baseStart_3472995 : Nat := 118140960795 + 3472995 * 2 ^ 59
def prefixEnd_3472995 : Nat := 4983230072969 + 3 ^ 40 * 3472995 * 2
def baseEnd_3472995 : Nat := 1188877163774496416526995

theorem tailTrace_3472995 : CollatzResearch.WordTrace tailWord_3472995 prefixEnd_3472995 1188877163774496416526995 := by
  unfold tailWord_3472995
  simp only [CollatzResearch.WordTrace]
  refine ⟨126670534052939730168796439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84447022701959820112530959 126670534052939730168796439)
  ·
    refine ⟨190005801079409595253194659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126670534052939730168796439 190005801079409595253194659)
    ·
      refine ⟨285008701619114392879791989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190005801079409595253194659 285008701619114392879791989)
      ·
        refine ⟨26719565776791974332480499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285008701619114392879791989 26719565776791974332480499)
        ·
          refine ⟨40079348665187961498720749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26719565776791974332480499 40079348665187961498720749)
          ·
            refine ⟨15029755749445485562020281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40079348665187961498720749 15029755749445485562020281)
            ·
              refine ⟨11272316812084114171515211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15029755749445485562020281 11272316812084114171515211)
              ·
                refine ⟨16908475218126171257272817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11272316812084114171515211 16908475218126171257272817)
                ·
                  refine ⟨12681356413594628442954613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16908475218126171257272817 12681356413594628442954613)
                  ·
                    refine ⟨1188877163774496416526995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12681356413594628442954613 1188877163774496416526995)
                    ·
                      rfl

theorem cell22_3472995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_3472995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3472995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3472995 prefixEnd_3472995 := by exact prefixLift 3472995
  have htrace : WordTrace (prefixWord ++ tailWord_3472995) baseStart_3472995 baseEnd_3472995 := by
    simpa [prefixWord, tailWord_3472995, baseEnd_3472995] using wordTrace_append hprefix tailTrace_3472995
  have hstable : (prefixWord ++ tailWord_3472995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3472995).length < 2 ^ (prefixWord ++ tailWord_3472995).sum := by decide
  have hdescent : baseEnd_3472995 < baseStart_3472995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3472995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473078 : List Nat := [5, 1, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3473078 : Nat := 118140960795 + 3473078 * 2 ^ 59
def prefixEnd_3473078 : Nat := 4983230072969 + 3 ^ 40 * 3473078 * 2
def baseEnd_3473078 : Nat := 1188905576370711866701741

theorem tailTrace_3473078 : CollatzResearch.WordTrace tailWord_3473078 prefixEnd_3473078 1188905576370711866701741 := by
  unfold tailWord_3473078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917097581977439709004243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84449040874426023562711925 7917097581977439709004243)
  ·
    refine ⟨11875646372966159563506365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7917097581977439709004243 11875646372966159563506365)
    ·
      refine ⟨4453367389862309836314887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11875646372966159563506365 4453367389862309836314887)
      ·
        refine ⟨6680051084793464754472331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4453367389862309836314887 6680051084793464754472331)
        ·
          refine ⟨10020076627190197131708497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680051084793464754472331 10020076627190197131708497)
          ·
            refine ⟨7515057470392647848781373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10020076627190197131708497 7515057470392647848781373)
            ·
              refine ⟨2818146551397242943293015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7515057470392647848781373 2818146551397242943293015)
              ·
                refine ⟨4227219827095864414939523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818146551397242943293015 4227219827095864414939523)
                ·
                  refine ⟨6340829740643796622409285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227219827095864414939523 6340829740643796622409285)
                  ·
                    refine ⟨1188905576370711866701741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6340829740643796622409285 1188905576370711866701741)
                    ·
                      rfl

theorem cell22_3473078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3473078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473078 prefixEnd_3473078 := by exact prefixLift 3473078
  have htrace : WordTrace (prefixWord ++ tailWord_3473078) baseStart_3473078 baseEnd_3473078 := by
    simpa [prefixWord, tailWord_3473078, baseEnd_3473078] using wordTrace_append hprefix tailTrace_3473078
  have hstable : (prefixWord ++ tailWord_3473078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473078).length < 2 ^ (prefixWord ++ tailWord_3473078).sum := by decide
  have hdescent : baseEnd_3473078 < baseStart_3473078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473284 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3473284 : Nat := 118140960795 + 3473284 * 2 ^ 59
def prefixEnd_3473284 : Nat := 4983230072969 + 3 ^ 40 * 3473284 * 2
def baseEnd_3473284 : Nat := 396325364793531998683703

theorem tailTrace_3473284 : CollatzResearch.WordTrace tailWord_3473284 prefixEnd_3473284 396325364793531998683703 := by
  unfold tailWord_3473284
  simp only [CollatzResearch.WordTrace]
  refine ⟨63340537374446366263033453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84454049832595155017377937 63340537374446366263033453)
  ·
    refine ⟨23752701515417387348637545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63340537374446366263033453 23752701515417387348637545)
    ·
      refine ⟨17814526136563040511478159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23752701515417387348637545 17814526136563040511478159)
      ·
        refine ⟨26721789204844560767217239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17814526136563040511478159 26721789204844560767217239)
        ·
          refine ⟨40082683807266841150825859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26721789204844560767217239 40082683807266841150825859)
          ·
            refine ⟨60124025710900261726238789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40082683807266841150825859 60124025710900261726238789)
            ·
              refine ⟨11273254820793799073669773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60124025710900261726238789 11273254820793799073669773)
              ·
                refine ⟨4227470557797674652626165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11273254820793799073669773 4227470557797674652626165)
                ·
                  refine ⟨396325364793531998683703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4227470557797674652626165 396325364793531998683703)
                  ·
                    rfl

theorem cell22_3473284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3473284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473284 prefixEnd_3473284 := by exact prefixLift 3473284
  have htrace : WordTrace (prefixWord ++ tailWord_3473284) baseStart_3473284 baseEnd_3473284 := by
    simpa [prefixWord, tailWord_3473284, baseEnd_3473284] using wordTrace_append hprefix tailTrace_3473284
  have hstable : (prefixWord ++ tailWord_3473284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473284).length < 2 ^ (prefixWord ++ tailWord_3473284).sum := by decide
  have hdescent : baseEnd_3473284 < baseStart_3473284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473312 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 10]
def baseStart_3473312 : Nat := 118140960795 + 3473312 * 2 ^ 59
def prefixEnd_3473312 : Nat := 4983230072969 + 3 ^ 40 * 3473312 * 2
def baseEnd_3473312 : Nat := 396328559784271085450341

theorem tailTrace_3473312 : CollatzResearch.WordTrace tailWord_3473312 prefixEnd_3473312 396328559784271085450341 := by
  unfold tailWord_3473312
  simp only [CollatzResearch.WordTrace]
  refine ⟨63341047996395646654043095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84454730661860862205390793 63341047996395646654043095)
  ·
    refine ⟨95011571994593469981064643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63341047996395646654043095 95011571994593469981064643)
    ·
      refine ⟨142517357991890204971596965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95011571994593469981064643 142517357991890204971596965)
      ·
        refine ⟨26722004623479413432174431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142517357991890204971596965 26722004623479413432174431)
        ·
          refine ⟨40083006935219120148261647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26722004623479413432174431 40083006935219120148261647)
          ·
            refine ⟨60124510402828680222392471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40083006935219120148261647 60124510402828680222392471)
            ·
              refine ⟨90186765604243020333588707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60124510402828680222392471 90186765604243020333588707)
              ·
                refine ⟨135280148406364530500383061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90186765604243020333588707 135280148406364530500383061)
                ·
                  refine ⟨396328559784271085450341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 135280148406364530500383061 396328559784271085450341)
                  ·
                    rfl

theorem cell22_3473312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_3473312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473312 prefixEnd_3473312 := by exact prefixLift 3473312
  have htrace : WordTrace (prefixWord ++ tailWord_3473312) baseStart_3473312 baseEnd_3473312 := by
    simpa [prefixWord, tailWord_3473312, baseEnd_3473312] using wordTrace_append hprefix tailTrace_3473312
  have hstable : (prefixWord ++ tailWord_3473312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473312).length < 2 ^ (prefixWord ++ tailWord_3473312).sum := by decide
  have hdescent : baseEnd_3473312 < baseStart_3473312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473329 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 6]
def baseStart_3473329 : Nat := 118140960795 + 3473329 * 2 ^ 59
def prefixEnd_3473329 : Nat := 4983230072969 + 3 ^ 40 * 3473329 * 2
def baseEnd_3473329 : Nat := 396330499600076959558657

theorem tailTrace_3473329 : CollatzResearch.WordTrace tailWord_3473329 prefixEnd_3473329 396330499600076959558657 := by
  unfold tailWord_3473329
  simp only [CollatzResearch.WordTrace]
  refine ⟨126682716033729705211455041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84455144022486470140970027 126682716033729705211455041)
  ·
    refine ⟨95012037025297278908591281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126682716033729705211455041 95012037025297278908591281)
    ·
      refine ⟨71259027768972959181443461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95012037025297278908591281 71259027768972959181443461)
      ·
        refine ⟨13361067706682429846520649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71259027768972959181443461 13361067706682429846520649)
        ·
          refine ⟨10020800780011822384890487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13361067706682429846520649 10020800780011822384890487)
          ·
            refine ⟨15031201170017733577335731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10020800780011822384890487 15031201170017733577335731)
            ·
              refine ⟨22546801755026600366003597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15031201170017733577335731 22546801755026600366003597)
              ·
                refine ⟨8455050658134975137251349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22546801755026600366003597 8455050658134975137251349)
                ·
                  refine ⟨396330499600076959558657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8455050658134975137251349 396330499600076959558657)
                  ·
                    rfl

theorem cell22_3473329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_3473329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473329 prefixEnd_3473329 := by exact prefixLift 3473329
  have htrace : WordTrace (prefixWord ++ tailWord_3473329) baseStart_3473329 baseEnd_3473329 := by
    simpa [prefixWord, tailWord_3473329, baseEnd_3473329] using wordTrace_append hprefix tailTrace_3473329
  have hstable : (prefixWord ++ tailWord_3473329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473329).length < 2 ^ (prefixWord ++ tailWord_3473329).sum := by decide
  have hdescent : baseEnd_3473329 < baseStart_3473329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473359 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 2, 4]
def baseStart_3473359 : Nat := 118140960795 + 3473359 * 2 ^ 59
def prefixEnd_3473359 : Nat := 4983230072969 + 3 ^ 40 * 3473359 * 2
def baseEnd_3473359 : Nat := 1189001768413320800425879

theorem tailTrace_3473359 : CollatzResearch.WordTrace tailWord_3473359 prefixEnd_3473359 1189001768413320800425879 := by
  unfold tailWord_3473359
  simp only [CollatzResearch.WordTrace]
  refine ⟨126683810223621020335047131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84455873482414013556698087 126683810223621020335047131)
  ·
    refine ⟨190025715335431530502570697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126683810223621020335047131 190025715335431530502570697)
    ·
      refine ⟨142519286501573647876928023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190025715335431530502570697 142519286501573647876928023)
      ·
        refine ⟨213778929752360471815392035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142519286501573647876928023 213778929752360471815392035)
        ·
          refine ⟨320668394628540707723088053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213778929752360471815392035 320668394628540707723088053)
          ·
            refine ⟨30062661996425691349039505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320668394628540707723088053 30062661996425691349039505)
            ·
              refine ⟨22546996497319268511779629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30062661996425691349039505 22546996497319268511779629)
              ·
                refine ⟨8455123686494725691917361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22546996497319268511779629 8455123686494725691917361)
                ·
                  refine ⟨6341342764871044268938021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8455123686494725691917361 6341342764871044268938021)
                  ·
                    refine ⟨1189001768413320800425879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6341342764871044268938021 1189001768413320800425879)
                    ·
                      rfl

theorem cell22_3473359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_3473359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473359 prefixEnd_3473359 := by exact prefixLift 3473359
  have htrace : WordTrace (prefixWord ++ tailWord_3473359) baseStart_3473359 baseEnd_3473359 := by
    simpa [prefixWord, tailWord_3473359, baseEnd_3473359] using wordTrace_append hprefix tailTrace_3473359
  have hstable : (prefixWord ++ tailWord_3473359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473359).length < 2 ^ (prefixWord ++ tailWord_3473359).sum := by decide
  have hdescent : baseEnd_3473359 < baseStart_3473359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473436 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 5]
def baseStart_3473436 : Nat := 118140960795 + 3473436 * 2 ^ 59
def prefixEnd_3473436 : Nat := 4983230072969 + 3 ^ 40 * 3473436 * 2
def baseEnd_3473436 : Nat := 396342709028972755416881

theorem tailTrace_3473436 : CollatzResearch.WordTrace tailWord_3473436 prefixEnd_3473436 396342709028972755416881 := by
  unfold tailWord_3473436
  simp only [CollatzResearch.WordTrace]
  refine ⟨63343309322171031242800081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84457745762894708323733441 63343309322171031242800081)
  ·
    refine ⟨47507481991628273432100061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63343309322171031242800081 47507481991628273432100061)
    ·
      refine ⟨17815305746860602537037523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47507481991628273432100061 17815305746860602537037523)
      ·
        refine ⟨26722958620290903805556285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17815305746860602537037523 26722958620290903805556285)
        ·
          refine ⟨10021109482609088927083607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26722958620290903805556285 10021109482609088927083607)
          ·
            refine ⟨15031664223913633390625411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021109482609088927083607 15031664223913633390625411)
            ·
              refine ⟨22547496335870450085938117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15031664223913633390625411 22547496335870450085938117)
              ·
                refine ⟨4227655562975709391113397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22547496335870450085938117 4227655562975709391113397)
                ·
                  refine ⟨396342709028972755416881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4227655562975709391113397 396342709028972755416881)
                  ·
                    rfl

theorem cell22_3473436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_3473436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473436 prefixEnd_3473436 := by exact prefixLift 3473436
  have htrace : WordTrace (prefixWord ++ tailWord_3473436) baseStart_3473436 baseEnd_3473436 := by
    simpa [prefixWord, tailWord_3473436, baseEnd_3473436] using wordTrace_append hprefix tailTrace_3473436
  have hstable : (prefixWord ++ tailWord_3473436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473436).length < 2 ^ (prefixWord ++ tailWord_3473436).sum := by decide
  have hdescent : baseEnd_3473436 < baseStart_3473436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473466 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_3473466 : Nat := 118140960795 + 3473466 * 2 ^ 59
def prefixEnd_3473466 : Nat := 4983230072969 + 3 ^ 40 * 3473466 * 2
def baseEnd_3473466 : Nat := 1189038396700008188000551

theorem tailTrace_3473466 : CollatzResearch.WordTrace tailWord_3473466 prefixEnd_3473466 1189038396700008188000551 := by
  unfold tailWord_3473466
  simp only [CollatzResearch.WordTrace]
  refine ⟨31671928208558344402298063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84458475222822251739461501 31671928208558344402298063)
  ·
    refine ⟨47507892312837516603447095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31671928208558344402298063 47507892312837516603447095)
    ·
      refine ⟨71261838469256274905170643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47507892312837516603447095 71261838469256274905170643)
      ·
        refine ⟨106892757703884412357755965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71261838469256274905170643 106892757703884412357755965)
        ·
          refine ⟨40084784138956654634158487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106892757703884412357755965 40084784138956654634158487)
          ·
            refine ⟨60127176208434981951237731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40084784138956654634158487 60127176208434981951237731)
            ·
              refine ⟨90190764312652472926856597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60127176208434981951237731 90190764312652472926856597)
              ·
                refine ⟨4227692077155584668446403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90190764312652472926856597 4227692077155584668446403)
                ·
                  refine ⟨6341538115733377002669605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227692077155584668446403 6341538115733377002669605)
                  ·
                    refine ⟨1189038396700008188000551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6341538115733377002669605 1189038396700008188000551)
                    ·
                      rfl

theorem cell22_3473466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_3473466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473466 prefixEnd_3473466 := by exact prefixLift 3473466
  have htrace : WordTrace (prefixWord ++ tailWord_3473466) baseStart_3473466 baseEnd_3473466 := by
    simpa [prefixWord, tailWord_3473466, baseEnd_3473466] using wordTrace_append hprefix tailTrace_3473466
  have hstable : (prefixWord ++ tailWord_3473466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473466).length < 2 ^ (prefixWord ++ tailWord_3473466).sum := by decide
  have hdescent : baseEnd_3473466 < baseStart_3473466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473618 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3473618 : Nat := 118140960795 + 3473618 * 2 ^ 59
def prefixEnd_3473618 : Nat := 4983230072969 + 3 ^ 40 * 3473618 * 2
def baseEnd_3473618 : Nat := 1189090429406330458200085

theorem tailTrace_3473618 : CollatzResearch.WordTrace tailWord_3473618 prefixEnd_3473618 1189090429406330458200085 := by
  unfold tailWord_3473618
  simp only [CollatzResearch.WordTrace]
  refine ⟨31673314182420676892181377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84462171153121805045817005 31673314182420676892181377)
  ·
    refine ⟨23754985636815507669136033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31673314182420676892181377 23754985636815507669136033)
    ·
      refine ⟨17816239227611630751852025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23754985636815507669136033 17816239227611630751852025)
      ·
        refine ⟨13362179420708723063889019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17816239227611630751852025 13362179420708723063889019)
        ·
          refine ⟨20043269131063084595833529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13362179420708723063889019 20043269131063084595833529)
          ·
            refine ⟨15032451848297313446875147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20043269131063084595833529 15032451848297313446875147)
            ·
              refine ⟨22548677772445970170312721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15032451848297313446875147 22548677772445970170312721)
              ·
                refine ⟨16911508329334477627734541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22548677772445970170312721 16911508329334477627734541)
                ·
                  refine ⟨6341815623500429110400453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16911508329334477627734541 6341815623500429110400453)
                  ·
                    refine ⟨1189090429406330458200085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6341815623500429110400453 1189090429406330458200085)
                    ·
                      rfl

theorem cell22_3473618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3473618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473618 prefixEnd_3473618 := by exact prefixLift 3473618
  have htrace : WordTrace (prefixWord ++ tailWord_3473618) baseStart_3473618 baseEnd_3473618 := by
    simpa [prefixWord, tailWord_3473618, baseEnd_3473618] using wordTrace_append hprefix tailTrace_3473618
  have hstable : (prefixWord ++ tailWord_3473618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473618).length < 2 ^ (prefixWord ++ tailWord_3473618).sum := by decide
  have hdescent : baseEnd_3473618 < baseStart_3473618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473650 : List Nat := [3, 2, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3473650 : Nat := 118140960795 + 3473650 * 2 ^ 59
def prefixEnd_3473650 : Nat := 4983230072969 + 3 ^ 40 * 3473650 * 2
def baseEnd_3473650 : Nat := 396367127886764347133329

theorem tailTrace_3473650 : CollatzResearch.WordTrace tailWord_3473650 prefixEnd_3473650 396367127886764347133329 := by
  unfold tailWord_3473650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31673605966391694258472601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84462949243711184689260269 31673605966391694258472601)
  ·
    refine ⟨23755204474793770693854451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31673605966391694258472601 23755204474793770693854451)
    ·
      refine ⟨35632806712190656040781677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23755204474793770693854451 35632806712190656040781677)
      ·
        refine ⟨13362302517071496015293129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35632806712190656040781677 13362302517071496015293129)
        ·
          refine ⟨10021726887803622011469847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13362302517071496015293129 10021726887803622011469847)
          ·
            refine ⟨15032590331705433017204771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021726887803622011469847 15032590331705433017204771)
            ·
              refine ⟨22548885497558149525807157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15032590331705433017204771 22548885497558149525807157)
              ·
                refine ⟨2113958015396076518044421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22548885497558149525807157 2113958015396076518044421)
                ·
                  refine ⟨396367127886764347133329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113958015396076518044421 396367127886764347133329)
                  ·
                    rfl

theorem cell22_3473650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3473650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473650 prefixEnd_3473650 := by exact prefixLift 3473650
  have htrace : WordTrace (prefixWord ++ tailWord_3473650) baseStart_3473650 baseEnd_3473650 := by
    simpa [prefixWord, tailWord_3473650, baseEnd_3473650] using wordTrace_append hprefix tailTrace_3473650
  have hstable : (prefixWord ++ tailWord_3473650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473650).length < 2 ^ (prefixWord ++ tailWord_3473650).sum := by decide
  have hdescent : baseEnd_3473650 < baseStart_3473650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473691 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 2, 6]
def baseStart_3473691 : Nat := 118140960795 + 3473691 * 2 ^ 59
def prefixEnd_3473691 : Nat := 4983230072969 + 3 ^ 40 * 3473691 * 2
def baseEnd_3473691 : Nat := 1189115418798182601124861

theorem tailTrace_3473691 : CollatzResearch.WordTrace tailWord_3473691 prefixEnd_3473691 1189115418798182601124861 := by
  unfold tailWord_3473691
  simp only [CollatzResearch.WordTrace]
  refine ⟨126695919258418241036132927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84463946172278827357421951 126695919258418241036132927)
  ·
    refine ⟨190043878887627361554199391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126695919258418241036132927 190043878887627361554199391)
    ·
      refine ⟨285065818331441042331299087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190043878887627361554199391 285065818331441042331299087)
      ·
        refine ⟨427598727497161563496948631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285065818331441042331299087 427598727497161563496948631)
        ·
          refine ⟨641398091245742345245422947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427598727497161563496948631 641398091245742345245422947)
          ·
            refine ⟨962097136868613517868134421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641398091245742345245422947 962097136868613517868134421)
            ·
              refine ⟨45098303290716258650068801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 962097136868613517868134421 45098303290716258650068801)
              ·
                refine ⟨33823727468037193987551601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45098303290716258650068801 33823727468037193987551601)
                ·
                  refine ⟨25367795601027895490663701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33823727468037193987551601 25367795601027895490663701)
                  ·
                    refine ⟨1189115418798182601124861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25367795601027895490663701 1189115418798182601124861)
                    ·
                      rfl

theorem cell22_3473691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_3473691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473691 prefixEnd_3473691 := by exact prefixLift 3473691
  have htrace : WordTrace (prefixWord ++ tailWord_3473691) baseStart_3473691 baseEnd_3473691 := by
    simpa [prefixWord, tailWord_3473691, baseEnd_3473691] using wordTrace_append hprefix tailTrace_3473691
  have hstable : (prefixWord ++ tailWord_3473691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473691).length < 2 ^ (prefixWord ++ tailWord_3473691).sum := by decide
  have hdescent : baseEnd_3473691 < baseStart_3473691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473695 : List Nat := [1, 1, 2, 4, 3, 3, 2, 6]
def baseStart_3473695 : Nat := 118140960795 + 3473695 * 2 ^ 59
def prefixEnd_3473695 : Nat := 4983230072969 + 3 ^ 40 * 3473695 * 2
def baseEnd_3473695 : Nat := 132124087564436436002761

theorem tailTrace_3473695 : CollatzResearch.WordTrace tailWord_3473695 prefixEnd_3473695 132124087564436436002761 := by
  unfold tailWord_3473695
  simp only [CollatzResearch.WordTrace]
  refine ⟨126696065150403749719278539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84464043433602499812852359 126696065150403749719278539)
  ·
    refine ⟨190044097725605624578917809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126696065150403749719278539 190044097725605624578917809)
    ·
      refine ⟨142533073294204218434188357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190044097725605624578917809 142533073294204218434188357)
      ·
        refine ⟨26724951242663290956410317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142533073294204218434188357 26724951242663290956410317)
        ·
          refine ⟨10021856715998734108653869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26724951242663290956410317 10021856715998734108653869)
          ·
            refine ⟨3758196268499525290745201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10021856715998734108653869 3758196268499525290745201)
            ·
              refine ⟨2818647201374643968058901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3758196268499525290745201 2818647201374643968058901)
              ·
                refine ⟨132124087564436436002761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2818647201374643968058901 132124087564436436002761)
                ·
                  rfl

theorem cell22_3473695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 6].length) (baseStart_3473695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473695 prefixEnd_3473695 := by exact prefixLift 3473695
  have htrace : WordTrace (prefixWord ++ tailWord_3473695) baseStart_3473695 baseEnd_3473695 := by
    simpa [prefixWord, tailWord_3473695, baseEnd_3473695] using wordTrace_append hprefix tailTrace_3473695
  have hstable : (prefixWord ++ tailWord_3473695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473695).length < 2 ^ (prefixWord ++ tailWord_3473695).sum := by decide
  have hdescent : baseEnd_3473695 < baseStart_3473695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473800 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_3473800 : Nat := 118140960795 + 3473800 * 2 ^ 59
def prefixEnd_3473800 : Nat := 4983230072969 + 3 ^ 40 * 3473800 * 2
def baseEnd_3473800 : Nat := 1189152731725742650149527

theorem tailTrace_3473800 : CollatzResearch.WordTrace tailWord_3473800 prefixEnd_3473800 1189152731725742650149527 := by
  unfold tailWord_3473800
  simp only [CollatzResearch.WordTrace]
  refine ⟨63349947407511676325925427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84466596543348901767900569 63349947407511676325925427)
  ·
    refine ⟨95024921111267514488888141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63349947407511676325925427 95024921111267514488888141)
    ·
      refine ⟨35634345416725317933333053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95024921111267514488888141 35634345416725317933333053)
      ·
        refine ⟨13362879531271994224999895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35634345416725317933333053 13362879531271994224999895)
        ·
          refine ⟨20044319296907991337499843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13362879531271994224999895 20044319296907991337499843)
          ·
            refine ⟨30066478945361987006249765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20044319296907991337499843 30066478945361987006249765)
            ·
              refine ⟨5637464802255372563671831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30066478945361987006249765 5637464802255372563671831)
              ·
                refine ⟨8456197203383058845507747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637464802255372563671831 8456197203383058845507747)
                ·
                  refine ⟨12684295805074588268261621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8456197203383058845507747 12684295805074588268261621)
                  ·
                    refine ⟨1189152731725742650149527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12684295805074588268261621 1189152731725742650149527)
                    ·
                      rfl

theorem cell22_3473800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_3473800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473800 prefixEnd_3473800 := by exact prefixLift 3473800
  have htrace : WordTrace (prefixWord ++ tailWord_3473800) baseStart_3473800 baseEnd_3473800 := by
    simpa [prefixWord, tailWord_3473800, baseEnd_3473800] using wordTrace_append hprefix tailTrace_3473800
  have hstable : (prefixWord ++ tailWord_3473800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473800).length < 2 ^ (prefixWord ++ tailWord_3473800).sum := by decide
  have hdescent : baseEnd_3473800 < baseStart_3473800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473802 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_3473802 : Nat := 118140960795 + 3473802 * 2 ^ 59
def prefixEnd_3473802 : Nat := 4983230072969 + 3 ^ 40 * 3473802 * 2
def baseEnd_3473802 : Nat := 396384472122205103866507

theorem tailTrace_3473802 : CollatzResearch.WordTrace tailWord_3473802 prefixEnd_3473802 396384472122205103866507 := by
  unfold tailWord_3473802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31674991940254026748355915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84466645174010737995615773 31674991940254026748355915)
  ·
    refine ⟨47512487910381040122533873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31674991940254026748355915 47512487910381040122533873)
    ·
      refine ⟨35634365932785780091900405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47512487910381040122533873 35634365932785780091900405)
      ·
        refine ⟨3340721806198666883615663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35634365932785780091900405 3340721806198666883615663)
        ·
          refine ⟨5011082709298000325423495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340721806198666883615663 5011082709298000325423495)
          ·
            refine ⟨7516624063947000488135243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011082709298000325423495 7516624063947000488135243)
            ·
              refine ⟨11274936095920500732202865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7516624063947000488135243 11274936095920500732202865)
              ·
                refine ⟨8456202071940375549152149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11274936095920500732202865 8456202071940375549152149)
                ·
                  refine ⟨396384472122205103866507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8456202071940375549152149 396384472122205103866507)
                  ·
                    rfl

theorem cell22_3473802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_3473802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473802 prefixEnd_3473802 := by exact prefixLift 3473802
  have htrace : WordTrace (prefixWord ++ tailWord_3473802) baseStart_3473802 baseEnd_3473802 := by
    simpa [prefixWord, tailWord_3473802, baseEnd_3473802] using wordTrace_append hprefix tailTrace_3473802
  have hstable : (prefixWord ++ tailWord_3473802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473802).length < 2 ^ (prefixWord ++ tailWord_3473802).sum := by decide
  have hdescent : baseEnd_3473802 < baseStart_3473802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473815 : List Nat := [1, 1, 3, 3, 1, 1, 5, 1, 2, 4]
def baseStart_3473815 : Nat := 118140960795 + 3473815 * 2 ^ 59
def prefixEnd_3473815 : Nat := 4983230072969 + 3 ^ 40 * 3473815 * 2
def baseEnd_3473815 : Nat := 1189157866532287611024481

theorem tailTrace_3473815 : CollatzResearch.WordTrace tailWord_3473815 prefixEnd_3473815 1189157866532287611024481 := by
  unfold tailWord_3473815
  simp only [CollatzResearch.WordTrace]
  refine ⟨126700441909969010213646899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84466961273312673475764599 126700441909969010213646899)
  ·
    refine ⟨190050662864953515320470349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126700441909969010213646899 190050662864953515320470349)
    ·
      refine ⟨71268998574357568245176381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190050662864953515320470349 71268998574357568245176381)
      ·
        refine ⟨26725874465384088091941143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71268998574357568245176381 26725874465384088091941143)
        ·
          refine ⟨40088811698076132137911715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26725874465384088091941143 40088811698076132137911715)
          ·
            refine ⟨60133217547114198206867573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40088811698076132137911715 60133217547114198206867573)
            ·
              refine ⟨5637489145041956081893835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60133217547114198206867573 5637489145041956081893835)
              ·
                refine ⟨8456233717562934122840753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637489145041956081893835 8456233717562934122840753)
                ·
                  refine ⟨6342175288172200592130565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8456233717562934122840753 6342175288172200592130565)
                  ·
                    refine ⟨1189157866532287611024481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6342175288172200592130565 1189157866532287611024481)
                    ·
                      rfl

theorem cell22_3473815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_3473815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473815 prefixEnd_3473815 := by exact prefixLift 3473815
  have htrace : WordTrace (prefixWord ++ tailWord_3473815) baseStart_3473815 baseEnd_3473815 := by
    simpa [prefixWord, tailWord_3473815, baseEnd_3473815] using wordTrace_append hprefix tailTrace_3473815
  have hstable : (prefixWord ++ tailWord_3473815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473815).length < 2 ^ (prefixWord ++ tailWord_3473815).sum := by decide
  have hdescent : baseEnd_3473815 < baseStart_3473815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473821 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_3473821 : Nat := 118140960795 + 3473821 * 2 ^ 59
def prefixEnd_3473821 : Nat := 4983230072969 + 3 ^ 40 * 3473821 * 2
def baseEnd_3473821 : Nat := 1189159920454905595374463

theorem tailTrace_3473821 : CollatzResearch.WordTrace tailWord_3473821 prefixEnd_3473821 1189159920454905595374463 := by
  unfold tailWord_3473821
  simp only [CollatzResearch.WordTrace]
  refine ⟨126700660747947273238365317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84467107165298182158910211 126700660747947273238365317)
  ·
    refine ⟨23756373890240113732193497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126700660747947273238365317 23756373890240113732193497)
    ·
      refine ⟨17817280417680085299145123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23756373890240113732193497 17817280417680085299145123)
      ·
        refine ⟨26725920626520127948717685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17817280417680085299145123 26725920626520127948717685)
        ·
          refine ⟨2505555058736261995192283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26725920626520127948717685 2505555058736261995192283)
          ·
            refine ⟨3758332588104392992788425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505555058736261995192283 3758332588104392992788425)
            ·
              refine ⟨2818749441078294744591319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3758332588104392992788425 2818749441078294744591319)
              ·
                refine ⟨4228124161617442116886979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818749441078294744591319 4228124161617442116886979)
                ·
                  refine ⟨6342186242426163175330469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228124161617442116886979 6342186242426163175330469)
                  ·
                    refine ⟨1189159920454905595374463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6342186242426163175330469 1189159920454905595374463)
                    ·
                      rfl

theorem cell22_3473821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_3473821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473821 prefixEnd_3473821 := by exact prefixLift 3473821
  have htrace : WordTrace (prefixWord ++ tailWord_3473821) baseStart_3473821 baseEnd_3473821 := by
    simpa [prefixWord, tailWord_3473821, baseEnd_3473821] using wordTrace_append hprefix tailTrace_3473821
  have hstable : (prefixWord ++ tailWord_3473821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473821).length < 2 ^ (prefixWord ++ tailWord_3473821).sum := by decide
  have hdescent : baseEnd_3473821 < baseStart_3473821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473873 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_3473873 : Nat := 118140960795 + 3473873 * 2 ^ 59
def prefixEnd_3473873 : Nat := 4983230072969 + 3 ^ 40 * 3473873 * 2
def baseEnd_3473873 : Nat := 1189177721117594793074303

theorem tailTrace_3473873 : CollatzResearch.WordTrace tailWord_3473873 prefixEnd_3473873 1189177721117594793074303 := by
  unfold tailWord_3473873
  simp only [CollatzResearch.WordTrace]
  refine ⟨126702557343758886119258273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84468371562505924079505515 126702557343758886119258273)
  ·
    refine ⟨95026918007819164589443705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126702557343758886119258273 95026918007819164589443705)
    ·
      refine ⟨71270188505864373442082779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95026918007819164589443705 71270188505864373442082779)
      ·
        refine ⟨106905282758796560163124169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71270188505864373442082779 106905282758796560163124169)
        ·
          refine ⟨80178962069097420122343127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106905282758796560163124169 80178962069097420122343127)
          ·
            refine ⟨120268443103646130183514691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80178962069097420122343127 120268443103646130183514691)
            ·
              refine ⟨180402664655469195275272037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120268443103646130183514691 180402664655469195275272037)
              ·
                refine ⟨33825499622900474114113507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180402664655469195275272037 33825499622900474114113507)
                ·
                  refine ⟨50738249434350711171170261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33825499622900474114113507 50738249434350711171170261)
                  ·
                    refine ⟨1189177721117594793074303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50738249434350711171170261 1189177721117594793074303)
                    ·
                      rfl

theorem cell22_3473873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_3473873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473873 prefixEnd_3473873 := by exact prefixLift 3473873
  have htrace : WordTrace (prefixWord ++ tailWord_3473873) baseStart_3473873 baseEnd_3473873 := by
    simpa [prefixWord, tailWord_3473873, baseEnd_3473873] using wordTrace_append hprefix tailTrace_3473873
  have hstable : (prefixWord ++ tailWord_3473873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473873).length < 2 ^ (prefixWord ++ tailWord_3473873).sum := by decide
  have hdescent : baseEnd_3473873 < baseStart_3473873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473896 : List Nat := [2, 1, 4, 1, 1, 4, 3, 2, 1, 3]
def baseStart_3473896 : Nat := 118140960795 + 3473896 * 2 ^ 59
def prefixEnd_3473896 : Nat := 4983230072969 + 3 ^ 40 * 3473896 * 2
def baseEnd_3473896 : Nat := 1189185594487630399749233

theorem tailTrace_3473896 : CollatzResearch.WordTrace tailWord_3473896 prefixEnd_3473896 1189185594487630399749233 := by
  unfold tailWord_3473896
  simp only [CollatzResearch.WordTrace]
  refine ⟨63351698111337780523672771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84468930815117040698230361 63351698111337780523672771)
  ·
    refine ⟨95027547167006670785509157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63351698111337780523672771 95027547167006670785509157)
    ·
      refine ⟨17817665093813750772282967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95027547167006670785509157 17817665093813750772282967)
      ·
        refine ⟨26726497640720626158424451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17817665093813750772282967 26726497640720626158424451)
        ·
          refine ⟨40089746461080939237636677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26726497640720626158424451 40089746461080939237636677)
          ·
            refine ⟨7516827461452676107056877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40089746461080939237636677 7516827461452676107056877)
            ·
              refine ⟨2818810298044753540146329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7516827461452676107056877 2818810298044753540146329)
              ·
                refine ⟨2114107723533565155109747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2818810298044753540146329 2114107723533565155109747)
                ·
                  refine ⟨3171161585300347732664621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114107723533565155109747 3171161585300347732664621)
                  ·
                    refine ⟨1189185594487630399749233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3171161585300347732664621 1189185594487630399749233)
                    ·
                      rfl

theorem cell22_3473896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_3473896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473896 prefixEnd_3473896 := by exact prefixLift 3473896
  have htrace : WordTrace (prefixWord ++ tailWord_3473896) baseStart_3473896 baseEnd_3473896 := by
    simpa [prefixWord, tailWord_3473896, baseEnd_3473896] using wordTrace_append hprefix tailTrace_3473896
  have hstable : (prefixWord ++ tailWord_3473896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473896).length < 2 ^ (prefixWord ++ tailWord_3473896).sum := by decide
  have hdescent : baseEnd_3473896 < baseStart_3473896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473905 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_3473905 : Nat := 118140960795 + 3473905 * 2 ^ 59
def prefixEnd_3473905 : Nat := 4983230072969 + 3 ^ 40 * 3473905 * 2
def baseEnd_3473905 : Nat := 1189188675371557376274205

theorem tailTrace_3473905 : CollatzResearch.WordTrace tailWord_3473905 prefixEnd_3473905 1189188675371557376274205 := by
  unfold tailWord_3473905
  simp only [CollatzResearch.WordTrace]
  refine ⟨126703724479642955584423169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84469149653095303722948779 126703724479642955584423169)
  ·
    refine ⟨95027793359732216688317377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126703724479642955584423169 95027793359732216688317377)
    ·
      refine ⟨71270845019799162516238033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95027793359732216688317377 71270845019799162516238033)
      ·
        refine ⟨53453133764849371887178525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71270845019799162516238033 53453133764849371887178525)
        ·
          refine ⟨20044925161818514457691947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53453133764849371887178525 20044925161818514457691947)
          ·
            refine ⟨30067387742727771686537921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20044925161818514457691947 30067387742727771686537921)
            ·
              refine ⟨22550540807045828764903441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30067387742727771686537921 22550540807045828764903441)
              ·
                refine ⟨16912905605284371573677581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22550540807045828764903441 16912905605284371573677581)
                ·
                  refine ⟨6342339601981639340129093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16912905605284371573677581 6342339601981639340129093)
                  ·
                    refine ⟨1189188675371557376274205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6342339601981639340129093 1189188675371557376274205)
                    ·
                      rfl

theorem cell22_3473905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_3473905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473905 prefixEnd_3473905 := by exact prefixLift 3473905
  have htrace : WordTrace (prefixWord ++ tailWord_3473905) baseStart_3473905 baseEnd_3473905 := by
    simpa [prefixWord, tailWord_3473905, baseEnd_3473905] using wordTrace_append hprefix tailTrace_3473905
  have hstable : (prefixWord ++ tailWord_3473905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473905).length < 2 ^ (prefixWord ++ tailWord_3473905).sum := by decide
  have hdescent : baseEnd_3473905 < baseStart_3473905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3473909 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 5]
def baseStart_3473909 : Nat := 118140960795 + 3473909 * 2 ^ 59
def prefixEnd_3473909 : Nat := 4983230072969 + 3 ^ 40 * 3473909 * 2
def baseEnd_3473909 : Nat := 396396681551100899724731

theorem tailTrace_3473909 : CollatzResearch.WordTrace tailWord_3473909 prefixEnd_3473909 396396681551100899724731 := by
  unfold tailWord_3473909
  simp only [CollatzResearch.WordTrace]
  refine ⟨126703870371628464267568781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84469246914418976178379187 126703870371628464267568781)
  ·
    refine ⟨47513951389360674100338293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126703870371628464267568781 47513951389360674100338293)
    ·
      refine ⟨4454432942752563196906715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47513951389360674100338293 4454432942752563196906715)
      ·
        refine ⟨6681649414128844795360073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4454432942752563196906715 6681649414128844795360073)
        ·
          refine ⟨5011237060596633596520055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6681649414128844795360073 5011237060596633596520055)
          ·
            refine ⟨7516855590894950394780083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011237060596633596520055 7516855590894950394780083)
            ·
              refine ⟨11275283386342425592170125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7516855590894950394780083 11275283386342425592170125)
              ·
                refine ⟨4228231269878409597063797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11275283386342425592170125 4228231269878409597063797)
                ·
                  refine ⟨396396681551100899724731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4228231269878409597063797 396396681551100899724731)
                  ·
                    rfl

theorem cell22_3473909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_3473909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3473909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3473909 prefixEnd_3473909 := by exact prefixLift 3473909
  have htrace : WordTrace (prefixWord ++ tailWord_3473909) baseStart_3473909 baseEnd_3473909 := by
    simpa [prefixWord, tailWord_3473909, baseEnd_3473909] using wordTrace_append hprefix tailTrace_3473909
  have hstable : (prefixWord ++ tailWord_3473909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3473909).length < 2 ^ (prefixWord ++ tailWord_3473909).sum := by decide
  have hdescent : baseEnd_3473909 < baseStart_3473909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3473909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474149 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_3474149 : Nat := 118140960795 + 3474149 * 2 ^ 59
def prefixEnd_3474149 : Nat := 4983230072969 + 3 ^ 40 * 3474149 * 2
def baseEnd_3474149 : Nat := 1189272201558022073173457

theorem tailTrace_3474149 : CollatzResearch.WordTrace tailWord_3474149 prefixEnd_3474149 1189272201558022073173457 := by
  unfold tailWord_3474149
  simp only [CollatzResearch.WordTrace]
  refine ⟨126712623890758985256305501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84475082593839323504203667 126712623890758985256305501)
  ·
    refine ⟨47517233959034619471114563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126712623890758985256305501 47517233959034619471114563)
    ·
      refine ⟨71275850938551929206671845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47517233959034619471114563 71275850938551929206671845)
      ·
        refine ⟨13364222050978486726250971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71275850938551929206671845 13364222050978486726250971)
        ·
          refine ⟨20046333076467730089376457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13364222050978486726250971 20046333076467730089376457)
          ·
            refine ⟨15034749807350797567032343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20046333076467730089376457 15034749807350797567032343)
            ·
              refine ⟨22552124711026196350548515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15034749807350797567032343 22552124711026196350548515)
              ·
                refine ⟨33828187066539294525822773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22552124711026196350548515 33828187066539294525822773)
                ·
                  refine ⟨3171392537488058861795885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33828187066539294525822773 3171392537488058861795885)
                  ·
                    refine ⟨1189272201558022073173457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3171392537488058861795885 1189272201558022073173457)
                    ·
                      rfl

theorem cell22_3474149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_3474149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474149 prefixEnd_3474149 := by exact prefixLift 3474149
  have htrace : WordTrace (prefixWord ++ tailWord_3474149) baseStart_3474149 baseEnd_3474149 := by
    simpa [prefixWord, tailWord_3474149, baseEnd_3474149] using wordTrace_append hprefix tailTrace_3474149
  have hstable : (prefixWord ++ tailWord_3474149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474149).length < 2 ^ (prefixWord ++ tailWord_3474149).sum := by decide
  have hdescent : baseEnd_3474149 < baseStart_3474149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474183 : List Nat := [1, 1, 4, 4, 1, 1, 2, 4, 1, 3]
def baseStart_3474183 : Nat := 118140960795 + 3474183 * 2 ^ 59
def prefixEnd_3474183 : Nat := 4983230072969 + 3 ^ 40 * 3474183 * 2
def baseEnd_3474183 : Nat := 1189283840452857317823353

theorem tailTrace_3474183 : CollatzResearch.WordTrace tailWord_3474183 prefixEnd_3474183 1189283840452857317823353 := by
  unfold tailWord_3474183
  simp only [CollatzResearch.WordTrace]
  refine ⟨126713863972635809063043203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84475909315090539375362135 126713863972635809063043203)
  ·
    refine ⟨190070795958953713594564805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126713863972635809063043203 190070795958953713594564805)
    ·
      refine ⟨35638274242303821298980901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190070795958953713594564805 35638274242303821298980901)
      ·
        refine ⟨6682176420431966493558919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35638274242303821298980901 6682176420431966493558919)
        ·
          refine ⟨10023264630647949740338379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682176420431966493558919 10023264630647949740338379)
          ·
            refine ⟨15034896945971924610507569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023264630647949740338379 15034896945971924610507569)
            ·
              refine ⟨11276172709478943457880677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15034896945971924610507569 11276172709478943457880677)
              ·
                refine ⟨2114282383027301898352627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11276172709478943457880677 2114282383027301898352627)
                ·
                  refine ⟨3171423574540952847528941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114282383027301898352627 3171423574540952847528941)
                  ·
                    refine ⟨1189283840452857317823353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3171423574540952847528941 1189283840452857317823353)
                    ·
                      rfl

theorem cell22_3474183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_3474183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474183 prefixEnd_3474183 := by exact prefixLift 3474183
  have htrace : WordTrace (prefixWord ++ tailWord_3474183) baseStart_3474183 baseEnd_3474183 := by
    simpa [prefixWord, tailWord_3474183, baseEnd_3474183] using wordTrace_append hprefix tailTrace_3474183
  have hstable : (prefixWord ++ tailWord_3474183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474183).length < 2 ^ (prefixWord ++ tailWord_3474183).sum := by decide
  have hdescent : baseEnd_3474183 < baseStart_3474183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474260 : List Nat := [2, 4, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3474260 : Nat := 118140960795 + 3474260 * 2 ^ 59
def prefixEnd_3474260 : Nat := 4983230072969 + 3 ^ 40 * 3474260 * 2
def baseEnd_3474260 : Nat := 1189310199126454783648117

theorem tailTrace_3474260 : CollatzResearch.WordTrace tailWord_3474260 prefixEnd_3474260 1189310199126454783648117 := by
  unfold tailWord_3474260
  simp only [CollatzResearch.WordTrace]
  refine ⟨63358336196678425606798117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84477781595571234142397489 63358336196678425606798117)
  ·
    refine ⟨11879688036877204801274647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63358336196678425606798117 11879688036877204801274647)
    ·
      refine ⟨17819532055315807201911971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11879688036877204801274647 17819532055315807201911971)
      ·
        refine ⟨26729298082973710802867957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17819532055315807201911971 26729298082973710802867957)
        ·
          refine ⟨2505871695278785387768871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26729298082973710802867957 2505871695278785387768871)
          ·
            refine ⟨3758807542918178081653307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505871695278785387768871 3758807542918178081653307)
            ·
              refine ⟨5638211314377267122479961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758807542918178081653307 5638211314377267122479961)
              ·
                refine ⟨4228658485782950341859971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5638211314377267122479961 4228658485782950341859971)
                ·
                  refine ⟨6342987728674425512789957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228658485782950341859971 6342987728674425512789957)
                  ·
                    refine ⟨1189310199126454783648117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6342987728674425512789957 1189310199126454783648117)
                    ·
                      rfl

theorem cell22_3474260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3474260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474260 prefixEnd_3474260 := by exact prefixLift 3474260
  have htrace : WordTrace (prefixWord ++ tailWord_3474260) baseStart_3474260 baseEnd_3474260 := by
    simpa [prefixWord, tailWord_3474260, baseEnd_3474260] using wordTrace_append hprefix tailTrace_3474260
  have hstable : (prefixWord ++ tailWord_3474260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474260).length < 2 ^ (prefixWord ++ tailWord_3474260).sum := by decide
  have hdescent : baseEnd_3474260 < baseStart_3474260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474286 : List Nat := [4, 1, 2, 3, 3, 9]
def baseStart_3474286 : Nat := 118140960795 + 3474286 * 2 ^ 59
def prefixEnd_3474286 : Nat := 4983230072969 + 3 ^ 40 * 3474286 * 2
def baseEnd_3474286 : Nat := 14682951845158017067877

theorem tailTrace_3474286 : CollatzResearch.WordTrace tailWord_3474286 prefixEnd_3474286 14682951845158017067877 := by
  unfold tailWord_3474286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839702586407832206755339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84478413794175105102695141 15839702586407832206755339)
  ·
    refine ⟨23759553879611748310133009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15839702586407832206755339 23759553879611748310133009)
    ·
      refine ⟨17819665409708811232599757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23759553879611748310133009 17819665409708811232599757)
      ·
        refine ⟨6682374528640804212224909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17819665409708811232599757 6682374528640804212224909)
        ·
          refine ⟨2505890448240301579584341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6682374528640804212224909 2505890448240301579584341)
          ·
            refine ⟨14682951845158017067877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2505890448240301579584341 14682951845158017067877)
            ·
              rfl

theorem cell22_3474286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 9].length) (baseStart_3474286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474286 prefixEnd_3474286 := by exact prefixLift 3474286
  have htrace : WordTrace (prefixWord ++ tailWord_3474286) baseStart_3474286 baseEnd_3474286 := by
    simpa [prefixWord, tailWord_3474286, baseEnd_3474286] using wordTrace_append hprefix tailTrace_3474286
  have hstable : (prefixWord ++ tailWord_3474286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474286).length < 2 ^ (prefixWord ++ tailWord_3474286).sum := by decide
  have hdescent : baseEnd_3474286 < baseStart_3474286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474335 : List Nat := [1, 1, 2, 5, 2, 2, 2, 3, 1, 3]
def baseStart_3474335 : Nat := 118140960795 + 3474335 * 2 ^ 59
def prefixEnd_3474335 : Nat := 4983230072969 + 3 ^ 40 * 3474335 * 2
def baseEnd_3474335 : Nat := 1189335873159179588022887

theorem tailTrace_3474335 : CollatzResearch.WordTrace tailWord_3474335 prefixEnd_3474335 1189335873159179588022887 := by
  unfold tailWord_3474335
  simp only [CollatzResearch.WordTrace]
  refine ⟨126719407868085139022576459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84479605245390092681717639 126719407868085139022576459)
  ·
    refine ⟨190079111802127708533864689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126719407868085139022576459 190079111802127708533864689)
    ·
      refine ⟨142559333851595781400398517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190079111802127708533864689 142559333851595781400398517)
      ·
        refine ⟨13364937548587104506287361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142559333851595781400398517 13364937548587104506287361)
        ·
          refine ⟨10023703161440328379715521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13364937548587104506287361 10023703161440328379715521)
          ·
            refine ⟨7517777371080246284786641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10023703161440328379715521 7517777371080246284786641)
            ·
              refine ⟨5638333028310184713589981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7517777371080246284786641 5638333028310184713589981)
              ·
                refine ⟨2114374885616319267596243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5638333028310184713589981 2114374885616319267596243)
                ·
                  refine ⟨3171562328424478901394365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114374885616319267596243 3171562328424478901394365)
                  ·
                    refine ⟨1189335873159179588022887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3171562328424478901394365 1189335873159179588022887)
                    ·
                      rfl

theorem cell22_3474335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 3, 1, 3].length) (baseStart_3474335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474335 prefixEnd_3474335 := by exact prefixLift 3474335
  have htrace : WordTrace (prefixWord ++ tailWord_3474335) baseStart_3474335 baseEnd_3474335 := by
    simpa [prefixWord, tailWord_3474335, baseEnd_3474335] using wordTrace_append hprefix tailTrace_3474335
  have hstable : (prefixWord ++ tailWord_3474335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474335).length < 2 ^ (prefixWord ++ tailWord_3474335).sum := by decide
  have hdescent : baseEnd_3474335 < baseStart_3474335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474359 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 6]
def baseStart_3474359 : Nat := 118140960795 + 3474359 * 2 ^ 59
def prefixEnd_3474359 : Nat := 4983230072969 + 3 ^ 40 * 3474359 * 2
def baseEnd_3474359 : Nat := 396448029616550508474271

theorem tailTrace_3474359 : CollatzResearch.WordTrace tailWord_3474359 prefixEnd_3474359 396448029616550508474271 := by
  unfold tailWord_3474359
  simp only [CollatzResearch.WordTrace]
  refine ⟨126720283219998191121450131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84480188813332127414300087 126720283219998191121450131)
  ·
    refine ⟨190080424829997286682175197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126720283219998191121450131 190080424829997286682175197)
    ·
      refine ⟨71280159311248982505815699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190080424829997286682175197 71280159311248982505815699)
      ·
        refine ⟨106920238966873473758723549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71280159311248982505815699 106920238966873473758723549)
        ·
          refine ⟨40095089612577552659521331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106920238966873473758723549 40095089612577552659521331)
          ·
            refine ⟨60142634418866328989281997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40095089612577552659521331 60142634418866328989281997)
            ·
              refine ⟨22553487907074873370980749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60142634418866328989281997 22553487907074873370980749)
              ·
                refine ⟨8457557965153077514117781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22553487907074873370980749 8457557965153077514117781)
                ·
                  refine ⟨396448029616550508474271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8457557965153077514117781 396448029616550508474271)
                  ·
                    rfl

theorem cell22_3474359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 6].length) (baseStart_3474359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474359 prefixEnd_3474359 := by exact prefixLift 3474359
  have htrace : WordTrace (prefixWord ++ tailWord_3474359) baseStart_3474359 baseEnd_3474359 := by
    simpa [prefixWord, tailWord_3474359, baseEnd_3474359] using wordTrace_append hprefix tailTrace_3474359
  have hstable : (prefixWord ++ tailWord_3474359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474359).length < 2 ^ (prefixWord ++ tailWord_3474359).sum := by decide
  have hdescent : baseEnd_3474359 < baseStart_3474359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474393 : List Nat := [1, 2, 1, 2, 5, 1, 3, 3, 4]
def baseStart_3474393 : Nat := 118140960795 + 3474393 * 2 ^ 59
def prefixEnd_3474393 : Nat := 4983230072969 + 3 ^ 40 * 3474393 * 2
def baseEnd_3474393 : Nat := 396451909248162256690903

theorem tailTrace_3474393 : CollatzResearch.WordTrace tailWord_3474393 prefixEnd_3474393 396451909248162256690903 := by
  unfold tailWord_3474393
  simp only [CollatzResearch.WordTrace]
  refine ⟨126721523301875014928187833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84481015534583343285458555 126721523301875014928187833)
  ·
    refine ⟨95041142476406261196140875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126721523301875014928187833 95041142476406261196140875)
    ·
      refine ⟨142561713714609391794211313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95041142476406261196140875 142561713714609391794211313)
      ·
        refine ⟨106921285285957043845658485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142561713714609391794211313 106921285285957043845658485)
        ·
          refine ⟨10023870495558472860530483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106921285285957043845658485 10023870495558472860530483)
          ·
            refine ⟨15035805743337709290795725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023870495558472860530483 15035805743337709290795725)
            ·
              refine ⟨5638427153751640984048397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15035805743337709290795725 5638427153751640984048397)
              ·
                refine ⟨2114410182656865369018149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5638427153751640984048397 2114410182656865369018149)
                ·
                  refine ⟨396451909248162256690903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114410182656865369018149 396451909248162256690903)
                  ·
                    rfl

theorem cell22_3474393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_3474393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474393 prefixEnd_3474393 := by exact prefixLift 3474393
  have htrace : WordTrace (prefixWord ++ tailWord_3474393) baseStart_3474393 baseEnd_3474393 := by
    simpa [prefixWord, tailWord_3474393, baseEnd_3474393] using wordTrace_append hprefix tailTrace_3474393
  have hstable : (prefixWord ++ tailWord_3474393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474393).length < 2 ^ (prefixWord ++ tailWord_3474393).sum := by decide
  have hdescent : baseEnd_3474393 < baseStart_3474393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474410 : List Nat := [3, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_3474410 : Nat := 118140960795 + 3474410 * 2 ^ 59
def prefixEnd_3474410 : Nat := 4983230072969 + 3 ^ 40 * 3474410 * 2
def baseEnd_3474410 : Nat := 396453849063968130799219

theorem tailTrace_3474410 : CollatzResearch.WordTrace tailWord_3474410 prefixEnd_3474410 396453849063968130799219 := by
  unfold tailWord_3474410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31680535835703356707889171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84481428895208951221037789 31680535835703356707889171)
  ·
    refine ⟨47520803753555035061833757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31680535835703356707889171 47520803753555035061833757)
    ·
      refine ⟨17820301407583138148187659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47520803753555035061833757 17820301407583138148187659)
      ·
        refine ⟨26730452111374707222281489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17820301407583138148187659 26730452111374707222281489)
        ·
          refine ⟨20047839083531030416711117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26730452111374707222281489 20047839083531030416711117)
          ·
            refine ⟨7517939656324136406266669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20047839083531030416711117 7517939656324136406266669)
            ·
              refine ⟨2819227371121551152350001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7517939656324136406266669 2819227371121551152350001)
              ·
                refine ⟨2114420528341163364262501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819227371121551152350001 2114420528341163364262501)
                ·
                  refine ⟨396453849063968130799219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114420528341163364262501 396453849063968130799219)
                  ·
                    rfl

theorem cell22_3474410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_3474410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474410 prefixEnd_3474410 := by exact prefixLift 3474410
  have htrace : WordTrace (prefixWord ++ tailWord_3474410) baseStart_3474410 baseEnd_3474410 := by
    simpa [prefixWord, tailWord_3474410, baseEnd_3474410] using wordTrace_append hprefix tailTrace_3474410
  have hstable : (prefixWord ++ tailWord_3474410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474410).length < 2 ^ (prefixWord ++ tailWord_3474410).sum := by decide
  have hdescent : baseEnd_3474410 < baseStart_3474410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474449 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 9]
def baseStart_3474449 : Nat := 118140960795 + 3474449 * 2 ^ 59
def prefixEnd_3474449 : Nat := 4983230072969 + 3 ^ 40 * 3474449 * 2
def baseEnd_3474449 : Nat := 396458299229640430224179

theorem tailTrace_3474449 : CollatzResearch.WordTrace tailWord_3474449 prefixEnd_3474449 396458299229640430224179 := by
  unfold tailWord_3474449
  simp only [CollatzResearch.WordTrace]
  refine ⟨126723565789672136492226401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84482377193114757661484267 126723565789672136492226401)
  ·
    refine ⟨95042674342254102369169801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126723565789672136492226401 95042674342254102369169801)
    ·
      refine ⟨71282005756690576776877351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95042674342254102369169801 71282005756690576776877351)
      ·
        refine ⟨106923008635035865165316027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71282005756690576776877351 106923008635035865165316027)
        ·
          refine ⟨160384512952553797747974041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106923008635035865165316027 160384512952553797747974041)
          ·
            refine ⟨120288384714415348310980531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160384512952553797747974041 120288384714415348310980531)
            ·
              refine ⟨180432577071623022466470797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120288384714415348310980531 180432577071623022466470797)
              ·
                refine ⟨67662216401858633424926549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180432577071623022466470797 67662216401858633424926549)
                ·
                  refine ⟨396458299229640430224179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67662216401858633424926549 396458299229640430224179)
                  ·
                    rfl

theorem cell22_3474449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_3474449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474449 prefixEnd_3474449 := by exact prefixLift 3474449
  have htrace : WordTrace (prefixWord ++ tailWord_3474449) baseStart_3474449 baseEnd_3474449 := by
    simpa [prefixWord, tailWord_3474449, baseEnd_3474449] using wordTrace_append hprefix tailTrace_3474449
  have hstable : (prefixWord ++ tailWord_3474449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474449).length < 2 ^ (prefixWord ++ tailWord_3474449).sum := by decide
  have hdescent : baseEnd_3474449 < baseStart_3474449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474481 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_3474481 : Nat := 118140960795 + 3474481 * 2 ^ 59
def prefixEnd_3474481 : Nat := 4983230072969 + 3 ^ 40 * 3474481 * 2
def baseEnd_3474481 : Nat := 1189385851942883873872439

theorem tailTrace_3474481 : CollatzResearch.WordTrace tailWord_3474481 prefixEnd_3474481 1189385851942883873872439 := by
  unfold tailWord_3474481
  simp only [CollatzResearch.WordTrace]
  refine ⟨126724732925556205957391297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84483155283704137304927531 126724732925556205957391297)
  ·
    refine ⟨95043549694167154468043473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126724732925556205957391297 95043549694167154468043473)
    ·
      refine ⟨71282662270625365851032605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95043549694167154468043473 71282662270625365851032605)
      ·
        refine ⟨26730998351484512194137227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71282662270625365851032605 26730998351484512194137227)
        ·
          refine ⟨40096497527226768291205841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26730998351484512194137227 40096497527226768291205841)
          ·
            refine ⟨30072373145420076218404381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40096497527226768291205841 30072373145420076218404381)
            ·
              refine ⟨11277139929532528581901643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30072373145420076218404381 11277139929532528581901643)
              ·
                refine ⟨16915709894298792872852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11277139929532528581901643 16915709894298792872852465)
                ·
                  refine ⟨12686782420724094654639349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16915709894298792872852465 12686782420724094654639349)
                  ·
                    refine ⟨1189385851942883873872439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12686782420724094654639349 1189385851942883873872439)
                    ·
                      rfl

theorem cell22_3474481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_3474481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474481 prefixEnd_3474481 := by exact prefixLift 3474481
  have htrace : WordTrace (prefixWord ++ tailWord_3474481) baseStart_3474481 baseEnd_3474481 := by
    simpa [prefixWord, tailWord_3474481, baseEnd_3474481] using wordTrace_append hprefix tailTrace_3474481
  have hstable : (prefixWord ++ tailWord_3474481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474481).length < 2 ^ (prefixWord ++ tailWord_3474481).sum := by decide
  have hdescent : baseEnd_3474481 < baseStart_3474481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474496 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_3474496 : Nat := 118140960795 + 3474496 * 2 ^ 59
def prefixEnd_3474496 : Nat := 4983230072969 + 3 ^ 40 * 3474496 * 2
def baseEnd_3474496 : Nat := 1189390986749428834747393

theorem tailTrace_3474496 : CollatzResearch.WordTrace tailWord_3474496 prefixEnd_3474496 1189390986749428834747393 := by
  unfold tailWord_3474496
  simp only [CollatzResearch.WordTrace]
  refine ⟨63362640010250931759593671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84483520013667909012791561 63362640010250931759593671)
  ·
    refine ⟨95043960015376397639390507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63362640010250931759593671 95043960015376397639390507)
    ·
      refine ⟨142565940023064596459085761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95043960015376397639390507 142565940023064596459085761)
      ·
        refine ⟨106924455017298447344314321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142565940023064596459085761 106924455017298447344314321)
        ·
          refine ⟨80193341262973835508235741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106924455017298447344314321 80193341262973835508235741)
          ·
            refine ⟨30072502973615188315588403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80193341262973835508235741 30072502973615188315588403)
            ·
              refine ⟨45108754460422782473382605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30072502973615188315588403 45108754460422782473382605)
              ·
                refine ⟨16915782922658543427518477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45108754460422782473382605 16915782922658543427518477)
                ·
                  refine ⟨6343418595996953785319429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16915782922658543427518477 6343418595996953785319429)
                  ·
                    refine ⟨1189390986749428834747393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6343418595996953785319429 1189390986749428834747393)
                    ·
                      rfl

theorem cell22_3474496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_3474496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474496 prefixEnd_3474496 := by exact prefixLift 3474496
  have htrace : WordTrace (prefixWord ++ tailWord_3474496) baseStart_3474496 baseEnd_3474496 := by
    simpa [prefixWord, tailWord_3474496, baseEnd_3474496] using wordTrace_append hprefix tailTrace_3474496
  have hstable : (prefixWord ++ tailWord_3474496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474496).length < 2 ^ (prefixWord ++ tailWord_3474496).sum := by decide
  have hdescent : baseEnd_3474496 < baseStart_3474496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474528 : List Nat := [2, 1, 1, 3, 2, 2, 1, 6, 4]
def baseStart_3474528 : Nat := 118140960795 + 3474528 * 2 ^ 59
def prefixEnd_3474528 : Nat := 4983230072969 + 3 ^ 40 * 3474528 * 2
def baseEnd_3474528 : Nat := 396467313667797139315765

theorem tailTrace_3474528 : CollatzResearch.WordTrace tailWord_3474528 prefixEnd_3474528 396467313667797139315765 := by
  unfold tailWord_3474528
  simp only [CollatzResearch.WordTrace]
  refine ⟨63363223578192966492176119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84484298104257288656234825 63363223578192966492176119)
  ·
    refine ⟨95044835367289449738264179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63363223578192966492176119 95044835367289449738264179)
    ·
      refine ⟨142567253050934174607396269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95044835367289449738264179 142567253050934174607396269)
      ·
        refine ⟨53462719894100315477773601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142567253050934174607396269 53462719894100315477773601)
        ·
          refine ⟨40097039920575236608330201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53462719894100315477773601 40097039920575236608330201)
          ·
            refine ⟨30072779940431427456247651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40097039920575236608330201 30072779940431427456247651)
            ·
              refine ⟨45109169910647141184371477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30072779940431427456247651 45109169910647141184371477)
              ·
                refine ⟨2114492339561584743017413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45109169910647141184371477 2114492339561584743017413)
                ·
                  refine ⟨396467313667797139315765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114492339561584743017413 396467313667797139315765)
                  ·
                    rfl

theorem cell22_3474528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 4].length) (baseStart_3474528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474528 prefixEnd_3474528 := by exact prefixLift 3474528
  have htrace : WordTrace (prefixWord ++ tailWord_3474528) baseStart_3474528 baseEnd_3474528 := by
    simpa [prefixWord, tailWord_3474528, baseEnd_3474528] using wordTrace_append hprefix tailTrace_3474528
  have hstable : (prefixWord ++ tailWord_3474528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474528).length < 2 ^ (prefixWord ++ tailWord_3474528).sum := by decide
  have hdescent : baseEnd_3474528 < baseStart_3474528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474556 : List Nat := [2, 2, 2, 1, 1, 3, 3, 8]
def baseStart_3474556 : Nat := 118140960795 + 3474556 * 2 ^ 59
def prefixEnd_3474556 : Nat := 4983230072969 + 3 ^ 40 * 3474556 * 2
def baseEnd_3474556 : Nat := 132156836219512075360801

theorem tailTrace_3474556 : CollatzResearch.WordTrace tailWord_3474556 prefixEnd_3474556 132156836219512075360801 := by
  unfold tailWord_3474556
  simp only [CollatzResearch.WordTrace]
  refine ⟨63363734200142246883185761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84484978933522995844247681 63363734200142246883185761)
  ·
    refine ⟨47522800650106685162389321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63363734200142246883185761 47522800650106685162389321)
    ·
      refine ⟨35642100487580013871791991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47522800650106685162389321 35642100487580013871791991)
      ·
        refine ⟨53463150731370020807687987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35642100487580013871791991 53463150731370020807687987)
        ·
          refine ⟨80194726097055031211531981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53463150731370020807687987 80194726097055031211531981)
          ·
            refine ⟨30073022286395636704324493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80194726097055031211531981 30073022286395636704324493)
            ·
              refine ⟨11277383357398363764121685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30073022286395636704324493 11277383357398363764121685)
              ·
                refine ⟨132156836219512075360801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11277383357398363764121685 132156836219512075360801)
                ·
                  rfl

theorem cell22_3474556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 8].length) (baseStart_3474556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474556 prefixEnd_3474556 := by exact prefixLift 3474556
  have htrace : WordTrace (prefixWord ++ tailWord_3474556) baseStart_3474556 baseEnd_3474556 := by
    simpa [prefixWord, tailWord_3474556, baseEnd_3474556] using wordTrace_append hprefix tailTrace_3474556
  have hstable : (prefixWord ++ tailWord_3474556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474556).length < 2 ^ (prefixWord ++ tailWord_3474556).sum := by decide
  have hdescent : baseEnd_3474556 < baseStart_3474556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474590 : List Nat := [4, 3, 1, 1, 2, 2, 2, 7]
def baseStart_3474590 : Nat := 118140960795 + 3474590 * 2 ^ 59
def prefixEnd_3474590 : Nat := 4983230072969 + 3 ^ 40 * 3474590 * 2
def baseEnd_3474590 : Nat := 132158129430049324766345

theorem tailTrace_3474590 : CollatzResearch.WordTrace tailWord_3474590 prefixEnd_3474590 132158129430049324766345 := by
  unfold tailWord_3474590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15841088560270164696638653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84485805654774211715406149 15841088560270164696638653)
  ·
    refine ⟨5940408210101311761239495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15841088560270164696638653 5940408210101311761239495)
    ·
      refine ⟨8910612315151967641859243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5940408210101311761239495 8910612315151967641859243)
      ·
        refine ⟨13365918472727951462788865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8910612315151967641859243 13365918472727951462788865)
        ·
          refine ⟨10024438854545963597091649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13365918472727951462788865 10024438854545963597091649)
          ·
            refine ⟨7518329140909472697818737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10024438854545963597091649 7518329140909472697818737)
            ·
              refine ⟨5638746855682104523364053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518329140909472697818737 5638746855682104523364053)
              ·
                refine ⟨132158129430049324766345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5638746855682104523364053 132158129430049324766345)
                ·
                  rfl

theorem cell22_3474590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_3474590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474590 prefixEnd_3474590 := by exact prefixLift 3474590
  have htrace : WordTrace (prefixWord ++ tailWord_3474590) baseStart_3474590 baseEnd_3474590 := by
    simpa [prefixWord, tailWord_3474590, baseEnd_3474590] using wordTrace_append hprefix tailTrace_3474590
  have hstable : (prefixWord ++ tailWord_3474590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474590).length < 2 ^ (prefixWord ++ tailWord_3474590).sum := by decide
  have hdescent : baseEnd_3474590 < baseStart_3474590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474616 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_3474616 : Nat := 118140960795 + 3474616 * 2 ^ 59
def prefixEnd_3474616 : Nat := 4983230072969 + 3 ^ 40 * 3474616 * 2
def baseEnd_3474616 : Nat := 1189432065201788521747025

theorem tailTrace_3474616 : CollatzResearch.WordTrace tailWord_3474616 prefixEnd_3474616 1189432065201788521747025 := by
  unfold tailWord_3474616
  simp only [CollatzResearch.WordTrace]
  refine ⟨63364828390033562006777851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84486437853378082675703801 63364828390033562006777851)
  ·
    refine ⟨95047242585050343010166777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63364828390033562006777851 95047242585050343010166777)
    ·
      refine ⟨71285431938787757257625083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95047242585050343010166777 71285431938787757257625083)
      ·
        refine ⟨106928147908181635886437625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71285431938787757257625083 106928147908181635886437625)
        ·
          refine ⟨80196110931136226914828219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106928147908181635886437625 80196110931136226914828219)
          ·
            refine ⟨120294166396704340372242329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80196110931136226914828219 120294166396704340372242329)
            ·
              refine ⟨90220624797528255279181747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120294166396704340372242329 90220624797528255279181747)
              ·
                refine ⟨135330937196292382918772621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90220624797528255279181747 135330937196292382918772621)
                ·
                  refine ⟨50749101448609643594539733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135330937196292382918772621 50749101448609643594539733)
                  ·
                    refine ⟨1189432065201788521747025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50749101448609643594539733 1189432065201788521747025)
                    ·
                      rfl

theorem cell22_3474616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_3474616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474616 prefixEnd_3474616 := by exact prefixLift 3474616
  have htrace : WordTrace (prefixWord ++ tailWord_3474616) baseStart_3474616 baseEnd_3474616 := by
    simpa [prefixWord, tailWord_3474616, baseEnd_3474616] using wordTrace_append hprefix tailTrace_3474616
  have hstable : (prefixWord ++ tailWord_3474616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474616).length < 2 ^ (prefixWord ++ tailWord_3474616).sum := by decide
  have hdescent : baseEnd_3474616 < baseStart_3474616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474630 : List Nat := [6, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3474630 : Nat := 118140960795 + 3474630 * 2 ^ 59
def prefixEnd_3474630 : Nat := 4983230072969 + 3 ^ 40 * 3474630 * 2
def baseEnd_3474630 : Nat := 396478952562632383965661

theorem tailTrace_3474630 : CollatzResearch.WordTrace tailWord_3474630 prefixEnd_3474630 396478952562632383965661 := by
  unfold tailWord_3474630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960317731313012637642667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84486778268010936269710229 3960317731313012637642667)
  ·
    refine ⟨5940476596969518956464001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3960317731313012637642667 5940476596969518956464001)
    ·
      refine ⟨4455357447727139217348001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5940476596969518956464001 4455357447727139217348001)
      ·
        refine ⟨3341518085795354413011001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4455357447727139217348001 3341518085795354413011001)
        ·
          refine ⟨2506138564346515809758251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3341518085795354413011001 2506138564346515809758251)
          ·
            refine ⟨3759207846519773714637377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506138564346515809758251 3759207846519773714637377)
            ·
              refine ⟨2819405884889830285978033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3759207846519773714637377 2819405884889830285978033)
              ·
                refine ⟨2114554413667372714483525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819405884889830285978033 2114554413667372714483525)
                ·
                  refine ⟨396478952562632383965661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114554413667372714483525 396478952562632383965661)
                  ·
                    rfl

theorem cell22_3474630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3474630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474630 prefixEnd_3474630 := by exact prefixLift 3474630
  have htrace : WordTrace (prefixWord ++ tailWord_3474630) baseStart_3474630 baseEnd_3474630 := by
    simpa [prefixWord, tailWord_3474630, baseEnd_3474630] using wordTrace_append hprefix tailTrace_3474630
  have hstable : (prefixWord ++ tailWord_3474630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474630).length < 2 ^ (prefixWord ++ tailWord_3474630).sum := by decide
  have hdescent : baseEnd_3474630 < baseStart_3474630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474693 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3474693 : Nat := 118140960795 + 3474693 * 2 ^ 59
def prefixEnd_3474693 : Nat := 4983230072969 + 3 ^ 40 * 3474693 * 2
def baseEnd_3474693 : Nat := 1189458423875385987571789

theorem tailTrace_3474693 : CollatzResearch.WordTrace tailWord_3474693 prefixEnd_3474693 1189458423875385987571789 := by
  unfold tailWord_3474693
  simp only [CollatzResearch.WordTrace]
  refine ⟨126732465200788166164108733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84488310133858777442739155 126732465200788166164108733)
  ·
    refine ⟨47524674450295562311540775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126732465200788166164108733 47524674450295562311540775)
    ·
      refine ⟨71287011675443343467311163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47524674450295562311540775 71287011675443343467311163)
      ·
        refine ⟨106930517513165015200966745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71287011675443343467311163 106930517513165015200966745)
        ·
          refine ⟨80197888134873761400725059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106930517513165015200966745 80197888134873761400725059)
          ·
            refine ⟨120296832202310642101087589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80197888134873761400725059 120296832202310642101087589)
            ·
              refine ⟨22555656037933245393953923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120296832202310642101087589 22555656037933245393953923)
              ·
                refine ⟨33833484056899868090930885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22555656037933245393953923 33833484056899868090930885)
                ·
                  refine ⟨6343778260668725267049541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33833484056899868090930885 6343778260668725267049541)
                  ·
                    refine ⟨1189458423875385987571789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6343778260668725267049541 1189458423875385987571789)
                    ·
                      rfl

theorem cell22_3474693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3474693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474693 prefixEnd_3474693 := by exact prefixLift 3474693
  have htrace : WordTrace (prefixWord ++ tailWord_3474693) baseStart_3474693 baseEnd_3474693 := by
    simpa [prefixWord, tailWord_3474693, baseEnd_3474693] using wordTrace_append hprefix tailTrace_3474693
  have hstable : (prefixWord ++ tailWord_3474693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474693).length < 2 ^ (prefixWord ++ tailWord_3474693).sum := by decide
  have hdescent : baseEnd_3474693 < baseStart_3474693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474725 : List Nat := [1, 3, 1, 2, 4, 1, 4, 6]
def baseStart_3474725 : Nat := 118140960795 + 3474725 * 2 ^ 59
def prefixEnd_3474725 : Nat := 4983230072969 + 3 ^ 40 * 3474725 * 2
def baseEnd_3474725 : Nat := 132163264236594285641299

theorem tailTrace_3474725 : CollatzResearch.WordTrace tailWord_3474725 prefixEnd_3474725 132163264236594285641299 := by
  unfold tailWord_3474725
  simp only [CollatzResearch.WordTrace]
  refine ⟨126733632336672235629273629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84489088224448157086182419 126733632336672235629273629)
  ·
    refine ⟨47525112126252088360977611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126733632336672235629273629 47525112126252088360977611)
    ·
      refine ⟨71287668189378132541466417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47525112126252088360977611 71287668189378132541466417)
      ·
        refine ⟨53465751142033599406099813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71287668189378132541466417 53465751142033599406099813)
        ·
          refine ⟨10024828339131299888643715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53465751142033599406099813 10024828339131299888643715)
          ·
            refine ⟨15037242508696949832965573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10024828339131299888643715 15037242508696949832965573)
            ·
              refine ⟨2819482970380678093681045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15037242508696949832965573 2819482970380678093681045)
              ·
                refine ⟨132163264236594285641299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2819482970380678093681045 132163264236594285641299)
                ·
                  rfl

theorem cell22_3474725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 6].length) (baseStart_3474725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474725 prefixEnd_3474725 := by exact prefixLift 3474725
  have htrace : WordTrace (prefixWord ++ tailWord_3474725) baseStart_3474725 baseEnd_3474725 := by
    simpa [prefixWord, tailWord_3474725, baseEnd_3474725] using wordTrace_append hprefix tailTrace_3474725
  have hstable : (prefixWord ++ tailWord_3474725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474725).length < 2 ^ (prefixWord ++ tailWord_3474725).sum := by decide
  have hdescent : baseEnd_3474725 < baseStart_3474725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474757 : List Nat := [1, 3, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_3474757 : Nat := 118140960795 + 3474757 * 2 ^ 59
def prefixEnd_3474757 : Nat := 4983230072969 + 3 ^ 40 * 3474757 * 2
def baseEnd_3474757 : Nat := 1189480332383311153971593

theorem tailTrace_3474757 : CollatzResearch.WordTrace tailWord_3474757 prefixEnd_3474757 1189480332383311153971593 := by
  unfold tailWord_3474757
  simp only [CollatzResearch.WordTrace]
  refine ⟨126734799472556305094438525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84489866315037536729625683 126734799472556305094438525)
  ·
    refine ⟨47525549802208614410414447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126734799472556305094438525 47525549802208614410414447)
    ·
      refine ⟨71288324703312921615621671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47525549802208614410414447 71288324703312921615621671)
      ·
        refine ⟨106932487054969382423432507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71288324703312921615621671 106932487054969382423432507)
        ·
          refine ⟨160398730582454073635148761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106932487054969382423432507 160398730582454073635148761)
          ·
            refine ⟨120299047936840555226361571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160398730582454073635148761 120299047936840555226361571)
            ·
              refine ⟨180448571905260832839542357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120299047936840555226361571 180448571905260832839542357)
              ·
                refine ⟨2114631702014775384838387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 180448571905260832839542357 2114631702014775384838387)
                ·
                  refine ⟨3171947553022163077257581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2114631702014775384838387 3171947553022163077257581)
                  ·
                    refine ⟨1189480332383311153971593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3171947553022163077257581 1189480332383311153971593)
                    ·
                      rfl

theorem cell22_3474757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_3474757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474757 prefixEnd_3474757 := by exact prefixLift 3474757
  have htrace : WordTrace (prefixWord ++ tailWord_3474757) baseStart_3474757 baseEnd_3474757 := by
    simpa [prefixWord, tailWord_3474757, baseEnd_3474757] using wordTrace_append hprefix tailTrace_3474757
  have hstable : (prefixWord ++ tailWord_3474757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474757).length < 2 ^ (prefixWord ++ tailWord_3474757).sum := by decide
  have hdescent : baseEnd_3474757 < baseStart_3474757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474768 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_3474768 : Nat := 118140960795 + 3474768 * 2 ^ 59
def prefixEnd_3474768 : Nat := 4983230072969 + 3 ^ 40 * 3474768 * 2
def baseEnd_3474768 : Nat := 1189484097908110791946559

theorem tailTrace_3474768 : CollatzResearch.WordTrace tailWord_3474768 prefixEnd_3474768 1189484097908110791946559 := by
  unfold tailWord_3474768
  simp only [CollatzResearch.WordTrace]
  refine ⟨63367600337758226986544479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84490133783677635982059305 63367600337758226986544479)
  ·
    refine ⟨95051400506637340479816719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63367600337758226986544479 95051400506637340479816719)
    ·
      refine ⟨142577100759956010719725079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95051400506637340479816719 142577100759956010719725079)
      ·
        refine ⟨213865651139934016079587619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142577100759956010719725079 213865651139934016079587619)
        ·
          refine ⟨320798476709901024119381429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213865651139934016079587619 320798476709901024119381429)
          ·
            refine ⟨30074857191553221011192009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320798476709901024119381429 30074857191553221011192009)
            ·
              refine ⟨22556142893664915758394007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30074857191553221011192009 22556142893664915758394007)
              ·
                refine ⟨33834214340497373637591011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22556142893664915758394007 33834214340497373637591011)
                ·
                  refine ⟨50751321510746060456386517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33834214340497373637591011 50751321510746060456386517)
                  ·
                    refine ⟨1189484097908110791946559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50751321510746060456386517 1189484097908110791946559)
                    ·
                      rfl

theorem cell22_3474768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_3474768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474768 prefixEnd_3474768 := by exact prefixLift 3474768
  have htrace : WordTrace (prefixWord ++ tailWord_3474768) baseStart_3474768 baseEnd_3474768 := by
    simpa [prefixWord, tailWord_3474768, baseEnd_3474768] using wordTrace_append hprefix tailTrace_3474768
  have hstable : (prefixWord ++ tailWord_3474768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474768).length < 2 ^ (prefixWord ++ tailWord_3474768).sum := by decide
  have hdescent : baseEnd_3474768 < baseStart_3474768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474905 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 7]
def baseStart_3474905 : Nat := 118140960795 + 3474905 * 2 ^ 59
def prefixEnd_3474905 : Nat := 4983230072969 + 3 ^ 40 * 3474905 * 2
def baseEnd_3474905 : Nat := 396510331935962700423713

theorem tailTrace_3474905 : CollatzResearch.WordTrace tailWord_3474905 prefixEnd_3474905 396510331935962700423713 := by
  unfold tailWord_3474905
  simp only [CollatzResearch.WordTrace]
  refine ⟨126740197476020126370826169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84493464984013417580550779 126740197476020126370826169)
  ·
    refine ⟨95055148107015094778119627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126740197476020126370826169 95055148107015094778119627)
    ·
      refine ⟨142582722160522642167179441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95055148107015094778119627 142582722160522642167179441)
      ·
        refine ⟨106937041620391981625384581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142582722160522642167179441 106937041620391981625384581)
        ·
          refine ⟨20050695303823496554759609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106937041620391981625384581 20050695303823496554759609)
          ·
            refine ⟨15038021477867622416069707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20050695303823496554759609 15038021477867622416069707)
            ·
              refine ⟨22557032216801433624104561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15038021477867622416069707 22557032216801433624104561)
              ·
                refine ⟨16917774162601075218078421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22557032216801433624104561 16917774162601075218078421)
                ·
                  refine ⟨396510331935962700423713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16917774162601075218078421 396510331935962700423713)
                  ·
                    rfl

theorem cell22_3474905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_3474905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474905 prefixEnd_3474905 := by exact prefixLift 3474905
  have htrace : WordTrace (prefixWord ++ tailWord_3474905) baseStart_3474905 baseEnd_3474905 := by
    simpa [prefixWord, tailWord_3474905, baseEnd_3474905] using wordTrace_append hprefix tailTrace_3474905
  have hstable : (prefixWord ++ tailWord_3474905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474905).length < 2 ^ (prefixWord ++ tailWord_3474905).sum := by decide
  have hdescent : baseEnd_3474905 < baseStart_3474905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3474999 : List Nat := [1, 1, 3, 1, 2, 4, 2, 3, 2, 3]
def baseStart_3474999 : Nat := 118140960795 + 3474999 * 2 ^ 59
def prefixEnd_3474999 : Nat := 4983230072969 + 3 ^ 40 * 3474999 * 2
def baseEnd_3474999 : Nat := 1189563173928903189420851

theorem tailTrace_3474999 : CollatzResearch.WordTrace tailWord_3474999 prefixEnd_3474999 1189563173928903189420851 := by
  unfold tailWord_3474999
  simp only [CollatzResearch.WordTrace]
  refine ⟨126743625937679580424748051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84495750625119720283165367 126743625937679580424748051)
  ·
    refine ⟨190115438906519370637122077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126743625937679580424748051 190115438906519370637122077)
    ·
      refine ⟨71293289589944763988920779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190115438906519370637122077 71293289589944763988920779)
      ·
        refine ⟨106939934384917145983381169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71293289589944763988920779 106939934384917145983381169)
        ·
          refine ⟨80204950788687859487535877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106939934384917145983381169 80204950788687859487535877)
          ·
            refine ⟨15038428272878973653912977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80204950788687859487535877 15038428272878973653912977)
            ·
              refine ⟨11278821204659230240434733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15038428272878973653912977 11278821204659230240434733)
              ·
                refine ⟨4229557951747211340163025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11278821204659230240434733 4229557951747211340163025)
                ·
                  refine ⟨3172168463810408505122269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4229557951747211340163025 3172168463810408505122269)
                  ·
                    refine ⟨1189563173928903189420851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3172168463810408505122269 1189563173928903189420851)
                    ·
                      rfl

theorem cell22_3474999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_3474999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3474999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3474999 prefixEnd_3474999 := by exact prefixLift 3474999
  have htrace : WordTrace (prefixWord ++ tailWord_3474999) baseStart_3474999 baseEnd_3474999 := by
    simpa [prefixWord, tailWord_3474999, baseEnd_3474999] using wordTrace_append hprefix tailTrace_3474999
  have hstable : (prefixWord ++ tailWord_3474999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3474999).length < 2 ^ (prefixWord ++ tailWord_3474999).sum := by decide
  have hdescent : baseEnd_3474999 < baseStart_3474999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3474999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475044 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_3475044 : Nat := 118140960795 + 3475044 * 2 ^ 59
def prefixEnd_3475044 : Nat := 4983230072969 + 3 ^ 40 * 3475044 * 2
def baseEnd_3475044 : Nat := 1189578578348538072045713

theorem tailTrace_3475044 : CollatzResearch.WordTrace tailWord_3475044 prefixEnd_3475044 1189578578348538072045713 := by
  unfold tailWord_3475044
  simp only [CollatzResearch.WordTrace]
  refine ⟨63372633611258276555068093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84496844815011035406757457 63372633611258276555068093)
  ·
    refine ⟨23764737604221853708150535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63372633611258276555068093 23764737604221853708150535)
    ·
      refine ⟨35647106406332780562225803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23764737604221853708150535 35647106406332780562225803)
      ·
        refine ⟨53470659609499170843338705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35647106406332780562225803 53470659609499170843338705)
        ·
          refine ⟨40102994707124378132504029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53470659609499170843338705 40102994707124378132504029)
          ·
            refine ⟨15038623015171641799689011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40102994707124378132504029 15038623015171641799689011)
            ·
              refine ⟨22557934522757462699533517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15038623015171641799689011 22557934522757462699533517)
              ·
                refine ⟨8459225446034048512325069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22557934522757462699533517 8459225446034048512325069)
                ·
                  refine ⟨3172209542262768192121901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8459225446034048512325069 3172209542262768192121901)
                  ·
                    refine ⟨1189578578348538072045713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3172209542262768192121901 1189578578348538072045713)
                    ·
                      rfl

theorem cell22_3475044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_3475044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475044 prefixEnd_3475044 := by exact prefixLift 3475044
  have htrace : WordTrace (prefixWord ++ tailWord_3475044) baseStart_3475044 baseEnd_3475044 := by
    simpa [prefixWord, tailWord_3475044, baseEnd_3475044] using wordTrace_append hprefix tailTrace_3475044
  have hstable : (prefixWord ++ tailWord_3475044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475044).length < 2 ^ (prefixWord ++ tailWord_3475044).sum := by decide
  have hdescent : baseEnd_3475044 < baseStart_3475044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475057 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 5]
def baseStart_3475057 : Nat := 118140960795 + 3475057 * 2 ^ 59
def prefixEnd_3475057 : Nat := 4983230072969 + 3 ^ 40 * 3475057 * 2
def baseEnd_3475057 : Nat := 396527676171403457156891

theorem tailTrace_3475057 : CollatzResearch.WordTrace tailWord_3475057 prefixEnd_3475057 396527676171403457156891 := by
  unfold tailWord_3475057
  simp only [CollatzResearch.WordTrace]
  refine ⟨126745741371469456330359425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84497160914312970886906283 126745741371469456330359425)
  ·
    refine ⟨95059306028602092247769569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126745741371469456330359425 95059306028602092247769569)
    ·
      refine ⟨71294479521451569185827177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95059306028602092247769569 71294479521451569185827177)
      ·
        refine ⟨53470859641088676889370383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71294479521451569185827177 53470859641088676889370383)
        ·
          refine ⟨80206289461633015334055575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53470859641088676889370383 80206289461633015334055575)
          ·
            refine ⟨120309434192449523001083363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80206289461633015334055575 120309434192449523001083363)
            ·
              refine ⟨180464151288674284501625045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120309434192449523001083363 180464151288674284501625045)
              ·
                refine ⟨4229628545828303543006837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 180464151288674284501625045 4229628545828303543006837)
                ·
                  refine ⟨396527676171403457156891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4229628545828303543006837 396527676171403457156891)
                  ·
                    rfl

theorem cell22_3475057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_3475057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475057 prefixEnd_3475057 := by exact prefixLift 3475057
  have htrace : WordTrace (prefixWord ++ tailWord_3475057) baseStart_3475057 baseEnd_3475057 := by
    simpa [prefixWord, tailWord_3475057, baseEnd_3475057] using wordTrace_append hprefix tailTrace_3475057
  have hstable : (prefixWord ++ tailWord_3475057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475057).length < 2 ^ (prefixWord ++ tailWord_3475057).sum := by decide
  have hdescent : baseEnd_3475057 < baseStart_3475057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475061 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3475061 : Nat := 118140960795 + 3475061 * 2 ^ 59
def prefixEnd_3475061 : Nat := 4983230072969 + 3 ^ 40 * 3475061 * 2
def baseEnd_3475061 : Nat := 1189584397795955694370661

theorem tailTrace_3475061 : CollatzResearch.WordTrace tailWord_3475061 prefixEnd_3475061 1189584397795955694370661 := by
  unfold tailWord_3475061
  simp only [CollatzResearch.WordTrace]
  refine ⟨126745887263454965013505037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84497258175636643342336691 126745887263454965013505037)
  ·
    refine ⟨47529707723795611880064389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126745887263454965013505037 47529707723795611880064389)
    ·
      refine ⟨8911820198211677227512073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47529707723795611880064389 8911820198211677227512073)
      ·
        refine ⟨6683865148658757920634055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8911820198211677227512073 6683865148658757920634055)
        ·
          refine ⟨10025797722988136880951083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6683865148658757920634055 10025797722988136880951083)
          ·
            refine ⟨15038696584482205321426625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10025797722988136880951083 15038696584482205321426625)
            ·
              refine ⟨11279022438361653991069969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15038696584482205321426625 11279022438361653991069969)
              ·
                refine ⟨8459266828771240493302477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11279022438361653991069969 8459266828771240493302477)
                ·
                  refine ⟨3172225060789215184988429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8459266828771240493302477 3172225060789215184988429)
                  ·
                    refine ⟨1189584397795955694370661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3172225060789215184988429 1189584397795955694370661)
                    ·
                      rfl

theorem cell22_3475061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3475061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475061 prefixEnd_3475061 := by exact prefixLift 3475061
  have htrace : WordTrace (prefixWord ++ tailWord_3475061) baseStart_3475061 baseEnd_3475061 := by
    simpa [prefixWord, tailWord_3475061, baseEnd_3475061] using wordTrace_append hprefix tailTrace_3475061
  have hstable : (prefixWord ++ tailWord_3475061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475061).length < 2 ^ (prefixWord ++ tailWord_3475061).sum := by decide
  have hdescent : baseEnd_3475061 < baseStart_3475061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475134 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_3475134 : Nat := 118140960795 + 3475134 * 2 ^ 59
def prefixEnd_3475134 : Nat := 4983230072969 + 3 ^ 40 * 3475134 * 2
def baseEnd_3475134 : Nat := 1189609387187807837295437

theorem tailTrace_3475134 : CollatzResearch.WordTrace tailWord_3475134 prefixEnd_3475134 1189609387187807837295437 := by
  unfold tailWord_3475134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15843568724023812310114057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84499033194793665653941637 15843568724023812310114057)
  ·
    refine ⟨11882676543017859232585543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15843568724023812310114057 11882676543017859232585543)
    ·
      refine ⟨17824014814526788848878315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11882676543017859232585543 17824014814526788848878315)
      ·
        refine ⟨26736022221790183273317473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17824014814526788848878315 26736022221790183273317473)
        ·
          refine ⟨20052016666342637454988105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26736022221790183273317473 20052016666342637454988105)
          ·
            refine ⟨15039012499756978091241079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20052016666342637454988105 15039012499756978091241079)
            ·
              refine ⟨22558518749635467136861619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15039012499756978091241079 22558518749635467136861619)
              ·
                refine ⟨33837778124453200705292429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22558518749635467136861619 33837778124453200705292429)
                ·
                  refine ⟨12689166796669950264484661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33837778124453200705292429 12689166796669950264484661)
                  ·
                    refine ⟨1189609387187807837295437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12689166796669950264484661 1189609387187807837295437)
                    ·
                      rfl

theorem cell22_3475134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_3475134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475134 prefixEnd_3475134 := by exact prefixLift 3475134
  have htrace : WordTrace (prefixWord ++ tailWord_3475134) baseStart_3475134 baseEnd_3475134 := by
    simpa [prefixWord, tailWord_3475134, baseEnd_3475134] using wordTrace_append hprefix tailTrace_3475134
  have hstable : (prefixWord ++ tailWord_3475134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475134).length < 2 ^ (prefixWord ++ tailWord_3475134).sum := by decide
  have hdescent : baseEnd_3475134 < baseStart_3475134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475153 : List Nat := [1, 2, 2, 1, 2, 6, 2, 2, 4]
def baseStart_3475153 : Nat := 118140960795 + 3475153 * 2 ^ 59
def prefixEnd_3475153 : Nat := 4983230072969 + 3 ^ 40 * 3475153 * 2
def baseEnd_3475153 : Nat := 396538630425366040356793

theorem tailTrace_3475153 : CollatzResearch.WordTrace tailWord_3475153 prefixEnd_3475153 396538630425366040356793 := by
  unfold tailWord_3475153
  simp only [CollatzResearch.WordTrace]
  refine ⟨126749242779121664725854113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84499495186081109817236075 126749242779121664725854113)
  ·
    refine ⟨95061932084341248544390585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126749242779121664725854113 95061932084341248544390585)
    ·
      refine ⟨71296449063255936408292939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95061932084341248544390585 71296449063255936408292939)
      ·
        refine ⟨106944673594883904612439409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71296449063255936408292939 106944673594883904612439409)
        ·
          refine ⟨80208505196162928459329557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106944673594883904612439409 80208505196162928459329557)
          ·
            refine ⟨3759773681070137271531073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80208505196162928459329557 3759773681070137271531073)
            ·
              refine ⟨2819830260802602953648305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3759773681070137271531073 2819830260802602953648305)
              ·
                refine ⟨2114872695601952215236229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819830260802602953648305 2114872695601952215236229)
                ·
                  refine ⟨396538630425366040356793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114872695601952215236229 396538630425366040356793)
                  ·
                    rfl

theorem cell22_3475153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_3475153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475153 prefixEnd_3475153 := by exact prefixLift 3475153
  have htrace : WordTrace (prefixWord ++ tailWord_3475153) baseStart_3475153 baseEnd_3475153 := by
    simpa [prefixWord, tailWord_3475153, baseEnd_3475153] using wordTrace_append hprefix tailTrace_3475153
  have hstable : (prefixWord ++ tailWord_3475153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475153).length < 2 ^ (prefixWord ++ tailWord_3475153).sum := by decide
  have hdescent : baseEnd_3475153 < baseStart_3475153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475177 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_3475177 : Nat := 118140960795 + 3475177 * 2 ^ 59
def prefixEnd_3475177 : Nat := 4983230072969 + 3 ^ 40 * 3475177 * 2
def baseEnd_3475177 : Nat := 1189624106966570058470305

theorem tailTrace_3475177 : CollatzResearch.WordTrace tailWord_3475177 prefixEnd_3475177 1189624106966570058470305 := by
  unfold tailWord_3475177
  simp only [CollatzResearch.WordTrace]
  refine ⟨126750118131034716824727785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84500078754023144549818523 126750118131034716824727785)
  ·
    refine ⟨95062588598276037618545839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126750118131034716824727785 95062588598276037618545839)
    ·
      refine ⟨142593882897414056427818759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95062588598276037618545839 142593882897414056427818759)
      ·
        refine ⟨213890824346121084641728139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142593882897414056427818759 213890824346121084641728139)
        ·
          refine ⟨320836236519181626962592209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213890824346121084641728139 320836236519181626962592209)
          ·
            refine ⟨240627177389386220221944157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320836236519181626962592209 240627177389386220221944157)
            ·
              refine ⟨90235191521019832583229059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240627177389386220221944157 90235191521019832583229059)
              ·
                refine ⟨135352787281529748874843589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90235191521019832583229059 135352787281529748874843589)
                ·
                  refine ⟨25378647615286827914033173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135352787281529748874843589 25378647615286827914033173)
                  ·
                    refine ⟨1189624106966570058470305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25378647615286827914033173 1189624106966570058470305)
                    ·
                      rfl

theorem cell22_3475177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_3475177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475177 prefixEnd_3475177 := by exact prefixLift 3475177
  have htrace : WordTrace (prefixWord ++ tailWord_3475177) baseStart_3475177 baseEnd_3475177 := by
    simpa [prefixWord, tailWord_3475177, baseEnd_3475177] using wordTrace_append hprefix tailTrace_3475177
  have hstable : (prefixWord ++ tailWord_3475177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475177).length < 2 ^ (prefixWord ++ tailWord_3475177).sum := by decide
  have hdescent : baseEnd_3475177 < baseStart_3475177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475179 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 5, 3]
def baseStart_3475179 : Nat := 118140960795 + 3475179 * 2 ^ 59
def prefixEnd_3475179 : Nat := 4983230072969 + 3 ^ 40 * 3475179 * 2
def baseEnd_3475179 : Nat := 1189624791607442719920299

theorem tailTrace_3475179 : CollatzResearch.WordTrace tailWord_3475179 prefixEnd_3475179 1189624791607442719920299 := by
  unfold tailWord_3475179
  simp only [CollatzResearch.WordTrace]
  refine ⟨126750191077027471166300591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84500127384684980777533727 126750191077027471166300591)
  ·
    refine ⟨190125286615541206749450887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126750191077027471166300591 190125286615541206749450887)
    ·
      refine ⟨285187929923311810124176331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190125286615541206749450887 285187929923311810124176331)
      ·
        refine ⟨427781894884967715186264497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285187929923311810124176331 427781894884967715186264497)
        ·
          refine ⟨320836421163725786389698373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427781894884967715186264497 320836421163725786389698373)
          ·
            refine ⟨60156828968198584948068445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320836421163725786389698373 60156828968198584948068445)
            ·
              refine ⟨22558810863074469355525667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60156828968198584948068445 22558810863074469355525667)
              ·
                refine ⟨33838216294611704033288501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22558810863074469355525667 33838216294611704033288501)
                ·
                  refine ⟨3172332777619847253120797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33838216294611704033288501 3172332777619847253120797)
                  ·
                    refine ⟨1189624791607442719920299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3172332777619847253120797 1189624791607442719920299)
                    ·
                      rfl

theorem cell22_3475179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 3].length) (baseStart_3475179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475179 prefixEnd_3475179 := by exact prefixLift 3475179
  have htrace : WordTrace (prefixWord ++ tailWord_3475179) baseStart_3475179 baseEnd_3475179 := by
    simpa [prefixWord, tailWord_3475179, baseEnd_3475179] using wordTrace_append hprefix tailTrace_3475179
  have hstable : (prefixWord ++ tailWord_3475179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475179).length < 2 ^ (prefixWord ++ tailWord_3475179).sum := by decide
  have hdescent : baseEnd_3475179 < baseStart_3475179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475181 : List Nat := [1, 5, 1, 2, 1, 3, 3, 6]
def baseStart_3475181 : Nat := 118140960795 + 3475181 * 2 ^ 59
def prefixEnd_3475181 : Nat := 4983230072969 + 3 ^ 40 * 3475181 * 2
def baseEnd_3475181 : Nat := 132180608472035042374477

theorem tailTrace_3475181 : CollatzResearch.WordTrace tailWord_3475181 prefixEnd_3475181 132180608472035042374477 := by
  unfold tailWord_3475181
  simp only [CollatzResearch.WordTrace]
  refine ⟨126750264023020225507873397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84500176015346817005248931 126750264023020225507873397)
  ·
    refine ⟨11882837252158146141363131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126750264023020225507873397 11882837252158146141363131)
    ·
      refine ⟨17824255878237219212044697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11882837252158146141363131 17824255878237219212044697)
      ·
        refine ⟨13368191908677914409033523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17824255878237219212044697 13368191908677914409033523)
        ·
          refine ⟨20052287863016871613550285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13368191908677914409033523 20052287863016871613550285)
          ·
            refine ⟨7519607948631326855081357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20052287863016871613550285 7519607948631326855081357)
            ·
              refine ⟨2819852980736747570655509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7519607948631326855081357 2819852980736747570655509)
              ·
                refine ⟨132180608472035042374477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2819852980736747570655509 132180608472035042374477)
                ·
                  rfl

theorem cell22_3475181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 6].length) (baseStart_3475181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475181 prefixEnd_3475181 := by exact prefixLift 3475181
  have htrace : WordTrace (prefixWord ++ tailWord_3475181) baseStart_3475181 baseEnd_3475181 := by
    simpa [prefixWord, tailWord_3475181, baseEnd_3475181] using wordTrace_append hprefix tailTrace_3475181
  have hstable : (prefixWord ++ tailWord_3475181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475181).length < 2 ^ (prefixWord ++ tailWord_3475181).sum := by decide
  have hdescent : baseEnd_3475181 < baseStart_3475181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475224 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_3475224 : Nat := 118140960795 + 3475224 * 2 ^ 59
def prefixEnd_3475224 : Nat := 4983230072969 + 3 ^ 40 * 3475224 * 2
def baseEnd_3475224 : Nat := 1189640196027077602545161

theorem tailTrace_3475224 : CollatzResearch.WordTrace tailWord_3475224 prefixEnd_3475224 1189640196027077602545161 := by
  unfold tailWord_3475224
  simp only [CollatzResearch.WordTrace]
  refine ⟨63375916180932221925844363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84501221574576295901125817 63375916180932221925844363)
  ·
    refine ⟨95063874271398332888766545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63375916180932221925844363 95063874271398332888766545)
    ·
      refine ⟨71297905703548749666574909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95063874271398332888766545 71297905703548749666574909)
      ·
        refine ⟨26736714638830781124965591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71297905703548749666574909 26736714638830781124965591)
        ·
          refine ⟨40105071958246171687448387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26736714638830781124965591 40105071958246171687448387)
          ·
            refine ⟨60157607937369257531172581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40105071958246171687448387 60157607937369257531172581)
            ·
              refine ⟨11279551488256735787094859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60157607937369257531172581 11279551488256735787094859)
              ·
                refine ⟨16919327232385103680642289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11279551488256735787094859 16919327232385103680642289)
                ·
                  refine ⟨12689495424288827760481717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16919327232385103680642289 12689495424288827760481717)
                  ·
                    refine ⟨1189640196027077602545161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12689495424288827760481717 1189640196027077602545161)
                    ·
                      rfl

theorem cell22_3475224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_3475224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475224 prefixEnd_3475224 := by exact prefixLift 3475224
  have htrace : WordTrace (prefixWord ++ tailWord_3475224) baseStart_3475224 baseEnd_3475224 := by
    simpa [prefixWord, tailWord_3475224, baseEnd_3475224] using wordTrace_append hprefix tailTrace_3475224
  have hstable : (prefixWord ++ tailWord_3475224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475224).length < 2 ^ (prefixWord ++ tailWord_3475224).sum := by decide
  have hdescent : baseEnd_3475224 < baseStart_3475224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475256 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_3475256 : Nat := 118140960795 + 3475256 * 2 ^ 59
def prefixEnd_3475256 : Nat := 4983230072969 + 3 ^ 40 * 3475256 * 2
def baseEnd_3475256 : Nat := 1189651150281040185745063

theorem tailTrace_3475256 : CollatzResearch.WordTrace tailWord_3475256 prefixEnd_3475256 1189651150281040185745063 := by
  unfold tailWord_3475256
  simp only [CollatzResearch.WordTrace]
  refine ⟨63376499748874256658426811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84501999665165675544569081 63376499748874256658426811)
  ·
    refine ⟨95064749623311384987640217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63376499748874256658426811 95064749623311384987640217)
    ·
      refine ⟨71298562217483538740730163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95064749623311384987640217 71298562217483538740730163)
      ·
        refine ⟨106947843326225308111095245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71298562217483538740730163 106947843326225308111095245)
        ·
          refine ⟨40105441247334490541660717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106947843326225308111095245 40105441247334490541660717)
          ·
            refine ⟨15039540467750433953122769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40105441247334490541660717 15039540467750433953122769)
            ·
              refine ⟨11279655350812825464842077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15039540467750433953122769 11279655350812825464842077)
              ·
                refine ⟨4229870756554809549315779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11279655350812825464842077 4229870756554809549315779)
                ·
                  refine ⟨6344806134832214323973669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229870756554809549315779 6344806134832214323973669)
                  ·
                    refine ⟨1189651150281040185745063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6344806134832214323973669 1189651150281040185745063)
                    ·
                      rfl

theorem cell22_3475256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_3475256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475256 prefixEnd_3475256 := by exact prefixLift 3475256
  have htrace : WordTrace (prefixWord ++ tailWord_3475256) baseStart_3475256 baseEnd_3475256 := by
    simpa [prefixWord, tailWord_3475256, baseEnd_3475256] using wordTrace_append hprefix tailTrace_3475256
  have hstable : (prefixWord ++ tailWord_3475256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475256).length < 2 ^ (prefixWord ++ tailWord_3475256).sum := by decide
  have hdescent : baseEnd_3475256 < baseStart_3475256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475271 : List Nat := [1, 1, 4, 1, 2, 1, 2, 6, 4]
def baseStart_3475271 : Nat := 118140960795 + 3475271 * 2 ^ 59
def prefixEnd_3475271 : Nat := 4983230072969 + 3 ^ 40 * 3475271 * 2
def baseEnd_3475271 : Nat := 396552095029195048873339

theorem tailTrace_3475271 : CollatzResearch.WordTrace tailWord_3475271 prefixEnd_3475271 396552095029195048873339 := by
  unfold tailWord_3475271
  simp only [CollatzResearch.WordTrace]
  refine ⟨126753546592694170878649667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84502364395129447252433111 126753546592694170878649667)
  ·
    refine ⟨190130319889041256317974501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126753546592694170878649667 190130319889041256317974501)
    ·
      refine ⟨35649434979195235559620219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190130319889041256317974501 35649434979195235559620219)
      ·
        refine ⟨53474152468792853339430329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35649434979195235559620219 53474152468792853339430329)
        ·
          refine ⟨40105614351594640004572747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53474152468792853339430329 40105614351594640004572747)
          ·
            refine ⟨60158421527391960006859121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40105614351594640004572747 60158421527391960006859121)
            ·
              refine ⟨45118816145543970005144341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60158421527391960006859121 45118816145543970005144341)
              ·
                refine ⟨2114944506822373593991141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45118816145543970005144341 2114944506822373593991141)
                ·
                  refine ⟨396552095029195048873339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114944506822373593991141 396552095029195048873339)
                  ·
                    rfl

theorem cell22_3475271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 4].length) (baseStart_3475271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475271 prefixEnd_3475271 := by exact prefixLift 3475271
  have htrace : WordTrace (prefixWord ++ tailWord_3475271) baseStart_3475271 baseEnd_3475271 := by
    simpa [prefixWord, tailWord_3475271, baseEnd_3475271] using wordTrace_append hprefix tailTrace_3475271
  have hstable : (prefixWord ++ tailWord_3475271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475271).length < 2 ^ (prefixWord ++ tailWord_3475271).sum := by decide
  have hdescent : baseEnd_3475271 < baseStart_3475271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475348 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3475348 : Nat := 118140960795 + 3475348 * 2 ^ 59
def prefixEnd_3475348 : Nat := 4983230072969 + 3 ^ 40 * 3475348 * 2
def baseEnd_3475348 : Nat := 1189682643761182612444781

theorem tailTrace_3475348 : CollatzResearch.WordTrace tailWord_3475348 prefixEnd_3475348 1189682643761182612444781 := by
  unfold tailWord_3475348
  simp only [CollatzResearch.WordTrace]
  refine ⟨63378177506707606514601349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84504236675610142019468465 63378177506707606514601349)
  ·
    refine ⟨11883408282507676221487753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63378177506707606514601349 11883408282507676221487753)
    ·
      refine ⟨8912556211880757166115815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11883408282507676221487753 8912556211880757166115815)
      ·
        refine ⟨13368834317821135749173723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8912556211880757166115815 13368834317821135749173723)
        ·
          refine ⟨20053251476731703623760585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13368834317821135749173723 20053251476731703623760585)
          ·
            refine ⟨15039938607548777717820439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20053251476731703623760585 15039938607548777717820439)
            ·
              refine ⟨22559907911323166576730659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15039938607548777717820439 22559907911323166576730659)
              ·
                refine ⟨33839861866984749865095989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22559907911323166576730659 33839861866984749865095989)
                ·
                  refine ⟨3172487050029820299852749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33839861866984749865095989 3172487050029820299852749)
                  ·
                    refine ⟨1189682643761182612444781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3172487050029820299852749 1189682643761182612444781)
                    ·
                      rfl

theorem cell22_3475348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3475348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475348 prefixEnd_3475348 := by exact prefixLift 3475348
  have htrace : WordTrace (prefixWord ++ tailWord_3475348) baseStart_3475348 baseEnd_3475348 := by
    simpa [prefixWord, tailWord_3475348, baseEnd_3475348] using wordTrace_append hprefix tailTrace_3475348
  have hstable : (prefixWord ++ tailWord_3475348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475348).length < 2 ^ (prefixWord ++ tailWord_3475348).sum := by decide
  have hdescent : baseEnd_3475348 < baseStart_3475348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475352 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 2, 4]
def baseStart_3475352 : Nat := 118140960795 + 3475352 * 2 ^ 59
def prefixEnd_3475352 : Nat := 4983230072969 + 3 ^ 40 * 3475352 * 2
def baseEnd_3475352 : Nat := 1189684013042927935344769

theorem tailTrace_3475352 : CollatzResearch.WordTrace tailWord_3475352 prefixEnd_3475352 1189684013042927935344769 := by
  unfold tailWord_3475352
  simp only [CollatzResearch.WordTrace]
  refine ⟨63378250452700360856174155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84504333936933814474898873 63378250452700360856174155)
  ·
    refine ⟨95067375679050541284261233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63378250452700360856174155 95067375679050541284261233)
    ·
      refine ⟨71300531759287905963195925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95067375679050541284261233 71300531759287905963195925)
      ·
        refine ⟨3342212426216620592024809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71300531759287905963195925 3342212426216620592024809)
        ·
          refine ⟨2506659319662465444018607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3342212426216620592024809 2506659319662465444018607)
          ·
            refine ⟨3759988979493698166027911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506659319662465444018607 3759988979493698166027911)
            ·
              refine ⟨5639983469240547249041867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3759988979493698166027911 5639983469240547249041867)
              ·
                refine ⟨8459975203860820873562801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639983469240547249041867 8459975203860820873562801)
                ·
                  refine ⟨6344981402895615655172101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8459975203860820873562801 6344981402895615655172101)
                  ·
                    refine ⟨1189684013042927935344769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6344981402895615655172101 1189684013042927935344769)
                    ·
                      rfl

theorem cell22_3475352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 2, 4].length) (baseStart_3475352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475352 prefixEnd_3475352 := by exact prefixLift 3475352
  have htrace : WordTrace (prefixWord ++ tailWord_3475352) baseStart_3475352 baseEnd_3475352 := by
    simpa [prefixWord, tailWord_3475352, baseEnd_3475352] using wordTrace_append hprefix tailTrace_3475352
  have hstable : (prefixWord ++ tailWord_3475352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475352).length < 2 ^ (prefixWord ++ tailWord_3475352).sum := by decide
  have hdescent : baseEnd_3475352 < baseStart_3475352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475406 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_3475406 : Nat := 118140960795 + 3475406 * 2 ^ 59
def prefixEnd_3475406 : Nat := 4983230072969 + 3 ^ 40 * 3475406 * 2
def baseEnd_3475406 : Nat := 396567499448829931498201

theorem tailTrace_3475406 : CollatzResearch.WordTrace tailWord_3475406 prefixEnd_3475406 396567499448829931498201 := by
  unfold tailWord_3475406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15844808805900636116851759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84505646964803392623209381 15844808805900636116851759)
  ·
    refine ⟨23767213208850954175277639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15844808805900636116851759 23767213208850954175277639)
    ·
      refine ⟨35650819813276431262916459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23767213208850954175277639 35650819813276431262916459)
      ·
        refine ⟨53476229719914646894374689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35650819813276431262916459 53476229719914646894374689)
        ·
          refine ⟨40107172289935985170781017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53476229719914646894374689 40107172289935985170781017)
          ·
            refine ⟨30080379217451988878085763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40107172289935985170781017 30080379217451988878085763)
            ·
              refine ⟨45120568826177983317128645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30080379217451988878085763 45120568826177983317128645)
              ·
                refine ⟨8460106654908371871961621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45120568826177983317128645 8460106654908371871961621)
                ·
                  refine ⟨396567499448829931498201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8460106654908371871961621 396567499448829931498201)
                  ·
                    rfl

theorem cell22_3475406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_3475406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475406 prefixEnd_3475406 := by exact prefixLift 3475406
  have htrace : WordTrace (prefixWord ++ tailWord_3475406) baseStart_3475406 baseEnd_3475406 := by
    simpa [prefixWord, tailWord_3475406, baseEnd_3475406] using wordTrace_append hprefix tailTrace_3475406
  have hstable : (prefixWord ++ tailWord_3475406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475406).length < 2 ^ (prefixWord ++ tailWord_3475406).sum := by decide
  have hdescent : baseEnd_3475406 < baseStart_3475406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475498 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3475498 : Nat := 118140960795 + 3475498 * 2 ^ 59
def prefixEnd_3475498 : Nat := 4983230072969 + 3 ^ 40 * 3475498 * 2
def baseEnd_3475498 : Nat := 1189733991826632221194321

theorem tailTrace_3475498 : CollatzResearch.WordTrace tailWord_3475498 prefixEnd_3475498 1189733991826632221194321 := by
  unfold tailWord_3475498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31690456490717947161790787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84507883975247859098108765 31690456490717947161790787)
  ·
    refine ⟨47535684736076920742686181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31690456490717947161790787 47535684736076920742686181)
    ·
      refine ⟨8912940888014422639253659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47535684736076920742686181 8912940888014422639253659)
      ·
        refine ⟨13369411332021633958880489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8912940888014422639253659 13369411332021633958880489)
        ·
          refine ⟨10027058499016225469160367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13369411332021633958880489 10027058499016225469160367)
          ·
            refine ⟨15040587748524338203740551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027058499016225469160367 15040587748524338203740551)
            ·
              refine ⟨22560881622786507305610827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15040587748524338203740551 22560881622786507305610827)
              ·
                refine ⟨33841322434179760958416241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22560881622786507305610827 33841322434179760958416241)
                ·
                  refine ⟨25380991825634820718812181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33841322434179760958416241 25380991825634820718812181)
                  ·
                    refine ⟨1189733991826632221194321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25380991825634820718812181 1189733991826632221194321)
                    ·
                      rfl

theorem cell22_3475498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3475498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475498 prefixEnd_3475498 := by exact prefixLift 3475498
  have htrace : WordTrace (prefixWord ++ tailWord_3475498) baseStart_3475498 baseEnd_3475498 := by
    simpa [prefixWord, tailWord_3475498, baseEnd_3475498] using wordTrace_append hprefix tailTrace_3475498
  have hstable : (prefixWord ++ tailWord_3475498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475498).length < 2 ^ (prefixWord ++ tailWord_3475498).sum := by decide
  have hdescent : baseEnd_3475498 < baseStart_3475498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475511 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 1, 7]
def baseStart_3475511 : Nat := 118140960795 + 3475511 * 2 ^ 59
def prefixEnd_3475511 : Nat := 4983230072969 + 3 ^ 40 * 3475511 * 2
def baseEnd_3475511 : Nat := 1189738441992304520619281

theorem tailTrace_3475511 : CollatzResearch.WordTrace tailWord_3475511 prefixEnd_3475511 1189738441992304520619281 := by
  unfold tailWord_3475511
  simp only [CollatzResearch.WordTrace]
  refine ⟨126762300111824691867386387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84508200074549794578257591 126762300111824691867386387)
  ·
    refine ⟨190143450167737037801079581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126762300111824691867386387 190143450167737037801079581)
    ·
      refine ⟨71303793812901389175404843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190143450167737037801079581 71303793812901389175404843)
      ·
        refine ⟨106955690719352083763107265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71303793812901389175404843 106955690719352083763107265)
        ·
          refine ⟨80216768039514062822330449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106955690719352083763107265 80216768039514062822330449)
          ·
            refine ⟨60162576029635547116747837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80216768039514062822330449 60162576029635547116747837)
            ·
              refine ⟨22560966011113330168780439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60162576029635547116747837 22560966011113330168780439)
              ·
                refine ⟨33841449016669995253170659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22560966011113330168780439 33841449016669995253170659)
                ·
                  refine ⟨50762173525004992879755989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33841449016669995253170659 50762173525004992879755989)
                  ·
                    refine ⟨1189738441992304520619281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50762173525004992879755989 1189738441992304520619281)
                    ·
                      rfl

theorem cell22_3475511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_3475511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475511 prefixEnd_3475511 := by exact prefixLift 3475511
  have htrace : WordTrace (prefixWord ++ tailWord_3475511) baseStart_3475511 baseEnd_3475511 := by
    simpa [prefixWord, tailWord_3475511, baseEnd_3475511] using wordTrace_append hprefix tailTrace_3475511
  have hstable : (prefixWord ++ tailWord_3475511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475511).length < 2 ^ (prefixWord ++ tailWord_3475511).sum := by decide
  have hdescent : baseEnd_3475511 < baseStart_3475511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475588 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3475588 : Nat := 118140960795 + 3475588 * 2 ^ 59
def prefixEnd_3475588 : Nat := 4983230072969 + 3 ^ 40 * 3475588 * 2
def baseEnd_3475588 : Nat := 1189764800665901986444045

theorem tailTrace_3475588 : CollatzResearch.WordTrace tailWord_3475588 prefixEnd_3475588 1189764800665901986444045 := by
  unfold tailWord_3475588
  simp only [CollatzResearch.WordTrace]
  refine ⟨63382554266272867008969709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84510072355030489345292945 63382554266272867008969709)
  ·
    refine ⟨23768457849852325128363641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63382554266272867008969709 23768457849852325128363641)
    ·
      refine ⟨17826343387389243846272731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23768457849852325128363641 17826343387389243846272731)
      ·
        refine ⟨26739515081083865769409097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17826343387389243846272731 26739515081083865769409097)
        ·
          refine ⟨20054636310812899327056823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26739515081083865769409097 20054636310812899327056823)
          ·
            refine ⟨30081954466219348990585235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20054636310812899327056823 30081954466219348990585235)
            ·
              refine ⟨45122931699329023485877853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30081954466219348990585235 45122931699329023485877853)
              ·
                refine ⟨16921099387248383807204195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45122931699329023485877853 16921099387248383807204195)
                ·
                  refine ⟨25381649080872575710806293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16921099387248383807204195 25381649080872575710806293)
                  ·
                    refine ⟨1189764800665901986444045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25381649080872575710806293 1189764800665901986444045)
                    ·
                      rfl

theorem cell22_3475588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3475588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475588 prefixEnd_3475588 := by exact prefixLift 3475588
  have htrace : WordTrace (prefixWord ++ tailWord_3475588) baseStart_3475588 baseEnd_3475588 := by
    simpa [prefixWord, tailWord_3475588, baseEnd_3475588] using wordTrace_append hprefix tailTrace_3475588
  have hstable : (prefixWord ++ tailWord_3475588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475588).length < 2 ^ (prefixWord ++ tailWord_3475588).sum := by decide
  have hdescent : baseEnd_3475588 < baseStart_3475588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475592 : List Nat := [2, 1, 3, 4, 1, 1, 3, 3, 4]
def baseStart_3475592 : Nat := 118140960795 + 3475592 * 2 ^ 59
def prefixEnd_3475592 : Nat := 4983230072969 + 3 ^ 40 * 3475592 * 2
def baseEnd_3475592 : Nat := 396588723315882436448011

theorem tailTrace_3475592 : CollatzResearch.WordTrace tailWord_3475592 prefixEnd_3475592 396588723315882436448011 := by
  unfold tailWord_3475592
  simp only [CollatzResearch.WordTrace]
  refine ⟨63382627212265621350542515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84510169616354161800723353 63382627212265621350542515)
  ·
    refine ⟨95073940818398432025813773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63382627212265621350542515 95073940818398432025813773)
    ·
      refine ⟨35652727806899412009680165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95073940818398432025813773 35652727806899412009680165)
      ·
        refine ⟨6684886463793639751815031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35652727806899412009680165 6684886463793639751815031)
        ·
          refine ⟨10027329695690459627722547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684886463793639751815031 10027329695690459627722547)
          ·
            refine ⟨15040994543535689441583821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027329695690459627722547 15040994543535689441583821)
            ·
              refine ⟨5640372953825883540593933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15040994543535689441583821 5640372953825883540593933)
              ·
                refine ⟨2115139857684706327722725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5640372953825883540593933 2115139857684706327722725)
                ·
                  refine ⟨396588723315882436448011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115139857684706327722725 396588723315882436448011)
                  ·
                    rfl

theorem cell22_3475592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 4].length) (baseStart_3475592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475592 prefixEnd_3475592 := by exact prefixLift 3475592
  have htrace : WordTrace (prefixWord ++ tailWord_3475592) baseStart_3475592 baseEnd_3475592 := by
    simpa [prefixWord, tailWord_3475592, baseEnd_3475592] using wordTrace_append hprefix tailTrace_3475592
  have hstable : (prefixWord ++ tailWord_3475592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475592).length < 2 ^ (prefixWord ++ tailWord_3475592).sum := by decide
  have hdescent : baseEnd_3475592 < baseStart_3475592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475620 : List Nat := [2, 3, 1, 2, 4, 1, 2, 7]
def baseStart_3475620 : Nat := 118140960795 + 3475620 * 2 ^ 59
def prefixEnd_3475620 : Nat := 4983230072969 + 3 ^ 40 * 3475620 * 2
def baseEnd_3475620 : Nat := 132197306102207174404883

theorem tailTrace_3475620 : CollatzResearch.WordTrace tailWord_3475620 prefixEnd_3475620 132197306102207174404883 := by
  unfold tailWord_3475620
  simp only [CollatzResearch.WordTrace]
  refine ⟨63383137834214901741552157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84510850445619868988736209 63383137834214901741552157)
  ·
    refine ⟨23768676687830588153082059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63383137834214901741552157 23768676687830588153082059)
    ·
      refine ⟨35653015031745882229623089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23768676687830588153082059 35653015031745882229623089)
      ·
        refine ⟨26739761273809411672217317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35653015031745882229623089 26739761273809411672217317)
        ·
          refine ⟨5013705238839264688540747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26739761273809411672217317 5013705238839264688540747)
          ·
            refine ⟨7520557858258897032811121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013705238839264688540747 7520557858258897032811121)
            ·
              refine ⟨5640418393694172774608341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7520557858258897032811121 5640418393694172774608341)
              ·
                refine ⟨132197306102207174404883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5640418393694172774608341 132197306102207174404883)
                ·
                  rfl

theorem cell22_3475620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 7].length) (baseStart_3475620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475620 prefixEnd_3475620 := by exact prefixLift 3475620
  have htrace : WordTrace (prefixWord ++ tailWord_3475620) baseStart_3475620 baseEnd_3475620 := by
    simpa [prefixWord, tailWord_3475620, baseEnd_3475620] using wordTrace_append hprefix tailTrace_3475620
  have hstable : (prefixWord ++ tailWord_3475620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475620).length < 2 ^ (prefixWord ++ tailWord_3475620).sum := by decide
  have hdescent : baseEnd_3475620 < baseStart_3475620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475663 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 2, 5]
def baseStart_3475663 : Nat := 118140960795 + 3475663 * 2 ^ 59
def prefixEnd_3475663 : Nat := 4983230072969 + 3 ^ 40 * 3475663 * 2
def baseEnd_3475663 : Nat := 1189790474698626790818815

theorem tailTrace_3475663 : CollatzResearch.WordTrace tailWord_3475663 prefixEnd_3475663 1189790474698626790818815 := by
  unfold tailWord_3475663
  simp only [CollatzResearch.WordTrace]
  refine ⟨126767844007274021826919643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84511896004849347884613095 126767844007274021826919643)
  ·
    refine ⟨190151766010911032740379465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126767844007274021826919643 190151766010911032740379465)
    ·
      refine ⟨142613824508183274555284599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190151766010911032740379465 142613824508183274555284599)
      ·
        refine ⟨213920736762274911832926899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142613824508183274555284599 213920736762274911832926899)
        ·
          refine ⟨320881105143412367749390349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213920736762274911832926899 320881105143412367749390349)
          ·
            refine ⟨120330414428779637906021381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320881105143412367749390349 120330414428779637906021381)
            ·
              refine ⟨22561952705396182107379009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120330414428779637906021381 22561952705396182107379009)
              ·
                refine ⟨16921464529047136580534257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22561952705396182107379009 16921464529047136580534257)
                ·
                  refine ⟨12691098396785352435400693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16921464529047136580534257 12691098396785352435400693)
                  ·
                    refine ⟨1189790474698626790818815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12691098396785352435400693 1189790474698626790818815)
                    ·
                      rfl

theorem cell22_3475663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_3475663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475663 prefixEnd_3475663 := by exact prefixLift 3475663
  have htrace : WordTrace (prefixWord ++ tailWord_3475663) baseStart_3475663 baseEnd_3475663 := by
    simpa [prefixWord, tailWord_3475663, baseEnd_3475663] using wordTrace_append hprefix tailTrace_3475663
  have hstable : (prefixWord ++ tailWord_3475663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475663).length < 2 ^ (prefixWord ++ tailWord_3475663).sum := by decide
  have hdescent : baseEnd_3475663 < baseStart_3475663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475695 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 3, 4]
def baseStart_3475695 : Nat := 118140960795 + 3475695 * 2 ^ 59
def prefixEnd_3475695 : Nat := 4983230072969 + 3 ^ 40 * 3475695 * 2
def baseEnd_3475695 : Nat := 1189801428952589374018717

theorem tailTrace_3475695 : CollatzResearch.WordTrace tailWord_3475695 prefixEnd_3475695 1189801428952589374018717 := by
  unfold tailWord_3475695
  simp only [CollatzResearch.WordTrace]
  refine ⟨126769011143158091292084539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84512674095438727528056359 126769011143158091292084539)
  ·
    refine ⟨190153516714737136938126809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126769011143158091292084539 190153516714737136938126809)
    ·
      refine ⟨142615137536052852703595107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190153516714737136938126809 142615137536052852703595107)
      ·
        refine ⟨213922706304079279055392661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142615137536052852703595107 213922706304079279055392661)
        ·
          refine ⟨10027626858003716205721531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 213922706304079279055392661 10027626858003716205721531)
          ·
            refine ⟨15041440287005574308582297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10027626858003716205721531 15041440287005574308582297)
            ·
              refine ⟨11281080215254180731436723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15041440287005574308582297 11281080215254180731436723)
              ·
                refine ⟨16921620322881271097155085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11281080215254180731436723 16921620322881271097155085)
                ·
                  refine ⟨6345607621080476661433157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16921620322881271097155085 6345607621080476661433157)
                  ·
                    refine ⟨1189801428952589374018717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6345607621080476661433157 1189801428952589374018717)
                    ·
                      rfl

theorem cell22_3475695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_3475695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475695 prefixEnd_3475695 := by exact prefixLift 3475695
  have htrace : WordTrace (prefixWord ++ tailWord_3475695) baseStart_3475695 baseEnd_3475695 := by
    simpa [prefixWord, tailWord_3475695, baseEnd_3475695] using wordTrace_append hprefix tailTrace_3475695
  have hstable : (prefixWord ++ tailWord_3475695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475695).length < 2 ^ (prefixWord ++ tailWord_3475695).sum := by decide
  have hdescent : baseEnd_3475695 < baseStart_3475695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475710 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_3475710 : Nat := 118140960795 + 3475710 * 2 ^ 59
def prefixEnd_3475710 : Nat := 4983230072969 + 3 ^ 40 * 3475710 * 2
def baseEnd_3475710 : Nat := 396602187919711444964557

theorem tailTrace_3475710 : CollatzResearch.WordTrace tailWord_3475710 prefixEnd_3475710 396602187919711444964557 := by
  unfold tailWord_3475710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846194779762968606735073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84513038825402499235920389 15846194779762968606735073)
  ·
    refine ⟨11884646084822226455051305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15846194779762968606735073 11884646084822226455051305)
    ·
      refine ⟨8913484563616669841288479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11884646084822226455051305 8913484563616669841288479)
      ·
        refine ⟨13370226845425004761932719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8913484563616669841288479 13370226845425004761932719)
        ·
          refine ⟨20055340268137507142899079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13370226845425004761932719 20055340268137507142899079)
          ·
            refine ⟨30083010402206260714348619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20055340268137507142899079 30083010402206260714348619)
            ·
              refine ⟨45124515603309391071522929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30083010402206260714348619 45124515603309391071522929)
              ·
                refine ⟨33843386702482043303642197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45124515603309391071522929 33843386702482043303642197)
                ·
                  refine ⟨396602187919711444964557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33843386702482043303642197 396602187919711444964557)
                  ·
                    rfl

theorem cell22_3475710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_3475710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475710 prefixEnd_3475710 := by exact prefixLift 3475710
  have htrace : WordTrace (prefixWord ++ tailWord_3475710) baseStart_3475710 baseEnd_3475710 := by
    simpa [prefixWord, tailWord_3475710, baseEnd_3475710] using wordTrace_append hprefix tailTrace_3475710
  have hstable : (prefixWord ++ tailWord_3475710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475710).length < 2 ^ (prefixWord ++ tailWord_3475710).sum := by decide
  have hdescent : baseEnd_3475710 < baseStart_3475710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475712 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 1, 4]
def baseStart_3475712 : Nat := 118140960795 + 3475712 * 2 ^ 59
def prefixEnd_3475712 : Nat := 4983230072969 + 3 ^ 40 * 3475712 * 2
def baseEnd_3475712 : Nat := 1189807248400006996343665

theorem tailTrace_3475712 : CollatzResearch.WordTrace tailWord_3475712 prefixEnd_3475712 1189807248400006996343665 := by
  unfold tailWord_3475712
  simp only [CollatzResearch.WordTrace]
  refine ⟨63384815592048251597726695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84513087456064335463635593 63384815592048251597726695)
  ·
    refine ⟨95077223388072377396590043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63384815592048251597726695 95077223388072377396590043)
    ·
      refine ⟨142615835082108566094885065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95077223388072377396590043 142615835082108566094885065)
      ·
        refine ⟨106961876311581424571163799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142615835082108566094885065 106961876311581424571163799)
        ·
          refine ⟨160442814467372136856745699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106961876311581424571163799 160442814467372136856745699)
          ·
            refine ⟨240664221701058205285118549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160442814467372136856745699 240664221701058205285118549)
            ·
              refine ⟨2820283848059275843184983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 240664221701058205285118549 2820283848059275843184983)
              ·
                refine ⟨4230425772088913764777475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820283848059275843184983 4230425772088913764777475)
                ·
                  refine ⟨6345638658133370647166213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230425772088913764777475 6345638658133370647166213)
                  ·
                    refine ⟨1189807248400006996343665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6345638658133370647166213 1189807248400006996343665)
                    ·
                      rfl

theorem cell22_3475712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 1, 4].length) (baseStart_3475712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475712 prefixEnd_3475712 := by exact prefixLift 3475712
  have htrace : WordTrace (prefixWord ++ tailWord_3475712) baseStart_3475712 baseEnd_3475712 := by
    simpa [prefixWord, tailWord_3475712, baseEnd_3475712] using wordTrace_append hprefix tailTrace_3475712
  have hstable : (prefixWord ++ tailWord_3475712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475712).length < 2 ^ (prefixWord ++ tailWord_3475712).sum := by decide
  have hdescent : baseEnd_3475712 < baseStart_3475712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475761 : List Nat := [1, 2, 2, 3, 5, 1, 1, 3, 4]
def baseStart_3475761 : Nat := 118140960795 + 3475761 * 2 ^ 59
def prefixEnd_3475761 : Nat := 4983230072969 + 3 ^ 40 * 3475761 * 2
def baseEnd_3475761 : Nat := 396608007367129067289505

theorem tailTrace_3475761 : CollatzResearch.WordTrace tailWord_3475761 prefixEnd_3475761 396608007367129067289505 := by
  unfold tailWord_3475761
  simp only [CollatzResearch.WordTrace]
  refine ⟨126771418360918984563987137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84514278907279323042658091 126771418360918984563987137)
  ·
    refine ⟨95078563770689238422990353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126771418360918984563987137 95078563770689238422990353)
    ·
      refine ⟨71308922828016928817242765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95078563770689238422990353 71308922828016928817242765)
      ·
        refine ⟨26740846060506348306466037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71308922828016928817242765 26740846060506348306466037)
        ·
          refine ⟨2506954318172470153731191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26740846060506348306466037 2506954318172470153731191)
          ·
            refine ⟨3760431477258705230596787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506954318172470153731191 3760431477258705230596787)
            ·
              refine ⟨5640647215888057845895181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760431477258705230596787 5640647215888057845895181)
              ·
                refine ⟨2115242705958021692210693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5640647215888057845895181 2115242705958021692210693)
                ·
                  refine ⟨396608007367129067289505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115242705958021692210693 396608007367129067289505)
                  ·
                    rfl

theorem cell22_3475761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_3475761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475761 prefixEnd_3475761 := by exact prefixLift 3475761
  have htrace : WordTrace (prefixWord ++ tailWord_3475761) baseStart_3475761 baseEnd_3475761 := by
    simpa [prefixWord, tailWord_3475761, baseEnd_3475761] using wordTrace_append hprefix tailTrace_3475761
  have hstable : (prefixWord ++ tailWord_3475761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475761).length < 2 ^ (prefixWord ++ tailWord_3475761).sum := by decide
  have hdescent : baseEnd_3475761 < baseStart_3475761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475845 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 6]
def baseStart_3475845 : Nat := 118140960795 + 3475845 * 2 ^ 59
def prefixEnd_3475845 : Nat := 4983230072969 + 3 ^ 40 * 3475845 * 2
def baseEnd_3475845 : Nat := 396617592339346327589419

theorem tailTrace_3475845 : CollatzResearch.WordTrace tailWord_3475845 prefixEnd_3475845 396617592339346327589419 := by
  unfold tailWord_3475845
  simp only [CollatzResearch.WordTrace]
  refine ⟨126774482092614666910044989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84516321395076444606696659 126774482092614666910044989)
  ·
    refine ⟨47540430784730500091266871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126774482092614666910044989 47540430784730500091266871)
    ·
      refine ⟨71310646177095750136900307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47540430784730500091266871 71310646177095750136900307)
      ·
        refine ⟨106965969265643625205350461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71310646177095750136900307 106965969265643625205350461)
        ·
          refine ⟨40112238474616359452006423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106965969265643625205350461 40112238474616359452006423)
          ·
            refine ⟨60168357711924539178009635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40112238474616359452006423 60168357711924539178009635)
            ·
              refine ⟨90252536567886808767014453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60168357711924539178009635 90252536567886808767014453)
              ·
                refine ⟨8461175303239388321907605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90252536567886808767014453 8461175303239388321907605)
                ·
                  refine ⟨396617592339346327589419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8461175303239388321907605 396617592339346327589419)
                  ·
                    rfl

theorem cell22_3475845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_3475845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475845 prefixEnd_3475845 := by exact prefixLift 3475845
  have htrace : WordTrace (prefixWord ++ tailWord_3475845) baseStart_3475845 baseEnd_3475845 := by
    simpa [prefixWord, tailWord_3475845, baseEnd_3475845] using wordTrace_append hprefix tailTrace_3475845
  have hstable : (prefixWord ++ tailWord_3475845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475845).length < 2 ^ (prefixWord ++ tailWord_3475845).sum := by decide
  have hdescent : baseEnd_3475845 < baseStart_3475845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475877 : List Nat := [1, 3, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_3475877 : Nat := 118140960795 + 3475877 * 2 ^ 59
def prefixEnd_3475877 : Nat := 4983230072969 + 3 ^ 40 * 3475877 * 2
def baseEnd_3475877 : Nat := 1189863731272001565968159

theorem tailTrace_3475877 : CollatzResearch.WordTrace tailWord_3475877 prefixEnd_3475877 1189863731272001565968159 := by
  unfold tailWord_3475877
  simp only [CollatzResearch.WordTrace]
  refine ⟨126775649228498736375209885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84517099485665824250139923 126775649228498736375209885)
  ·
    refine ⟨47540868460687026140703707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126775649228498736375209885 47540868460687026140703707)
    ·
      refine ⟨71311302691030539211055561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47540868460687026140703707 71311302691030539211055561)
      ·
        refine ⟨53483477018272904408291671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71311302691030539211055561 53483477018272904408291671)
        ·
          refine ⟨80225215527409356612437507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53483477018272904408291671 80225215527409356612437507)
          ·
            refine ⟨120337823291114034918656261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80225215527409356612437507 120337823291114034918656261)
            ·
              refine ⟨22563341867083881547248049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120337823291114034918656261 22563341867083881547248049)
              ·
                refine ⟨16922506400312911160436037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22563341867083881547248049 16922506400312911160436037)
                ·
                  refine ⟨3172969950058670842581757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16922506400312911160436037 3172969950058670842581757)
                  ·
                    refine ⟨1189863731272001565968159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3172969950058670842581757 1189863731272001565968159)
                    ·
                      rfl

theorem cell22_3475877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_3475877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475877 prefixEnd_3475877 := by exact prefixLift 3475877
  have htrace : WordTrace (prefixWord ++ tailWord_3475877) baseStart_3475877 baseEnd_3475877 := by
    simpa [prefixWord, tailWord_3475877, baseEnd_3475877] using wordTrace_append hprefix tailTrace_3475877
  have hstable : (prefixWord ++ tailWord_3475877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475877).length < 2 ^ (prefixWord ++ tailWord_3475877).sum := by decide
  have hdescent : baseEnd_3475877 < baseStart_3475877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475879 : List Nat := [1, 1, 6, 1, 1, 2, 1, 5, 4]
def baseStart_3475879 : Nat := 118140960795 + 3475879 * 2 ^ 59
def prefixEnd_3475879 : Nat := 4983230072969 + 3 ^ 40 * 3475879 * 2
def baseEnd_3475879 : Nat := 396621471970958075806051

theorem tailTrace_3475879 : CollatzResearch.WordTrace tailWord_3475879 prefixEnd_3475879 396621471970958075806051 := by
  unfold tailWord_3475879
  simp only [CollatzResearch.WordTrace]
  refine ⟨126775722174491490716782691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84517148116327660477855127 126775722174491490716782691)
  ·
    refine ⟨190163583261737236075174037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126775722174491490716782691 190163583261737236075174037)
    ·
      refine ⟨8913917965393932941023783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190163583261737236075174037 8913917965393932941023783)
      ·
        refine ⟨13370876948090899411535675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8913917965393932941023783 13370876948090899411535675)
        ·
          refine ⟨20056315422136349117303513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13370876948090899411535675 20056315422136349117303513)
          ·
            refine ⟨15042236566602261837977635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20056315422136349117303513 15042236566602261837977635)
            ·
              refine ⟨22563354849903392756966453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15042236566602261837977635 22563354849903392756966453)
              ·
                refine ⟨2115314517178443070965605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22563354849903392756966453 2115314517178443070965605)
                ·
                  refine ⟨396621471970958075806051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115314517178443070965605 396621471970958075806051)
                  ·
                    rfl

theorem cell22_3475879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 4].length) (baseStart_3475879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475879 prefixEnd_3475879 := by exact prefixLift 3475879
  have htrace : WordTrace (prefixWord ++ tailWord_3475879) baseStart_3475879 baseEnd_3475879 := by
    simpa [prefixWord, tailWord_3475879, baseEnd_3475879] using wordTrace_append hprefix tailTrace_3475879
  have hstable : (prefixWord ++ tailWord_3475879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475879).length < 2 ^ (prefixWord ++ tailWord_3475879).sum := by decide
  have hdescent : baseEnd_3475879 < baseStart_3475879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475890 : List Nat := [3, 2, 1, 1, 1, 1, 13]
def baseStart_3475890 : Nat := 118140960795 + 3475890 * 2 ^ 59
def prefixEnd_3475890 : Nat := 4983230072969 + 3 ^ 40 * 3475890 * 2
def baseEnd_3475890 : Nat := 44069191905099032051597

theorem tailTrace_3475890 : CollatzResearch.WordTrace tailWord_3475890 prefixEnd_3475890 44069191905099032051597 := by
  unfold tailWord_3475890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31694030844362909898858281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84517415584967759730288749 31694030844362909898858281)
  ·
    refine ⟨23770523133272182424143711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31694030844362909898858281 23770523133272182424143711)
    ·
      refine ⟨35655784699908273636215567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23770523133272182424143711 35655784699908273636215567)
      ·
        refine ⟨53483677049862410454323351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35655784699908273636215567 53483677049862410454323351)
        ·
          refine ⟨80225515574793615681485027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53483677049862410454323351 80225515574793615681485027)
          ·
            refine ⟨120338273362190423522227541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80225515574793615681485027 120338273362190423522227541)
            ·
              refine ⟨44069191905099032051597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 120338273362190423522227541 44069191905099032051597)
              ·
                rfl

theorem cell22_3475890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 13].length) (baseStart_3475890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475890 prefixEnd_3475890 := by exact prefixLift 3475890
  have htrace : WordTrace (prefixWord ++ tailWord_3475890) baseStart_3475890 baseEnd_3475890 := by
    simpa [prefixWord, tailWord_3475890, baseEnd_3475890] using wordTrace_append hprefix tailTrace_3475890
  have hstable : (prefixWord ++ tailWord_3475890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475890).length < 2 ^ (prefixWord ++ tailWord_3475890).sum := by decide
  have hdescent : baseEnd_3475890 < baseStart_3475890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475911 : List Nat := [1, 1, 4, 1, 1, 5, 3, 1, 2, 3]
def baseStart_3475911 : Nat := 118140960795 + 3475911 * 2 ^ 59
def prefixEnd_3475911 : Nat := 4983230072969 + 3 ^ 40 * 3475911 * 2
def baseEnd_3475911 : Nat := 1189875370166836810618055

theorem tailTrace_3475911 : CollatzResearch.WordTrace tailWord_3475911 prefixEnd_3475911 1189875370166836810618055 := by
  unfold tailWord_3475911
  simp only [CollatzResearch.WordTrace]
  refine ⟨126776889310375560181947587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84517926206917040121298391 126776889310375560181947587)
  ·
    refine ⟨190165333965563340272921381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126776889310375560181947587 190165333965563340272921381)
    ·
      refine ⟨35656000118543126301172759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190165333965563340272921381 35656000118543126301172759)
      ·
        refine ⟨53484000177814689451759139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35656000118543126301172759 53484000177814689451759139)
        ·
          refine ⟨80226000266722034177638709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53484000177814689451759139 80226000266722034177638709)
          ·
            refine ⟨7521187525005190704153629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80226000266722034177638709 7521187525005190704153629)
            ·
              refine ⟨2820445321876946514057611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7521187525005190704153629 2820445321876946514057611)
              ·
                refine ⟨4230667982815419771086417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820445321876946514057611 4230667982815419771086417)
                ·
                  refine ⟨3173000987111564828314813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4230667982815419771086417 3173000987111564828314813)
                  ·
                    refine ⟨1189875370166836810618055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173000987111564828314813 1189875370166836810618055)
                    ·
                      rfl

theorem cell22_3475911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_3475911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475911 prefixEnd_3475911 := by exact prefixLift 3475911
  have htrace : WordTrace (prefixWord ++ tailWord_3475911) baseStart_3475911 baseEnd_3475911 := by
    simpa [prefixWord, tailWord_3475911, baseEnd_3475911] using wordTrace_append hprefix tailTrace_3475911
  have hstable : (prefixWord ++ tailWord_3475911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475911).length < 2 ^ (prefixWord ++ tailWord_3475911).sum := by decide
  have hdescent : baseEnd_3475911 < baseStart_3475911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475924 : List Nat := [2, 4, 1, 2, 2, 1, 4, 6]
def baseStart_3475924 : Nat := 118140960795 + 3475924 * 2 ^ 59
def prefixEnd_3475924 : Nat := 4983230072969 + 3 ^ 40 * 3475924 * 2
def baseEnd_3475924 : Nat := 132208868925834345560335

theorem tailTrace_3475924 : CollatzResearch.WordTrace tailWord_3475924 prefixEnd_3475924 132208868925834345560335 := by
  unfold tailWord_3475924
  simp only [CollatzResearch.WordTrace]
  refine ⟨63388681729664231701085413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84518242306218975601447217 63388681729664231701085413)
  ·
    refine ⟨11885377824312043443953515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63388681729664231701085413 11885377824312043443953515)
    ·
      refine ⟨17828066736468065165930273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11885377824312043443953515 17828066736468065165930273)
      ·
        refine ⟨13371050052351048874447705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17828066736468065165930273 13371050052351048874447705)
        ·
          refine ⟨10028287539263286655835779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13371050052351048874447705 10028287539263286655835779)
          ·
            refine ⟨15042431308894929983753669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10028287539263286655835779 15042431308894929983753669)
            ·
              refine ⟨2820455870417799371953813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15042431308894929983753669 2820455870417799371953813)
              ·
                refine ⟨132208868925834345560335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2820455870417799371953813 132208868925834345560335)
                ·
                  rfl

theorem cell22_3475924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 6].length) (baseStart_3475924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475924 prefixEnd_3475924 := by exact prefixLift 3475924
  have htrace : WordTrace (prefixWord ++ tailWord_3475924) baseStart_3475924 baseEnd_3475924 := by
    simpa [prefixWord, tailWord_3475924, baseEnd_3475924] using wordTrace_append hprefix tailTrace_3475924
  have hstable : (prefixWord ++ tailWord_3475924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475924).length < 2 ^ (prefixWord ++ tailWord_3475924).sum := by decide
  have hdescent : baseEnd_3475924 < baseStart_3475924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475952 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 5]
def baseStart_3475952 : Nat := 118140960795 + 3475952 * 2 ^ 59
def prefixEnd_3475952 : Nat := 4983230072969 + 3 ^ 40 * 3475952 * 2
def baseEnd_3475952 : Nat := 396629801768242123447643

theorem tailTrace_3475952 : CollatzResearch.WordTrace tailWord_3475952 prefixEnd_3475952 396629801768242123447643 := by
  unfold tailWord_3475952
  simp only [CollatzResearch.WordTrace]
  refine ⟨63389192351613512092095055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84518923135484682789460073 63389192351613512092095055)
  ·
    refine ⟨95083788527420268138142583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63389192351613512092095055 95083788527420268138142583)
    ·
      refine ⟨142625682791130402207213875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95083788527420268138142583 142625682791130402207213875)
      ·
        refine ⟨213938524186695603310820813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142625682791130402207213875 213938524186695603310820813)
        ·
          refine ⟨80226946570010851241557805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213938524186695603310820813 80226946570010851241557805)
          ·
            refine ⟨30085104963754069215584177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80226946570010851241557805 30085104963754069215584177)
            ·
              refine ⟨22563828722815551911688133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30085104963754069215584177 22563828722815551911688133)
              ·
                refine ⟨4230717885527915983441525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22563828722815551911688133 4230717885527915983441525)
                ·
                  refine ⟨396629801768242123447643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4230717885527915983441525 396629801768242123447643)
                  ·
                    rfl

theorem cell22_3475952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_3475952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475952 prefixEnd_3475952 := by exact prefixLift 3475952
  have htrace : WordTrace (prefixWord ++ tailWord_3475952) baseStart_3475952 baseEnd_3475952 := by
    simpa [prefixWord, tailWord_3475952, baseEnd_3475952] using wordTrace_append hprefix tailTrace_3475952
  have hstable : (prefixWord ++ tailWord_3475952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475952).length < 2 ^ (prefixWord ++ tailWord_3475952).sum := by decide
  have hdescent : baseEnd_3475952 < baseStart_3475952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3475969 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 5]
def baseStart_3475969 : Nat := 118140960795 + 3475969 * 2 ^ 59
def prefixEnd_3475969 : Nat := 4983230072969 + 3 ^ 40 * 3475969 * 2
def baseEnd_3475969 : Nat := 396631741584047997555959

theorem tailTrace_3475969 : CollatzResearch.WordTrace tailWord_3475969 prefixEnd_3475969 396631741584047997555959 := by
  unfold tailWord_3475969
  simp only [CollatzResearch.WordTrace]
  refine ⟨126779004744165436087558961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84519336496110290725039307 126779004744165436087558961)
  ·
    refine ⟨95084253558124077065669221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126779004744165436087558961 95084253558124077065669221)
    ·
      refine ⟨17828297542148264449812979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95084253558124077065669221 17828297542148264449812979)
      ·
        refine ⟨26742446313222396674719469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17828297542148264449812979 26742446313222396674719469)
        ·
          refine ⟨10028417367458398753019801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26742446313222396674719469 10028417367458398753019801)
          ·
            refine ⟨7521313025593799064764851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10028417367458398753019801 7521313025593799064764851)
            ·
              refine ⟨11281969538390698597147277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521313025593799064764851 11281969538390698597147277)
              ·
                refine ⟨4230738576896511973930229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11281969538390698597147277 4230738576896511973930229)
                ·
                  refine ⟨396631741584047997555959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4230738576896511973930229 396631741584047997555959)
                  ·
                    rfl

theorem cell22_3475969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_3475969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3475969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3475969 prefixEnd_3475969 := by exact prefixLift 3475969
  have htrace : WordTrace (prefixWord ++ tailWord_3475969) baseStart_3475969 baseEnd_3475969 := by
    simpa [prefixWord, tailWord_3475969, baseEnd_3475969] using wordTrace_append hprefix tailTrace_3475969
  have hstable : (prefixWord ++ tailWord_3475969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3475969).length < 2 ^ (prefixWord ++ tailWord_3475969).sum := by decide
  have hdescent : baseEnd_3475969 < baseStart_3475969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3475969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476029 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_3476029 : Nat := 118140960795 + 3476029 * 2 ^ 59
def prefixEnd_3476029 : Nat := 4983230072969 + 3 ^ 40 * 3476029 * 2
def baseEnd_3476029 : Nat := 1189915763978323836167693

theorem tailTrace_3476029 : CollatzResearch.WordTrace tailWord_3476029 prefixEnd_3476029 1189915763978323836167693 := by
  unfold tailWord_3476029
  simp only [CollatzResearch.WordTrace]
  refine ⟨126781193123948066334743141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84520795415965377556495427 126781193123948066334743141)
  ·
    refine ⟨23771473710740262437764339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126781193123948066334743141 23771473710740262437764339)
    ·
      refine ⟨35657210566110393656646509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23771473710740262437764339 35657210566110393656646509)
      ·
        refine ⟨13371453962291397621242441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35657210566110393656646509 13371453962291397621242441)
        ·
          refine ⟨10028590471718548215931831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13371453962291397621242441 10028590471718548215931831)
          ·
            refine ⟨15042885707577822323897747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10028590471718548215931831 15042885707577822323897747)
            ·
              refine ⟨22564328561366733485846621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15042885707577822323897747 22564328561366733485846621)
              ·
                refine ⟨8461623210512525057192483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22564328561366733485846621 8461623210512525057192483)
                ·
                  refine ⟨12692434815768787585788725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8461623210512525057192483 12692434815768787585788725)
                  ·
                    refine ⟨1189915763978323836167693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12692434815768787585788725 1189915763978323836167693)
                    ·
                      rfl

theorem cell22_3476029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_3476029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476029 prefixEnd_3476029 := by exact prefixLift 3476029
  have htrace : WordTrace (prefixWord ++ tailWord_3476029) baseStart_3476029 baseEnd_3476029 := by
    simpa [prefixWord, tailWord_3476029, baseEnd_3476029] using wordTrace_append hprefix tailTrace_3476029
  have hstable : (prefixWord ++ tailWord_3476029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476029).length < 2 ^ (prefixWord ++ tailWord_3476029).sum := by decide
  have hdescent : baseEnd_3476029 < baseStart_3476029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476093 : List Nat := [1, 4, 1, 1, 6, 1, 2, 6]
def baseStart_3476093 : Nat := 118140960795 + 3476093 * 2 ^ 59
def prefixEnd_3476093 : Nat := 4983230072969 + 3 ^ 40 * 3476093 * 2
def baseEnd_3476093 : Nat := 132215296942916555840833

theorem tailTrace_3476093 : CollatzResearch.WordTrace tailWord_3476093 prefixEnd_3476093 132215296942916555840833 := by
  unfold tailWord_3476093
  simp only [CollatzResearch.WordTrace]
  refine ⟨126783527395716205265072933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84522351597144136843381955 126783527395716205265072933)
  ·
    refine ⟨23771911386696788487201175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126783527395716205265072933 23771911386696788487201175)
    ·
      refine ⟨35657867080045182730801763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23771911386696788487201175 35657867080045182730801763)
      ·
        refine ⟨53486800620067774096202645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35657867080045182730801763 53486800620067774096202645)
        ·
          refine ⟨2507193779065676910759499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53486800620067774096202645 2507193779065676910759499)
          ·
            refine ⟨3760790668598515366139249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507193779065676910759499 3760790668598515366139249)
            ·
              refine ⟨2820593001448886524604437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3760790668598515366139249 2820593001448886524604437)
              ·
                refine ⟨132215296942916555840833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2820593001448886524604437 132215296942916555840833)
                ·
                  rfl

theorem cell22_3476093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 6].length) (baseStart_3476093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476093 prefixEnd_3476093 := by exact prefixLift 3476093
  have htrace : WordTrace (prefixWord ++ tailWord_3476093) baseStart_3476093 baseEnd_3476093 := by
    simpa [prefixWord, tailWord_3476093, baseEnd_3476093] using wordTrace_append hprefix tailTrace_3476093
  have hstable : (prefixWord ++ tailWord_3476093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476093).length < 2 ^ (prefixWord ++ tailWord_3476093).sum := by decide
  have hdescent : baseEnd_3476093 < baseStart_3476093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476151 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 3, 4]
def baseStart_3476151 : Nat := 118140960795 + 3476151 * 2 ^ 59
def prefixEnd_3476151 : Nat := 4983230072969 + 3 ^ 40 * 3476151 * 2
def baseEnd_3476151 : Nat := 1189957527071556184617319

theorem tailTrace_3476151 : CollatzResearch.WordTrace tailWord_3476151 prefixEnd_3476151 1189957527071556184617319 := by
  unfold tailWord_3476151
  simp only [CollatzResearch.WordTrace]
  refine ⟨126785642829506081170684307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84523761886337387447122871 126785642829506081170684307)
  ·
    refine ⟨190178464244259121756026461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126785642829506081170684307 190178464244259121756026461)
    ·
      refine ⟨71316924091597170658509923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190178464244259121756026461 71316924091597170658509923)
      ·
        refine ⟨106975386137395755987764885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71316924091597170658509923 106975386137395755987764885)
        ·
          refine ⟨5014471225190426061926479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106975386137395755987764885 5014471225190426061926479)
          ·
            refine ⟨7521706837785639092889719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014471225190426061926479 7521706837785639092889719)
            ·
              refine ⟨11282560256678458639334579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521706837785639092889719 11282560256678458639334579)
              ·
                refine ⟨16923840385017687959001869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282560256678458639334579 16923840385017687959001869)
                ·
                  refine ⟨6346440144381632984625701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16923840385017687959001869 6346440144381632984625701)
                  ·
                    refine ⟨1189957527071556184617319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346440144381632984625701 1189957527071556184617319)
                    ·
                      rfl

theorem cell22_3476151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_3476151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476151 prefixEnd_3476151 := by exact prefixLift 3476151
  have htrace : WordTrace (prefixWord ++ tailWord_3476151) baseStart_3476151 baseEnd_3476151 := by
    simpa [prefixWord, tailWord_3476151, baseEnd_3476151] using wordTrace_append hprefix tailTrace_3476151
  have hstable : (prefixWord ++ tailWord_3476151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476151).length < 2 ^ (prefixWord ++ tailWord_3476151).sum := by decide
  have hdescent : baseEnd_3476151 < baseStart_3476151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476168 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 1, 4]
def baseStart_3476168 : Nat := 118140960795 + 3476168 * 2 ^ 59
def prefixEnd_3476168 : Nat := 4983230072969 + 3 ^ 40 * 3476168 * 2
def baseEnd_3476168 : Nat := 1189963346518973806942267

theorem tailTrace_3476168 : CollatzResearch.WordTrace tailWord_3476168 prefixEnd_3476168 1189963346518973806942267 := by
  unfold tailWord_3476168
  simp only [CollatzResearch.WordTrace]
  refine ⟨63393131435222246537026579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84524175246962995382702105 63393131435222246537026579)
  ·
    refine ⟨95089697152833369805539869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63393131435222246537026579 95089697152833369805539869)
    ·
      refine ⟨35658636432312513677077451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95089697152833369805539869 35658636432312513677077451)
      ·
        refine ⟨53487954648468770515616177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35658636432312513677077451 53487954648468770515616177)
        ·
          refine ⟨40115965986351577886712133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53487954648468770515616177 40115965986351577886712133)
          ·
            refine ⟨7521743622440920853758525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40115965986351577886712133 7521743622440920853758525)
            ·
              refine ⟨2820653858415345320159447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7521743622440920853758525 2820653858415345320159447)
              ·
                refine ⟨4230980787623017980239171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820653858415345320159447 4230980787623017980239171)
                ·
                  refine ⟨6346471181434526970358757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4230980787623017980239171 6346471181434526970358757)
                  ·
                    refine ⟨1189963346518973806942267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346471181434526970358757 1189963346518973806942267)
                    ·
                      rfl

theorem cell22_3476168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_3476168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476168 prefixEnd_3476168 := by exact prefixLift 3476168
  have htrace : WordTrace (prefixWord ++ tailWord_3476168) baseStart_3476168 baseEnd_3476168 := by
    simpa [prefixWord, tailWord_3476168, baseEnd_3476168] using wordTrace_append hprefix tailTrace_3476168
  have hstable : (prefixWord ++ tailWord_3476168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476168).length < 2 ^ (prefixWord ++ tailWord_3476168).sum := by decide
  have hdescent : baseEnd_3476168 < baseStart_3476168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476183 : List Nat := [1, 1, 3, 2, 1, 4, 4, 2, 4]
def baseStart_3476183 : Nat := 118140960795 + 3476183 * 2 ^ 59
def prefixEnd_3476183 : Nat := 4983230072969 + 3 ^ 40 * 3476183 * 2
def baseEnd_3476183 : Nat := 396656160441839589272407

theorem tailTrace_3476183 : CollatzResearch.WordTrace tailWord_3476183 prefixEnd_3476183 396656160441839589272407 := by
  unfold tailWord_3476183
  simp only [CollatzResearch.WordTrace]
  refine ⟨126786809965390150635849203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84524539976926767090566135 126786809965390150635849203)
  ·
    refine ⟨190180214948085225953773805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126786809965390150635849203 190180214948085225953773805)
    ·
      refine ⟨71317580605531959732665177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190180214948085225953773805 71317580605531959732665177)
      ·
        refine ⟨53488185454148969799498883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71317580605531959732665177 53488185454148969799498883)
        ·
          refine ⟨80232278181223454699248325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53488185454148969799498883 80232278181223454699248325)
          ·
            refine ⟨15043552158979397756109061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80232278181223454699248325 15043552158979397756109061)
            ·
              refine ⟨2820666029808637079270449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15043552158979397756109061 2820666029808637079270449)
              ·
                refine ⟨2115499522356477809452837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820666029808637079270449 2115499522356477809452837)
                ·
                  refine ⟨396656160441839589272407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115499522356477809452837 396656160441839589272407)
                  ·
                    rfl

theorem cell22_3476183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 4].length) (baseStart_3476183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476183 prefixEnd_3476183 := by exact prefixLift 3476183
  have htrace : WordTrace (prefixWord ++ tailWord_3476183) baseStart_3476183 baseEnd_3476183 := by
    simpa [prefixWord, tailWord_3476183, baseEnd_3476183] using wordTrace_append hprefix tailTrace_3476183
  have hstable : (prefixWord ++ tailWord_3476183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476183).length < 2 ^ (prefixWord ++ tailWord_3476183).sum := by decide
  have hdescent : baseEnd_3476183 < baseStart_3476183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476239 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 7]
def baseStart_3476239 : Nat := 118140960795 + 3476239 * 2 ^ 59
def prefixEnd_3476239 : Nat := 4983230072969 + 3 ^ 40 * 3476239 * 2
def baseEnd_3476239 : Nat := 396662550423317762805683

theorem tailTrace_3476239 : CollatzResearch.WordTrace tailWord_3476239 prefixEnd_3476239 396662550423317762805683 := by
  unfold tailWord_3476239
  simp only [CollatzResearch.WordTrace]
  refine ⟨126788852453187272199887771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84525901635458181466591847 126788852453187272199887771)
  ·
    refine ⟨190183278679780908299831657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126788852453187272199887771 190183278679780908299831657)
    ·
      refine ⟨142637459009835681224873743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190183278679780908299831657 142637459009835681224873743)
      ·
        refine ⟨213956188514753521837310615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142637459009835681224873743 213956188514753521837310615)
        ·
          refine ⟨320934282772130282755965923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213956188514753521837310615 320934282772130282755965923)
          ·
            refine ⟨481401424158195424133948885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320934282772130282755965923 481401424158195424133948885)
            ·
              refine ⟨11282845878707705253139427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 481401424158195424133948885 11282845878707705253139427)
              ·
                refine ⟨16924268818061557879709141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11282845878707705253139427 16924268818061557879709141)
                ·
                  refine ⟨396662550423317762805683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16924268818061557879709141 396662550423317762805683)
                  ·
                    rfl

theorem cell22_3476239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 7].length) (baseStart_3476239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476239 prefixEnd_3476239 := by exact prefixLift 3476239
  have htrace : WordTrace (prefixWord ++ tailWord_3476239) baseStart_3476239 baseEnd_3476239 := by
    simpa [prefixWord, tailWord_3476239, baseEnd_3476239] using wordTrace_append hprefix tailTrace_3476239
  have hstable : (prefixWord ++ tailWord_3476239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476239).length < 2 ^ (prefixWord ++ tailWord_3476239).sum := by decide
  have hdescent : baseEnd_3476239 < baseStart_3476239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476243 : List Nat := [1, 1, 1, 2, 1, 3, 3, 6, 1, 3]
def baseStart_3476243 : Nat := 118140960795 + 3476243 * 2 ^ 59
def prefixEnd_3476243 : Nat := 4983230072969 + 3 ^ 40 * 3476243 * 2
def baseEnd_3476243 : Nat := 1189989020551698611317037

theorem tailTrace_3476243 : CollatzResearch.WordTrace tailWord_3476243 prefixEnd_3476243 1189989020551698611317037 := by
  unfold tailWord_3476243
  simp only [CollatzResearch.WordTrace]
  refine ⟨126788998345172780883033383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84525998896781853922022255 126788998345172780883033383)
  ·
    refine ⟨190183497517759171324550075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126788998345172780883033383 190183497517759171324550075)
    ·
      refine ⟨285275246276638756986825113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190183497517759171324550075 285275246276638756986825113)
      ·
        refine ⟨213956434707479067740118835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285275246276638756986825113 213956434707479067740118835)
        ·
          refine ⟨320934652061218601610178253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213956434707479067740118835 320934652061218601610178253)
          ·
            refine ⟨120350494522956975603816845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320934652061218601610178253 120350494522956975603816845)
            ·
              refine ⟨45131435446108865851431317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120350494522956975603816845 45131435446108865851431317)
              ·
                refine ⟨2115536036536353086785843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45131435446108865851431317 2115536036536353086785843)
                ·
                  refine ⟨3173304054804529630178765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115536036536353086785843 3173304054804529630178765)
                  ·
                    refine ⟨1189989020551698611317037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173304054804529630178765 1189989020551698611317037)
                    ·
                      rfl

theorem cell22_3476243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 1, 3].length) (baseStart_3476243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476243 prefixEnd_3476243 := by exact prefixLift 3476243
  have htrace : WordTrace (prefixWord ++ tailWord_3476243) baseStart_3476243 baseEnd_3476243 := by
    simpa [prefixWord, tailWord_3476243, baseEnd_3476243] using wordTrace_append hprefix tailTrace_3476243
  have hstable : (prefixWord ++ tailWord_3476243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476243).length < 2 ^ (prefixWord ++ tailWord_3476243).sum := by decide
  have hdescent : baseEnd_3476243 < baseStart_3476243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476277 : List Nat := [1, 3, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3476277 : Nat := 118140960795 + 3476277 * 2 ^ 59
def prefixEnd_3476277 : Nat := 4983230072969 + 3 ^ 40 * 3476277 * 2
def baseEnd_3476277 : Nat := 1190000659446533855966933

theorem tailTrace_3476277 : CollatzResearch.WordTrace tailWord_3476277 prefixEnd_3476277 1190000659446533855966933 := by
  unfold tailWord_3476277
  simp only [CollatzResearch.WordTrace]
  refine ⟨126790238427049604689771085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84526825618033069793180723 126790238427049604689771085)
  ·
    refine ⟨47546339410143601758664157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126790238427049604689771085 47546339410143601758664157)
    ·
      refine ⟨17829877278803850659499059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47546339410143601758664157 17829877278803850659499059)
      ·
        refine ⟨26744815918205775989248589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17829877278803850659499059 26744815918205775989248589)
        ·
          refine ⟨10029305969327165995968221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26744815918205775989248589 10029305969327165995968221)
          ·
            refine ⟨3760989738497687248488083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10029305969327165995968221 3760989738497687248488083)
            ·
              refine ⟨5641484607746530872732125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760989738497687248488083 5641484607746530872732125)
              ·
                refine ⟨2115556727904949077274547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5641484607746530872732125 2115556727904949077274547)
                ·
                  refine ⟨3173335091857423615911821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115556727904949077274547 3173335091857423615911821)
                  ·
                    refine ⟨1190000659446533855966933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173335091857423615911821 1190000659446533855966933)
                    ·
                      rfl

theorem cell22_3476277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3476277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476277 prefixEnd_3476277 := by exact prefixLift 3476277
  have htrace : WordTrace (prefixWord ++ tailWord_3476277) baseStart_3476277 baseEnd_3476277 := by
    simpa [prefixWord, tailWord_3476277, baseEnd_3476277] using wordTrace_append hprefix tailTrace_3476277
  have hstable : (prefixWord ++ tailWord_3476277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476277).length < 2 ^ (prefixWord ++ tailWord_3476277).sum := by decide
  have hdescent : baseEnd_3476277 < baseStart_3476277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476294 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3476294 : Nat := 118140960795 + 3476294 * 2 ^ 59
def prefixEnd_3476294 : Nat := 4983230072969 + 3 ^ 40 * 3476294 * 2
def baseEnd_3476294 : Nat := 1190006478893951478291881

theorem tailTrace_3476294 : CollatzResearch.WordTrace tailWord_3476294 prefixEnd_3476294 1190006478893951478291881 := by
  unfold tailWord_3476294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962214327124625518535623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 84527238978658677728759957 3962214327124625518535623)
  ·
    refine ⟨5943321490686938277803435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3962214327124625518535623 5943321490686938277803435)
    ·
      refine ⟨8914982236030407416705153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943321490686938277803435 8914982236030407416705153)
      ·
        refine ⟨6686236677022805562528865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8914982236030407416705153 6686236677022805562528865)
        ·
          refine ⟨5014677507767104171896649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6686236677022805562528865 5014677507767104171896649)
          ·
            refine ⟨3761008130825328128922487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014677507767104171896649 3761008130825328128922487)
            ·
              refine ⟨5641512196237992193383731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761008130825328128922487 5641512196237992193383731)
              ·
                refine ⟨8462268294356988290075597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641512196237992193383731 8462268294356988290075597)
                ·
                  refine ⟨3173350610383870608778349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8462268294356988290075597 3173350610383870608778349)
                  ·
                    refine ⟨1190006478893951478291881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173350610383870608778349 1190006478893951478291881)
                    ·
                      rfl

theorem cell22_3476294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3476294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476294 prefixEnd_3476294 := by exact prefixLift 3476294
  have htrace : WordTrace (prefixWord ++ tailWord_3476294) baseStart_3476294 baseEnd_3476294 := by
    simpa [prefixWord, tailWord_3476294, baseEnd_3476294] using wordTrace_append hprefix tailTrace_3476294
  have hstable : (prefixWord ++ tailWord_3476294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476294).length < 2 ^ (prefixWord ++ tailWord_3476294).sum := by decide
  have hdescent : baseEnd_3476294 < baseStart_3476294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476331 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 2, 4]
def baseStart_3476331 : Nat := 118140960795 + 3476331 * 2 ^ 59
def prefixEnd_3476331 : Nat := 4983230072969 + 3 ^ 40 * 3476331 * 2
def baseEnd_3476331 : Nat := 1190019144750095715116767

theorem tailTrace_3476331 : CollatzResearch.WordTrace tailWord_3476331 prefixEnd_3476331 1190019144750095715116767 := by
  unfold tailWord_3476331
  simp only [CollatzResearch.WordTrace]
  refine ⟨126792207968853971912236847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84528138645902647941491231 126792207968853971912236847)
  ·
    refine ⟨190188311953280957868355271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126792207968853971912236847 190188311953280957868355271)
    ·
      refine ⟨285282467929921436802532907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190188311953280957868355271 285282467929921436802532907)
      ·
        refine ⟨427923701894882155203799361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285282467929921436802532907 427923701894882155203799361)
        ·
          refine ⟨320942776421161616402849521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427923701894882155203799361 320942776421161616402849521)
          ·
            refine ⟨240707082315871212302137141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320942776421161616402849521 240707082315871212302137141)
            ·
              refine ⟨22566288967112926153325357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240707082315871212302137141 22566288967112926153325357)
              ·
                refine ⟨8462358362667347307497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22566288967112926153325357 8462358362667347307497009)
                ·
                  refine ⟨6346768772000510480622757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8462358362667347307497009 6346768772000510480622757)
                  ·
                    refine ⟨1190019144750095715116767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346768772000510480622757 1190019144750095715116767)
                    ·
                      rfl

theorem cell22_3476331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_3476331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476331 prefixEnd_3476331 := by exact prefixLift 3476331
  have htrace : WordTrace (prefixWord ++ tailWord_3476331) baseStart_3476331 baseEnd_3476331 := by
    simpa [prefixWord, tailWord_3476331, baseEnd_3476331] using wordTrace_append hprefix tailTrace_3476331
  have hstable : (prefixWord ++ tailWord_3476331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476331).length < 2 ^ (prefixWord ++ tailWord_3476331).sum := by decide
  have hdescent : baseEnd_3476331 < baseStart_3476331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476380 : List Nat := [2, 2, 3, 3, 2, 1, 3, 6]
def baseStart_3476380 : Nat := 118140960795 + 3476380 * 2 ^ 59
def prefixEnd_3476380 : Nat := 4983230072969 + 3 ^ 40 * 3476380 * 2
def baseEnd_3476380 : Nat := 132226213161275102293513

theorem tailTrace_3476380 : CollatzResearch.WordTrace tailWord_3476380 prefixEnd_3476380 132226213161275102293513 := by
  unfold tailWord_3476380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63396997572838226640385297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84529330097117635520513729 63396997572838226640385297)
  ·
    refine ⟨47547748179628669980288973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63396997572838226640385297 47547748179628669980288973)
    ·
      refine ⟨17830405567360751242608365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47547748179628669980288973 17830405567360751242608365)
      ·
        refine ⟨6686402087760281715978137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17830405567360751242608365 6686402087760281715978137)
        ·
          refine ⟨5014801565820211286983603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6686402087760281715978137 5014801565820211286983603)
          ·
            refine ⟨7522202348730316930475405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014801565820211286983603 7522202348730316930475405)
            ·
              refine ⟨2820825880773868848928277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7522202348730316930475405 2820825880773868848928277)
              ·
                refine ⟨132226213161275102293513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2820825880773868848928277 132226213161275102293513)
                ·
                  rfl

theorem cell22_3476380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 6].length) (baseStart_3476380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476380 prefixEnd_3476380 := by exact prefixLift 3476380
  have htrace : WordTrace (prefixWord ++ tailWord_3476380) baseStart_3476380 baseEnd_3476380 := by
    simpa [prefixWord, tailWord_3476380, baseEnd_3476380] using wordTrace_append hprefix tailTrace_3476380
  have hstable : (prefixWord ++ tailWord_3476380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476380).length < 2 ^ (prefixWord ++ tailWord_3476380).sum := by decide
  have hdescent : baseEnd_3476380 < baseStart_3476380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476408 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 5]
def baseStart_3476408 : Nat := 118140960795 + 3476408 * 2 ^ 59
def prefixEnd_3476408 : Nat := 4983230072969 + 3 ^ 40 * 3476408 * 2
def baseEnd_3476408 : Nat := 396681834474564393647177

theorem tailTrace_3476408 : CollatzResearch.WordTrace tailWord_3476408 prefixEnd_3476408 396681834474564393647177 := by
  unfold tailWord_3476408
  simp only [CollatzResearch.WordTrace]
  refine ⟨63397508194787507031394939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84530010926383342708526585 63397508194787507031394939)
  ·
    refine ⟨95096262292181260547092409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63397508194787507031394939 95096262292181260547092409)
    ·
      refine ⟨71322196719135945410319307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95096262292181260547092409 71322196719135945410319307)
      ·
        refine ⟨106983295078703918115478961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71322196719135945410319307 106983295078703918115478961)
        ·
          refine ⟨80237471309027938586609221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106983295078703918115478961 80237471309027938586609221)
          ·
            refine ⟨15044525870442738484989229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80237471309027938586609221 15044525870442738484989229)
            ·
              refine ⟨5641697201416026931870961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15044525870442738484989229 5641697201416026931870961)
              ·
                refine ⟨4231272901062020198903221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5641697201416026931870961 4231272901062020198903221)
                ·
                  refine ⟨396681834474564393647177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4231272901062020198903221 396681834474564393647177)
                  ·
                    rfl

theorem cell22_3476408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_3476408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476408 prefixEnd_3476408 := by exact prefixLift 3476408
  have htrace : WordTrace (prefixWord ++ tailWord_3476408) baseStart_3476408 baseEnd_3476408 := by
    simpa [prefixWord, tailWord_3476408, baseEnd_3476408] using wordTrace_append hprefix tailTrace_3476408
  have hstable : (prefixWord ++ tailWord_3476408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476408).length < 2 ^ (prefixWord ++ tailWord_3476408).sum := by decide
  have hdescent : baseEnd_3476408 < baseStart_3476408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476455 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3476455 : Nat := 118140960795 + 3476455 * 2 ^ 59
def prefixEnd_3476455 : Nat := 4983230072969 + 3 ^ 40 * 3476455 * 2
def baseEnd_3476455 : Nat := 1190061592484200725016387

theorem tailTrace_3476455 : CollatzResearch.WordTrace tailWord_3476455 prefixEnd_3476455 1190061592484200725016387 := by
  unfold tailWord_3476455
  simp only [CollatzResearch.WordTrace]
  refine ⟨126796730620404741089750819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84531153746936494059833879 126796730620404741089750819)
  ·
    refine ⟨190195095930607111634626229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126796730620404741089750819 190195095930607111634626229)
    ·
      refine ⟨17830790243494416715746209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190195095930607111634626229 17830790243494416715746209)
      ·
        refine ⟨13373092682620812536809657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17830790243494416715746209 13373092682620812536809657)
        ·
          refine ⟨10029819511965609402607243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13373092682620812536809657 10029819511965609402607243)
          ·
            refine ⟨15044729267948414103910865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10029819511965609402607243 15044729267948414103910865)
            ·
              refine ⟨11283546950961310577933149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15044729267948414103910865 11283546950961310577933149)
              ·
                refine ⟨4231330106610491466724931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11283546950961310577933149 4231330106610491466724931)
                ·
                  refine ⟨6346995159915737200087397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4231330106610491466724931 6346995159915737200087397)
                  ·
                    refine ⟨1190061592484200725016387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6346995159915737200087397 1190061592484200725016387)
                    ·
                      rfl

theorem cell22_3476455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3476455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476455 prefixEnd_3476455 := by exact prefixLift 3476455
  have htrace : WordTrace (prefixWord ++ tailWord_3476455) baseStart_3476455 baseEnd_3476455 := by
    simpa [prefixWord, tailWord_3476455, baseEnd_3476455] using wordTrace_append hprefix tailTrace_3476455
  have hstable : (prefixWord ++ tailWord_3476455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476455).length < 2 ^ (prefixWord ++ tailWord_3476455).sum := by decide
  have hdescent : baseEnd_3476455 < baseStart_3476455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476470 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3476470 : Nat := 118140960795 + 3476470 * 2 ^ 59
def prefixEnd_3476470 : Nat := 4983230072969 + 3 ^ 40 * 3476470 * 2
def baseEnd_3476470 : Nat := 396688909096915228630447

theorem tailTrace_3476470 : CollatzResearch.WordTrace tailWord_3476470 prefixEnd_3476470 396688909096915228630447 := by
  unfold tailWord_3476470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924829857209399915721679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84531518476900265767697909 7924829857209399915721679)
  ·
    refine ⟨11887244785814099873582519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7924829857209399915721679 11887244785814099873582519)
    ·
      refine ⟨17830867178721149810373779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11887244785814099873582519 17830867178721149810373779)
      ·
        refine ⟨26746300768081724715560669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17830867178721149810373779 26746300768081724715560669)
        ·
          refine ⟨10029862788030646768335251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26746300768081724715560669 10029862788030646768335251)
          ·
            refine ⟨15044794182045970152502877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10029862788030646768335251 15044794182045970152502877)
            ·
              refine ⟨5641797818267238807188579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15044794182045970152502877 5641797818267238807188579)
              ·
                refine ⟨8462696727400858210782869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641797818267238807188579 8462696727400858210782869)
                ·
                  refine ⟨396688909096915228630447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8462696727400858210782869 396688909096915228630447)
                  ·
                    rfl

theorem cell22_3476470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3476470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476470 prefixEnd_3476470 := by exact prefixLift 3476470
  have htrace : WordTrace (prefixWord ++ tailWord_3476470) baseStart_3476470 baseEnd_3476470 := by
    simpa [prefixWord, tailWord_3476470, baseEnd_3476470] using wordTrace_append hprefix tailTrace_3476470
  have hstable : (prefixWord ++ tailWord_3476470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476470).length < 2 ^ (prefixWord ++ tailWord_3476470).sum := by decide
  have hdescent : baseEnd_3476470 < baseStart_3476470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476485 : List Nat := [1, 3, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_3476485 : Nat := 118140960795 + 3476485 * 2 ^ 59
def prefixEnd_3476485 : Nat := 4983230072969 + 3 ^ 40 * 3476485 * 2
def baseEnd_3476485 : Nat := 1190071862097290646766295

theorem tailTrace_3476485 : CollatzResearch.WordTrace tailWord_3476485 prefixEnd_3476485 1190071862097290646766295 := by
  unfold tailWord_3476485
  simp only [CollatzResearch.WordTrace]
  refine ⟨126797824810296056213342909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84531883206864037475561939 126797824810296056213342909)
  ·
    refine ⟨47549184303861021080003591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126797824810296056213342909 47549184303861021080003591)
    ·
      refine ⟨71323776455791531620005387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47549184303861021080003591 71323776455791531620005387)
      ·
        refine ⟨106985664683687297430008081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71323776455791531620005387 106985664683687297430008081)
        ·
          refine ⟨80239248512765473072506061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106985664683687297430008081 80239248512765473072506061)
          ·
            refine ⟨30089718192287052402189773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80239248512765473072506061 30089718192287052402189773)
            ·
              refine ⟨11283644322107644650821165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30089718192287052402189773 11283644322107644650821165)
              ·
                refine ⟨4231366620790366744057937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11283644322107644650821165 4231366620790366744057937)
                ·
                  refine ⟨3173524965592775058043453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231366620790366744057937 3173524965592775058043453)
                  ·
                    refine ⟨1190071862097290646766295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173524965592775058043453 1190071862097290646766295)
                    ·
                      rfl

theorem cell22_3476485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_3476485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476485 prefixEnd_3476485 := by exact prefixLift 3476485
  have htrace : WordTrace (prefixWord ++ tailWord_3476485) baseStart_3476485 baseEnd_3476485 := by
    simpa [prefixWord, tailWord_3476485, baseEnd_3476485] using wordTrace_append hprefix tailTrace_3476485
  have hstable : (prefixWord ++ tailWord_3476485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476485).length < 2 ^ (prefixWord ++ tailWord_3476485).sum := by decide
  have hdescent : baseEnd_3476485 < baseStart_3476485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476519 : List Nat := [1, 1, 7, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3476519 : Nat := 118140960795 + 3476519 * 2 ^ 59
def prefixEnd_3476519 : Nat := 4983230072969 + 3 ^ 40 * 3476519 * 2
def baseEnd_3476519 : Nat := 1190083500992125891416191

theorem tailTrace_3476519 : CollatzResearch.WordTrace tailWord_3476519 prefixEnd_3476519 1190083500992125891416191 := by
  unfold tailWord_3476519
  simp only [CollatzResearch.WordTrace]
  refine ⟨126799064892172880020080611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84532709928115253346720407 126799064892172880020080611)
  ·
    refine ⟨190198597338259320030120917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126799064892172880020080611 190198597338259320030120917)
    ·
      refine ⟨4457779625115452813205959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 190198597338259320030120917 4457779625115452813205959)
      ·
        refine ⟨6686669437673179219808939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457779625115452813205959 6686669437673179219808939)
        ·
          refine ⟨10030004156509768829713409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6686669437673179219808939 10030004156509768829713409)
          ·
            refine ⟨7522503117382326622285057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10030004156509768829713409 7522503117382326622285057)
            ·
              refine ⟨5641877338036744966713793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7522503117382326622285057 5641877338036744966713793)
              ·
                refine ⟨4231408003527558725035345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5641877338036744966713793 4231408003527558725035345)
                ·
                  refine ⟨3173556002645669043776509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231408003527558725035345 3173556002645669043776509)
                  ·
                    refine ⟨1190083500992125891416191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173556002645669043776509 1190083500992125891416191)
                    ·
                      rfl

theorem cell22_3476519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3476519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476519 prefixEnd_3476519 := by exact prefixLift 3476519
  have htrace : WordTrace (prefixWord ++ tailWord_3476519) baseStart_3476519 baseEnd_3476519 := by
    simpa [prefixWord, tailWord_3476519, baseEnd_3476519] using wordTrace_append hprefix tailTrace_3476519
  have hstable : (prefixWord ++ tailWord_3476519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476519).length < 2 ^ (prefixWord ++ tailWord_3476519).sum := by decide
  have hdescent : baseEnd_3476519 < baseStart_3476519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476530 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_3476530 : Nat := 118140960795 + 3476530 * 2 ^ 59
def prefixEnd_3476530 : Nat := 4983230072969 + 3 ^ 40 * 3476530 * 2
def baseEnd_3476530 : Nat := 1190087266516925529391157

theorem tailTrace_3476530 : CollatzResearch.WordTrace tailWord_3476530 prefixEnd_3476530 1190087266516925529391157 := by
  unfold tailWord_3476530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31699866523783257224682761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84532977396755352599154029 31699866523783257224682761)
  ·
    refine ⟨23774899892837442918512071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31699866523783257224682761 23774899892837442918512071)
    ·
      refine ⟨35662349839256164377768107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23774899892837442918512071 35662349839256164377768107)
      ·
        refine ⟨53493524758884246566652161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35662349839256164377768107 53493524758884246566652161)
        ·
          refine ⟨40120143569163184924989121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53493524758884246566652161 40120143569163184924989121)
          ·
            refine ⟨30090107676872388693741841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40120143569163184924989121 30090107676872388693741841)
            ·
              refine ⟨22567580757654291520306381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30090107676872388693741841 22567580757654291520306381)
              ·
                refine ⟨8462842784120359320114893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22567580757654291520306381 8462842784120359320114893)
                ·
                  refine ⟨3173566044045134745043085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8462842784120359320114893 3173566044045134745043085)
                  ·
                    refine ⟨1190087266516925529391157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173566044045134745043085 1190087266516925529391157)
                    ·
                      rfl

theorem cell22_3476530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_3476530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476530 prefixEnd_3476530 := by exact prefixLift 3476530
  have htrace : WordTrace (prefixWord ++ tailWord_3476530) baseStart_3476530 baseEnd_3476530 := by
    simpa [prefixWord, tailWord_3476530, baseEnd_3476530] using wordTrace_append hprefix tailTrace_3476530
  have hstable : (prefixWord ++ tailWord_3476530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476530).length < 2 ^ (prefixWord ++ tailWord_3476530).sum := by decide
  have hdescent : baseEnd_3476530 < baseStart_3476530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476532 : List Nat := [2, 5, 1, 2, 1, 3, 1, 7]
def baseStart_3476532 : Nat := 118140960795 + 3476532 * 2 ^ 59
def prefixEnd_3476532 : Nat := 4983230072969 + 3 ^ 40 * 3476532 * 2
def baseEnd_3476532 : Nat := 132231994573088687871239

theorem tailTrace_3476532 : CollatzResearch.WordTrace tailWord_3476532 prefixEnd_3476532 132231994573088687871239 := by
  unfold tailWord_3476532
  simp only [CollatzResearch.WordTrace]
  refine ⟨63399769520562891620151925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84533026027417188826869233 63399769520562891620151925)
  ·
    refine ⟨5943728392552771089389243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63399769520562891620151925 5943728392552771089389243)
    ·
      refine ⟨8915592588829156634083865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943728392552771089389243 8915592588829156634083865)
      ·
        refine ⟨6686694441621867475562899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8915592588829156634083865 6686694441621867475562899)
        ·
          refine ⟨10030041662432801213344349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6686694441621867475562899 10030041662432801213344349)
          ·
            refine ⟨3761265623412300455004131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10030041662432801213344349 3761265623412300455004131)
            ·
              refine ⟨5641898435118450682506197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761265623412300455004131 5641898435118450682506197)
              ·
                refine ⟨132231994573088687871239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5641898435118450682506197 132231994573088687871239)
                ·
                  rfl

theorem cell22_3476532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 7].length) (baseStart_3476532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476532 prefixEnd_3476532 := by exact prefixLift 3476532
  have htrace : WordTrace (prefixWord ++ tailWord_3476532) baseStart_3476532 baseEnd_3476532 := by
    simpa [prefixWord, tailWord_3476532, baseEnd_3476532] using wordTrace_append hprefix tailTrace_3476532
  have hstable : (prefixWord ++ tailWord_3476532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476532).length < 2 ^ (prefixWord ++ tailWord_3476532).sum := by decide
  have hdescent : baseEnd_3476532 < baseStart_3476532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476558 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_3476558 : Nat := 118140960795 + 3476558 * 2 ^ 59
def prefixEnd_3476558 : Nat := 4983230072969 + 3 ^ 40 * 3476558 * 2
def baseEnd_3476558 : Nat := 1190096851489142789691071

theorem tailTrace_3476558 : CollatzResearch.WordTrace tailWord_3476558 prefixEnd_3476558 1190096851489142789691071 := by
  unfold tailWord_3476558
  simp only [CollatzResearch.WordTrace]
  refine ⟨15850060917378948710093791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 84533658226021059787166885 15850060917378948710093791)
  ·
    refine ⟨23775091376068423065140687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15850060917378948710093791 23775091376068423065140687)
    ·
      refine ⟨35662637064102634597711031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23775091376068423065140687 35662637064102634597711031)
      ·
        refine ⟨53493955596153951896566547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35662637064102634597711031 53493955596153951896566547)
        ·
          refine ⟨80240933394230927844849821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53493955596153951896566547 80240933394230927844849821)
          ·
            refine ⟨30090350022836597941818683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80240933394230927844849821 30090350022836597941818683)
            ·
              refine ⟨45135525034254896912728025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30090350022836597941818683 45135525034254896912728025)
              ·
                refine ⟨33851643775691172684546019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45135525034254896912728025 33851643775691172684546019)
                ·
                  refine ⟨50777465663536759026819029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33851643775691172684546019 50777465663536759026819029)
                  ·
                    refine ⟨1190096851489142789691071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50777465663536759026819029 1190096851489142789691071)
                    ·
                      rfl

theorem cell22_3476558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_3476558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476558 prefixEnd_3476558 := by exact prefixLift 3476558
  have htrace : WordTrace (prefixWord ++ tailWord_3476558) baseStart_3476558 baseEnd_3476558 := by
    simpa [prefixWord, tailWord_3476558, baseEnd_3476558] using wordTrace_append hprefix tailTrace_3476558
  have hstable : (prefixWord ++ tailWord_3476558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476558).length < 2 ^ (prefixWord ++ tailWord_3476558).sum := by decide
  have hdescent : baseEnd_3476558 < baseStart_3476558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476637 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3476637 : Nat := 118140960795 + 3476637 * 2 ^ 59
def prefixEnd_3476637 : Nat := 4983230072969 + 3 ^ 40 * 3476637 * 2
def baseEnd_3476637 : Nat := 1190123894803612916965829

theorem tailTrace_3476637 : CollatzResearch.WordTrace tailWord_3476637 prefixEnd_3476637 1190123894803612916965829 := by
  unfold tailWord_3476637
  simp only [CollatzResearch.WordTrace]
  refine ⟨126803368705745386172876165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84535579137163590781917443 126803368705745386172876165)
  ·
    refine ⟨23775631632327259907414281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126803368705745386172876165 23775631632327259907414281)
    ·
      refine ⟨17831723724245444930560711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23775631632327259907414281 17831723724245444930560711)
      ·
        refine ⟨26747585586368167395841067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17831723724245444930560711 26747585586368167395841067)
        ·
          refine ⟨40121378379552251093761601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26747585586368167395841067 40121378379552251093761601)
          ·
            refine ⟨30091033784664188320321201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40121378379552251093761601 30091033784664188320321201)
            ·
              refine ⟨22568275338498141240240901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30091033784664188320321201 22568275338498141240240901)
              ·
                refine ⟨4231551625968401482545169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22568275338498141240240901 4231551625968401482545169)
                ·
                  refine ⟨3173663719476301111908877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4231551625968401482545169 3173663719476301111908877)
                  ·
                    refine ⟨1190123894803612916965829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173663719476301111908877 1190123894803612916965829)
                    ·
                      rfl

theorem cell22_3476637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3476637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476637 prefixEnd_3476637 := by exact prefixLift 3476637
  have htrace : WordTrace (prefixWord ++ tailWord_3476637) baseStart_3476637 baseEnd_3476637 := by
    simpa [prefixWord, tailWord_3476637, baseEnd_3476637] using wordTrace_append hprefix tailTrace_3476637
  have hstable : (prefixWord ++ tailWord_3476637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476637).length < 2 ^ (prefixWord ++ tailWord_3476637).sum := by decide
  have hdescent : baseEnd_3476637 < baseStart_3476637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476639 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 6]
def baseStart_3476639 : Nat := 118140960795 + 3476639 * 2 ^ 59
def prefixEnd_3476639 : Nat := 4983230072969 + 3 ^ 40 * 3476639 * 2
def baseEnd_3476639 : Nat := 396708193148161859471941

theorem tailTrace_3476639 : CollatzResearch.WordTrace tailWord_3476639 prefixEnd_3476639 396708193148161859471941 := by
  unfold tailWord_3476639
  simp only [CollatzResearch.WordTrace]
  refine ⟨126803441651738140514448971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84535627767825427009632647 126803441651738140514448971)
  ·
    refine ⟨190205162477607210771673457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126803441651738140514448971 190205162477607210771673457)
    ·
      refine ⟨142653871858205408078755093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190205162477607210771673457 142653871858205408078755093)
      ·
        refine ⟨6686900243353378503691645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 142653871858205408078755093 6686900243353378503691645)
        ·
          refine ⟨2507587591257516938884367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6686900243353378503691645 2507587591257516938884367)
          ·
            refine ⟨3761381386886275408326551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507587591257516938884367 3761381386886275408326551)
            ·
              refine ⟨5642072080329413112489827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761381386886275408326551 5642072080329413112489827)
              ·
                refine ⟨8463108120494119668734741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642072080329413112489827 8463108120494119668734741)
                ·
                  refine ⟨396708193148161859471941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8463108120494119668734741 396708193148161859471941)
                  ·
                    rfl

theorem cell22_3476639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 6].length) (baseStart_3476639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476639 prefixEnd_3476639 := by exact prefixLift 3476639
  have htrace : WordTrace (prefixWord ++ tailWord_3476639) baseStart_3476639 baseEnd_3476639 := by
    simpa [prefixWord, tailWord_3476639, baseEnd_3476639] using wordTrace_append hprefix tailTrace_3476639
  have hstable : (prefixWord ++ tailWord_3476639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476639).length < 2 ^ (prefixWord ++ tailWord_3476639).sum := by decide
  have hdescent : baseEnd_3476639 < baseStart_3476639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476695 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 5]
def baseStart_3476695 : Nat := 118140960795 + 3476695 * 2 ^ 59
def prefixEnd_3476695 : Nat := 4983230072969 + 3 ^ 40 * 3476695 * 2
def baseEnd_3476695 : Nat := 396714583129640033005217

theorem tailTrace_3476695 : CollatzResearch.WordTrace tailWord_3476695 prefixEnd_3476695 396714583129640033005217 := by
  unfold tailWord_3476695
  simp only [CollatzResearch.WordTrace]
  refine ⟨126805484139535262078487539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84536989426356841385658359 126805484139535262078487539)
  ·
    refine ⟨190208226209302893117731309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126805484139535262078487539 190208226209302893117731309)
    ·
      refine ⟨71328084828488584919149241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190208226209302893117731309 71328084828488584919149241)
      ·
        refine ⟨53496063621366438689361931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71328084828488584919149241 53496063621366438689361931)
        ·
          refine ⟨80244095432049658034042897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53496063621366438689361931 80244095432049658034042897)
          ·
            refine ⟨60183071574037243525532173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80244095432049658034042897 60183071574037243525532173)
            ·
              refine ⟨22568651840263966322074565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60183071574037243525532173 22568651840263966322074565)
              ·
                refine ⟨4231622220049493685388981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22568651840263966322074565 4231622220049493685388981)
                ·
                  refine ⟨396714583129640033005217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4231622220049493685388981 396714583129640033005217)
                  ·
                    rfl

theorem cell22_3476695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 5].length) (baseStart_3476695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476695 prefixEnd_3476695 := by exact prefixLift 3476695
  have htrace : WordTrace (prefixWord ++ tailWord_3476695) baseStart_3476695 baseEnd_3476695 := by
    simpa [prefixWord, tailWord_3476695, baseEnd_3476695] using wordTrace_append hprefix tailTrace_3476695
  have hstable : (prefixWord ++ tailWord_3476695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476695).length < 2 ^ (prefixWord ++ tailWord_3476695).sum := by decide
  have hdescent : baseEnd_3476695 < baseStart_3476695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476804 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3476804 : Nat := 118140960795 + 3476804 * 2 ^ 59
def prefixEnd_3476804 : Nat := 4983230072969 + 3 ^ 40 * 3476804 * 2
def baseEnd_3476804 : Nat := 1190181062316480148040317

theorem tailTrace_3476804 : CollatzResearch.WordTrace tailWord_3476804 prefixEnd_3476804 1190181062316480148040317 := by
  unfold tailWord_3476804
  simp only [CollatzResearch.WordTrace]
  refine ⟨63404729848070186847102733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84539639797426915796136977 63404729848070186847102733)
  ·
    refine ⟨23776773693026320067663525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63404729848070186847102733 23776773693026320067663525)
    ·
      refine ⟨4458145067442435012686911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23776773693026320067663525 4458145067442435012686911)
      ·
        refine ⟨6687217601163652519030367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458145067442435012686911 6687217601163652519030367)
        ·
          refine ⟨10030826401745478778545551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6687217601163652519030367 10030826401745478778545551)
          ·
            refine ⟨15046239602618218167818327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10030826401745478778545551 15046239602618218167818327)
            ·
              refine ⟨22569359403927327251727491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15046239602618218167818327 22569359403927327251727491)
              ·
                refine ⟨33854039105890990877591237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22569359403927327251727491 33854039105890990877591237)
                ·
                  refine ⟨6347632332354560789548357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33854039105890990877591237 6347632332354560789548357)
                  ·
                    refine ⟨1190181062316480148040317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6347632332354560789548357 1190181062316480148040317)
                    ·
                      rfl

theorem cell22_3476804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3476804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476804 prefixEnd_3476804 := by exact prefixLift 3476804
  have htrace : WordTrace (prefixWord ++ tailWord_3476804) baseStart_3476804 baseEnd_3476804 := by
    simpa [prefixWord, tailWord_3476804, baseEnd_3476804] using wordTrace_append hprefix tailTrace_3476804
  have hstable : (prefixWord ++ tailWord_3476804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476804).length < 2 ^ (prefixWord ++ tailWord_3476804).sum := by decide
  have hdescent : baseEnd_3476804 < baseStart_3476804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476834 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_3476834 : Nat := 118140960795 + 3476834 * 2 ^ 59
def prefixEnd_3476834 : Nat := 4983230072969 + 3 ^ 40 * 3476834 * 2
def baseEnd_3476834 : Nat := 1190191331929570069790225

theorem tailTrace_3476834 : CollatzResearch.WordTrace tailWord_3476834 prefixEnd_3476834 1190191331929570069790225 := by
  unfold tailWord_3476834
  simp only [CollatzResearch.WordTrace]
  refine ⟨31702638471507922204449389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84540369257354459211865037 31702638471507922204449389)
  ·
    refine ⟨11888489426815470826668521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31702638471507922204449389 11888489426815470826668521)
    ·
      refine ⟨8916367070111603120001391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11888489426815470826668521 8916367070111603120001391)
      ·
        refine ⟨13374550605167404680002087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8916367070111603120001391 13374550605167404680002087)
        ·
          refine ⟨20061825907751107020003131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13374550605167404680002087 20061825907751107020003131)
          ·
            refine ⟨30092738861626660530004697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20061825907751107020003131 30092738861626660530004697)
            ·
              refine ⟨22569554146219995397503523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30092738861626660530004697 22569554146219995397503523)
              ·
                refine ⟨33854331219329993096255285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22569554146219995397503523 33854331219329993096255285)
                ·
                  refine ⟨3173843551812186852773933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33854331219329993096255285 3173843551812186852773933)
                  ·
                    refine ⟨1190191331929570069790225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173843551812186852773933 1190191331929570069790225)
                    ·
                      rfl

theorem cell22_3476834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_3476834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476834 prefixEnd_3476834 := by exact prefixLift 3476834
  have htrace : WordTrace (prefixWord ++ tailWord_3476834) baseStart_3476834 baseEnd_3476834 := by
    simpa [prefixWord, tailWord_3476834, baseEnd_3476834] using wordTrace_append hprefix tailTrace_3476834
  have hstable : (prefixWord ++ tailWord_3476834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476834).length < 2 ^ (prefixWord ++ tailWord_3476834).sum := by decide
  have hdescent : baseEnd_3476834 < baseStart_3476834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476868 : List Nat := [2, 3, 2, 1, 1, 3, 4, 2, 1, 3]
def baseStart_3476868 : Nat := 118140960795 + 3476868 * 2 ^ 59
def prefixEnd_3476868 : Nat := 4983230072969 + 3 ^ 40 * 3476868 * 2
def baseEnd_3476868 : Nat := 1190202970824405314440121

theorem tailTrace_3476868 : CollatzResearch.WordTrace tailWord_3476868 prefixEnd_3476868 1190202970824405314440121 := by
  unfold tailWord_3476868
  simp only [CollatzResearch.WordTrace]
  refine ⟨63405896983954256312267629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84541195978605675083023505 63405896983954256312267629)
  ·
    refine ⟨23777211368982846117100361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63405896983954256312267629 23777211368982846117100361)
    ·
      refine ⟨17832908526737134587825271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23777211368982846117100361 17832908526737134587825271)
      ·
        refine ⟨26749362790105701881737907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17832908526737134587825271 26749362790105701881737907)
        ·
          refine ⟨40124044185158552822606861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26749362790105701881737907 40124044185158552822606861)
          ·
            refine ⟨15046516569434457308477573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40124044185158552822606861 15046516569434457308477573)
            ·
              refine ⟨2821221856768960745339545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15046516569434457308477573 2821221856768960745339545)
              ·
                refine ⟨2115916392576720559004659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821221856768960745339545 2115916392576720559004659)
                ·
                  refine ⟨3173874588865080838506989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2115916392576720559004659 3173874588865080838506989)
                  ·
                    refine ⟨1190202970824405314440121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3173874588865080838506989 1190202970824405314440121)
                    ·
                      rfl

theorem cell22_3476868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_3476868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476868 prefixEnd_3476868 := by exact prefixLift 3476868
  have htrace : WordTrace (prefixWord ++ tailWord_3476868) baseStart_3476868 baseEnd_3476868 := by
    simpa [prefixWord, tailWord_3476868, baseEnd_3476868] using wordTrace_append hprefix tailTrace_3476868
  have hstable : (prefixWord ++ tailWord_3476868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476868).length < 2 ^ (prefixWord ++ tailWord_3476868).sum := by decide
  have hdescent : baseEnd_3476868 < baseStart_3476868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476954 : List Nat := [3, 1, 1, 2, 3, 2, 4, 6]
def baseStart_3476954 : Nat := 118140960795 + 3476954 * 2 ^ 59
def prefixEnd_3476954 : Nat := 4983230072969 + 3 ^ 40 * 3476954 * 2
def baseEnd_3476954 : Nat := 132248045597992195198873

theorem tailTrace_3476954 : CollatzResearch.WordTrace tailWord_3476954 prefixEnd_3476954 132248045597992195198873 := by
  unfold tailWord_3476954
  simp only [CollatzResearch.WordTrace]
  refine ⟨31703732661399237328041479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84543287097064632874777277 31703732661399237328041479)
  ·
    refine ⟨47555598992098855992062219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31703732661399237328041479 47555598992098855992062219)
    ·
      refine ⟨71333398488148283988093329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47555598992098855992062219 71333398488148283988093329)
      ·
        refine ⟨53500048866111212991069997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71333398488148283988093329 53500048866111212991069997)
        ·
          refine ⟨20062518324791704871651249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53500048866111212991069997 20062518324791704871651249)
          ·
            refine ⟨15046888743593778653738437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20062518324791704871651249 15046888743593778653738437)
            ·
              refine ⟨2821291639423833497575957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15046888743593778653738437 2821291639423833497575957)
              ·
                refine ⟨132248045597992195198873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2821291639423833497575957 132248045597992195198873)
                ·
                  rfl

theorem cell22_3476954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_3476954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476954 prefixEnd_3476954 := by exact prefixLift 3476954
  have htrace : WordTrace (prefixWord ++ tailWord_3476954) baseStart_3476954 baseEnd_3476954 := by
    simpa [prefixWord, tailWord_3476954, baseEnd_3476954] using wordTrace_append hprefix tailTrace_3476954
  have hstable : (prefixWord ++ tailWord_3476954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476954).length < 2 ^ (prefixWord ++ tailWord_3476954).sum := by decide
  have hdescent : baseEnd_3476954 < baseStart_3476954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3476997 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3476997 : Nat := 118140960795 + 3476997 * 2 ^ 59
def prefixEnd_3476997 : Nat := 4983230072969 + 3 ^ 40 * 3476997 * 2
def baseEnd_3476997 : Nat := 1190247130160691977964725

theorem tailTrace_3476997 : CollatzResearch.WordTrace tailWord_3476997 prefixEnd_3476997 1190247130160691977964725 := by
  unfold tailWord_3476997
  simp only [CollatzResearch.WordTrace]
  refine ⟨126816498984441167655981245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84544332656294111770654163 126816498984441167655981245)
  ·
    refine ⟨47556187119165437870992967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126816498984441167655981245 47556187119165437870992967)
    ·
      refine ⟨71334280678748156806489451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47556187119165437870992967 71334280678748156806489451)
      ·
        refine ⟨107001421018122235209734177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71334280678748156806489451 107001421018122235209734177)
        ·
          refine ⟨80251065763591676407300633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107001421018122235209734177 80251065763591676407300633)
          ·
            refine ⟨60188299322693757305475475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80251065763591676407300633 60188299322693757305475475)
            ·
              refine ⟨90282448984040635958213213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60188299322693757305475475 90282448984040635958213213)
              ·
                refine ⟨33855918369015238484329955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90282448984040635958213213 33855918369015238484329955)
                ·
                  refine ⟨50783877553522857726494933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33855918369015238484329955 50783877553522857726494933)
                  ·
                    refine ⟨1190247130160691977964725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50783877553522857726494933 1190247130160691977964725)
                    ·
                      rfl

theorem cell22_3476997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3476997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3476997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3476997 prefixEnd_3476997 := by exact prefixLift 3476997
  have htrace : WordTrace (prefixWord ++ tailWord_3476997) baseStart_3476997 baseEnd_3476997 := by
    simpa [prefixWord, tailWord_3476997, baseEnd_3476997] using wordTrace_append hprefix tailTrace_3476997
  have hstable : (prefixWord ++ tailWord_3476997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3476997).length < 2 ^ (prefixWord ++ tailWord_3476997).sum := by decide
  have hdescent : baseEnd_3476997 < baseStart_3476997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3476997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477059 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 8, 3]
def baseStart_3477059 : Nat := 118140960795 + 3477059 * 2 ^ 59
def prefixEnd_3477059 : Nat := 4983230072969 + 3 ^ 40 * 3477059 * 2
def baseEnd_3477059 : Nat := 1190268354027744482914535

theorem tailTrace_3477059 : CollatzResearch.WordTrace tailWord_3477059 prefixEnd_3477059 1190268354027744482914535 := by
  unfold tailWord_3477059
  simp only [CollatzResearch.WordTrace]
  refine ⟨126818760310216552244738231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84545840206811034829825487 126818760310216552244738231)
  ·
    refine ⟨190228140465324828367107347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126818760310216552244738231 190228140465324828367107347)
    ·
      refine ⟨285342210697987242550661021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190228140465324828367107347 285342210697987242550661021)
      ·
        refine ⟨107003329011745215956497883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285342210697987242550661021 107003329011745215956497883)
        ·
          refine ⟨160504993517617823934746825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107003329011745215956497883 160504993517617823934746825)
          ·
            refine ⟨120378745138213367951060119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160504993517617823934746825 120378745138213367951060119)
            ·
              refine ⟨180568117707320051926590179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120378745138213367951060119 180568117707320051926590179)
              ·
                refine ⟨270852176560980077889885269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180568117707320051926590179 270852176560980077889885269)
                ·
                  refine ⟨3174048944073985287772093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 270852176560980077889885269 3174048944073985287772093)
                  ·
                    refine ⟨1190268354027744482914535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174048944073985287772093 1190268354027744482914535)
                    ·
                      rfl

theorem cell22_3477059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 3].length) (baseStart_3477059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477059 prefixEnd_3477059 := by exact prefixLift 3477059
  have htrace : WordTrace (prefixWord ++ tailWord_3477059) baseStart_3477059 baseEnd_3477059 := by
    simpa [prefixWord, tailWord_3477059, baseEnd_3477059] using wordTrace_append hprefix tailTrace_3477059
  have hstable : (prefixWord ++ tailWord_3477059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477059).length < 2 ^ (prefixWord ++ tailWord_3477059).sum := by decide
  have hdescent : baseEnd_3477059 < baseStart_3477059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477076 : List Nat := [2, 4, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_3477076 : Nat := 118140960795 + 3477076 * 2 ^ 59
def prefixEnd_3477076 : Nat := 4983230072969 + 3 ^ 40 * 3477076 * 2
def baseEnd_3477076 : Nat := 1190274173475162105239483

theorem tailTrace_3477076 : CollatzResearch.WordTrace tailWord_3477076 prefixEnd_3477076 1190274173475162105239483 := by
  unfold tailWord_3477076
  simp only [CollatzResearch.WordTrace]
  refine ⟨63409690175577482074053541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84546253567436642765404721 63409690175577482074053541)
  ·
    refine ⟨11889316907920777888885039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63409690175577482074053541 11889316907920777888885039)
    ·
      refine ⟨17833975361881166833327559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11889316907920777888885039 17833975361881166833327559)
      ·
        refine ⟨26750963042821750249991339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17833975361881166833327559 26750963042821750249991339)
        ·
          refine ⟨40126444564232625374987009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26750963042821750249991339 40126444564232625374987009)
          ·
            refine ⟨30094833423174469031240257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40126444564232625374987009 30094833423174469031240257)
            ·
              refine ⟨22571125067380851773430193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30094833423174469031240257 22571125067380851773430193)
              ·
                refine ⟨16928343800535638830072645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22571125067380851773430193 16928343800535638830072645)
                ·
                  refine ⟨3174064462600432280638621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16928343800535638830072645 3174064462600432280638621)
                  ·
                    refine ⟨1190274173475162105239483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174064462600432280638621 1190274173475162105239483)
                    ·
                      rfl

theorem cell22_3477076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_3477076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477076 prefixEnd_3477076 := by exact prefixLift 3477076
  have htrace : WordTrace (prefixWord ++ tailWord_3477076) baseStart_3477076 baseEnd_3477076 := by
    simpa [prefixWord, tailWord_3477076, baseEnd_3477076] using wordTrace_append hprefix tailTrace_3477076
  have hstable : (prefixWord ++ tailWord_3477076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477076).length < 2 ^ (prefixWord ++ tailWord_3477076).sum := by decide
  have hdescent : baseEnd_3477076 < baseStart_3477076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477093 : List Nat := [1, 3, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_3477093 : Nat := 118140960795 + 3477093 * 2 ^ 59
def prefixEnd_3477093 : Nat := 4983230072969 + 3 ^ 40 * 3477093 * 2
def baseEnd_3477093 : Nat := 1190279992922579727564431

theorem tailTrace_3477093 : CollatzResearch.WordTrace tailWord_3477093 prefixEnd_3477093 1190279992922579727564431 := by
  unfold tailWord_3477093
  simp only [CollatzResearch.WordTrace]
  refine ⟨126820000392093376051475933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84546666928062250700983955 126820000392093376051475933)
  ·
    refine ⟨47557500147035016019303475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126820000392093376051475933 47557500147035016019303475)
    ·
      refine ⟨71336250220552524028955213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47557500147035016019303475 71336250220552524028955213)
      ·
        refine ⟨26751093832707196510858205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71336250220552524028955213 26751093832707196510858205)
        ·
          refine ⟨10031660187265198691571827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26751093832707196510858205 10031660187265198691571827)
          ·
            refine ⟨15047490280897798037357741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10031660187265198691571827 15047490280897798037357741)
            ·
              refine ⟨5642808855336674264009153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15047490280897798037357741 5642808855336674264009153)
              ·
                refine ⟨4232106641502505698006865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5642808855336674264009153 4232106641502505698006865)
                ·
                  refine ⟨3174079981126879273505149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232106641502505698006865 3174079981126879273505149)
                  ·
                    refine ⟨1190279992922579727564431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174079981126879273505149 1190279992922579727564431)
                    ·
                      rfl

theorem cell22_3477093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_3477093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477093 prefixEnd_3477093 := by exact prefixLift 3477093
  have htrace : WordTrace (prefixWord ++ tailWord_3477093) baseStart_3477093 baseEnd_3477093 := by
    simpa [prefixWord, tailWord_3477093, baseEnd_3477093] using wordTrace_append hprefix tailTrace_3477093
  have hstable : (prefixWord ++ tailWord_3477093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477093).length < 2 ^ (prefixWord ++ tailWord_3477093).sum := by decide
  have hdescent : baseEnd_3477093 < baseStart_3477093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477155 : List Nat := [1, 1, 1, 4, 1, 1, 7, 2, 1, 3]
def baseStart_3477155 : Nat := 118140960795 + 3477155 * 2 ^ 59
def prefixEnd_3477155 : Nat := 4983230072969 + 3 ^ 40 * 3477155 * 2
def baseEnd_3477155 : Nat := 1190301216789632232514241

theorem tailTrace_3477155 : CollatzResearch.WordTrace tailWord_3477155 prefixEnd_3477155 1190301216789632232514241 := by
  unfold tailWord_3477155
  simp only [CollatzResearch.WordTrace]
  refine ⟨126822261717868760640232919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84548174478579173760155279 126822261717868760640232919)
  ·
    refine ⟨190233392576803140960349379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126822261717868760640232919 190233392576803140960349379)
    ·
      refine ⟨285350088865204711440524069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190233392576803140960349379 285350088865204711440524069)
      ·
        refine ⟨53503141662225883395098263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285350088865204711440524069 53503141662225883395098263)
        ·
          refine ⟨80254712493338825092647395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53503141662225883395098263 80254712493338825092647395)
          ·
            refine ⟨120382068740008237638971093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80254712493338825092647395 120382068740008237638971093)
            ·
              refine ⟨2821454736093943069663385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 120382068740008237638971093 2821454736093943069663385)
              ·
                refine ⟨2116091052070457302247539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821454736093943069663385 2116091052070457302247539)
                ·
                  refine ⟨3174136578105685953371309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116091052070457302247539 3174136578105685953371309)
                  ·
                    refine ⟨1190301216789632232514241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174136578105685953371309 1190301216789632232514241)
                    ·
                      rfl

theorem cell22_3477155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2, 1, 3].length) (baseStart_3477155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477155 prefixEnd_3477155 := by exact prefixLift 3477155
  have htrace : WordTrace (prefixWord ++ tailWord_3477155) baseStart_3477155 baseEnd_3477155 := by
    simpa [prefixWord, tailWord_3477155, baseEnd_3477155] using wordTrace_append hprefix tailTrace_3477155
  have hstable : (prefixWord ++ tailWord_3477155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477155).length < 2 ^ (prefixWord ++ tailWord_3477155).sum := by decide
  have hdescent : baseEnd_3477155 < baseStart_3477155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477179 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 6]
def baseStart_3477179 : Nat := 118140960795 + 3477179 * 2 ^ 59
def prefixEnd_3477179 : Nat := 4983230072969 + 3 ^ 40 * 3477179 * 2
def baseEnd_3477179 : Nat := 396769810826701389971389

theorem tailTrace_3477179 : CollatzResearch.WordTrace tailWord_3477179 prefixEnd_3477179 396769810826701389971389 := by
  unfold tailWord_3477179
  simp only [CollatzResearch.WordTrace]
  refine ⟨126823137069781812739106591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84548758046521208492737727 126823137069781812739106591)
  ·
    refine ⟨190234705604672719108659887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126823137069781812739106591 190234705604672719108659887)
    ·
      refine ⟨285352058407009078662989831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190234705604672719108659887 285352058407009078662989831)
      ·
        refine ⟨428028087610513617994484747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285352058407009078662989831 428028087610513617994484747)
        ·
          refine ⟨642042131415770426991727121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428028087610513617994484747 642042131415770426991727121)
          ·
            refine ⟨481531598561827820243795341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642042131415770426991727121 481531598561827820243795341)
            ·
              refine ⟨180574349460685432591423253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481531598561827820243795341 180574349460685432591423253)
              ·
                refine ⟨8464422630969629652722965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180574349460685432591423253 8464422630969629652722965)
                ·
                  refine ⟨396769810826701389971389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8464422630969629652722965 396769810826701389971389)
                  ·
                    rfl

theorem cell22_3477179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 6].length) (baseStart_3477179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477179 prefixEnd_3477179 := by exact prefixLift 3477179
  have htrace : WordTrace (prefixWord ++ tailWord_3477179) baseStart_3477179 baseEnd_3477179 := by
    simpa [prefixWord, tailWord_3477179, baseEnd_3477179] using wordTrace_append hprefix tailTrace_3477179
  have hstable : (prefixWord ++ tailWord_3477179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477179).length < 2 ^ (prefixWord ++ tailWord_3477179).sum := by decide
  have hdescent : baseEnd_3477179 < baseStart_3477179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477181 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_3477181 : Nat := 118140960795 + 3477181 * 2 ^ 59
def prefixEnd_3477181 : Nat := 4983230072969 + 3 ^ 40 * 3477181 * 2
def baseEnd_3477181 : Nat := 1190310117120976831364161

theorem tailTrace_3477181 : CollatzResearch.WordTrace tailWord_3477181 prefixEnd_3477181 1190310117120976831364161 := by
  unfold tailWord_3477181
  simp only [CollatzResearch.WordTrace]
  refine ⟨126823210015774567080679397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84548806677183044720452931 126823210015774567080679397)
  ·
    refine ⟨23779351877957731327627387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126823210015774567080679397 23779351877957731327627387)
    ·
      refine ⟨35669027816936596991441081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23779351877957731327627387 35669027816936596991441081)
      ·
        refine ⟨26751770862702447743580811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35669027816936596991441081 26751770862702447743580811)
        ·
          refine ⟨40127656294053671615371217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26751770862702447743580811 40127656294053671615371217)
          ·
            refine ⟨30095742220540253711528413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40127656294053671615371217 30095742220540253711528413)
            ·
              refine ⟨11285903332702595141823155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30095742220540253711528413 11285903332702595141823155)
              ·
                refine ⟨16928854999053892712734733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11285903332702595141823155 16928854999053892712734733)
                ·
                  refine ⟨6348320624645209767275525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16928854999053892712734733 6348320624645209767275525)
                  ·
                    refine ⟨1190310117120976831364161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348320624645209767275525 1190310117120976831364161)
                    ·
                      rfl

theorem cell22_3477181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_3477181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477181 prefixEnd_3477181 := by exact prefixLift 3477181
  have htrace : WordTrace (prefixWord ++ tailWord_3477181) baseStart_3477181 baseEnd_3477181 := by
    simpa [prefixWord, tailWord_3477181, baseEnd_3477181] using wordTrace_append hprefix tailTrace_3477181
  have hstable : (prefixWord ++ tailWord_3477181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477181).length < 2 ^ (prefixWord ++ tailWord_3477181).sum := by decide
  have hdescent : baseEnd_3477181 < baseStart_3477181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477226 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3477226 : Nat := 118140960795 + 3477226 * 2 ^ 59
def prefixEnd_3477226 : Nat := 4983230072969 + 3 ^ 40 * 3477226 * 2
def baseEnd_3477226 : Nat := 1190325521540611713989023

theorem tailTrace_3477226 : CollatzResearch.WordTrace tailWord_3477226 prefixEnd_3477226 1190325521540611713989023 := by
  unfold tailWord_3477226
  simp only [CollatzResearch.WordTrace]
  refine ⟨31706212825152884941516883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84549900867074359844045021 31706212825152884941516883)
  ·
    refine ⟨47559319237729327412275325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31706212825152884941516883 47559319237729327412275325)
    ·
      refine ⟨17834744714148497779603247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47559319237729327412275325 17834744714148497779603247)
      ·
        refine ⟨26752117071222746669404871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17834744714148497779603247 26752117071222746669404871)
        ·
          refine ⟨40128175606834120004107307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26752117071222746669404871 40128175606834120004107307)
          ·
            refine ⟨60192263410251180006160961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40128175606834120004107307 60192263410251180006160961)
            ·
              refine ⟨45144197557688385004620721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60192263410251180006160961 45144197557688385004620721)
              ·
                refine ⟨33858148168266288753465541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45144197557688385004620721 33858148168266288753465541)
                ·
                  refine ⟨6348402781549929141274789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33858148168266288753465541 6348402781549929141274789)
                  ·
                    refine ⟨1190325521540611713989023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348402781549929141274789 1190325521540611713989023)
                    ·
                      rfl

theorem cell22_3477226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3477226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477226 prefixEnd_3477226 := by exact prefixLift 3477226
  have htrace : WordTrace (prefixWord ++ tailWord_3477226) baseStart_3477226 baseEnd_3477226 := by
    simpa [prefixWord, tailWord_3477226, baseEnd_3477226] using wordTrace_append hprefix tailTrace_3477226
  have hstable : (prefixWord ++ tailWord_3477226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477226).length < 2 ^ (prefixWord ++ tailWord_3477226).sum := by decide
  have hdescent : baseEnd_3477226 < baseStart_3477226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477228 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_3477228 : Nat := 118140960795 + 3477228 * 2 ^ 59
def prefixEnd_3477228 : Nat := 4983230072969 + 3 ^ 40 * 3477228 * 2
def baseEnd_3477228 : Nat := 1190326206181484375439017

theorem tailTrace_3477228 : CollatzResearch.WordTrace tailWord_3477228 prefixEnd_3477228 1190326206181484375439017 := by
  unfold tailWord_3477228
  simp only [CollatzResearch.WordTrace]
  refine ⟨63412462123302147053820169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84549949497736196071760225 63412462123302147053820169)
  ·
    refine ⟨47559346592476610290365127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63412462123302147053820169 47559346592476610290365127)
    ·
      refine ⟨71339019888714915435547691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47559346592476610290365127 71339019888714915435547691)
      ·
        refine ⟨107008529833072373153321537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71339019888714915435547691 107008529833072373153321537)
        ·
          refine ⟨80256397374804279864991153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107008529833072373153321537 80256397374804279864991153)
          ·
            refine ⟨60192298031103209898743365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80256397374804279864991153 60192298031103209898743365)
            ·
              refine ⟨11286055880831851856014381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60192298031103209898743365 11286055880831851856014381)
              ·
                refine ⟨4232270955311944446005393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11286055880831851856014381 4232270955311944446005393)
                ·
                  refine ⟨3174203216483958334504045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232270955311944446005393 3174203216483958334504045)
                  ·
                    refine ⟨1190326206181484375439017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174203216483958334504045 1190326206181484375439017)
                    ·
                      rfl

theorem cell22_3477228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_3477228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477228 prefixEnd_3477228 := by exact prefixLift 3477228
  have htrace : WordTrace (prefixWord ++ tailWord_3477228) baseStart_3477228 baseEnd_3477228 := by
    simpa [prefixWord, tailWord_3477228, baseEnd_3477228] using wordTrace_append hprefix tailTrace_3477228
  have hstable : (prefixWord ++ tailWord_3477228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477228).length < 2 ^ (prefixWord ++ tailWord_3477228).sum := by decide
  have hdescent : baseEnd_3477228 < baseStart_3477228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477324 : List Nat := [2, 2, 1, 3, 4, 1, 3, 2, 1, 3]
def baseStart_3477324 : Nat := 118140960795 + 3477324 * 2 ^ 59
def prefixEnd_3477324 : Nat := 4983230072969 + 3 ^ 40 * 3477324 * 2
def baseEnd_3477324 : Nat := 1190359068943372125038723

theorem tailTrace_3477324 : CollatzResearch.WordTrace tailWord_3477324 prefixEnd_3477324 1190359068943372125038723 := by
  unfold tailWord_3477324
  simp only [CollatzResearch.WordTrace]
  refine ⟨63414212827128251251567513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84552283769504335002090017 63414212827128251251567513)
  ·
    refine ⟨47560659620346188438675635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63414212827128251251567513 47560659620346188438675635)
    ·
      refine ⟨71340989430519282658013453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47560659620346188438675635 71340989430519282658013453)
      ·
        refine ⟨26752871036444730996755045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71340989430519282658013453 26752871036444730996755045)
        ·
          refine ⟨5016163319333387061891571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26752871036444730996755045 5016163319333387061891571)
          ·
            refine ⟨7524244979000080592837357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5016163319333387061891571 7524244979000080592837357)
            ·
              refine ⟨2821591867125030222314009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7524244979000080592837357 2821591867125030222314009)
              ·
                refine ⟨2116193900343772666735507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821591867125030222314009 2116193900343772666735507)
                ·
                  refine ⟨3174290850515659000103261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116193900343772666735507 3174290850515659000103261)
                  ·
                    refine ⟨1190359068943372125038723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174290850515659000103261 1190359068943372125038723)
                    ·
                      rfl

theorem cell22_3477324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 2, 1, 3].length) (baseStart_3477324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477324 prefixEnd_3477324 := by exact prefixLift 3477324
  have htrace : WordTrace (prefixWord ++ tailWord_3477324) baseStart_3477324 baseEnd_3477324 := by
    simpa [prefixWord, tailWord_3477324, baseEnd_3477324] using wordTrace_append hprefix tailTrace_3477324
  have hstable : (prefixWord ++ tailWord_3477324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477324).length < 2 ^ (prefixWord ++ tailWord_3477324).sum := by decide
  have hdescent : baseEnd_3477324 < baseStart_3477324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477365 : List Nat := [1, 3, 4, 1, 1, 1, 2, 5, 4]
def baseStart_3477365 : Nat := 118140960795 + 3477365 * 2 ^ 59
def prefixEnd_3477365 : Nat := 4983230072969 + 3 ^ 40 * 3477365 * 2
def baseEnd_3477365 : Nat := 396791034693753894921199

theorem tailTrace_3477365 : CollatzResearch.WordTrace tailWord_3477365 prefixEnd_3477365 396791034693753894921199 := by
  unfold tailWord_3477365
  simp only [CollatzResearch.WordTrace]
  refine ⟨126829921047107966505377549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84553280698071977670251699 126829921047107966505377549)
  ·
    refine ⟨47561220392665487439516581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126829921047107966505377549 47561220392665487439516581)
    ·
      refine ⟨8917728823624778894909359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47561220392665487439516581 8917728823624778894909359)
      ·
        refine ⟨13376593235437168342364039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8917728823624778894909359 13376593235437168342364039)
        ·
          refine ⟨20064889853155752513546059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13376593235437168342364039 20064889853155752513546059)
          ·
            refine ⟨30097334779733628770319089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20064889853155752513546059 30097334779733628770319089)
            ·
              refine ⟨22573001084800221577739317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30097334779733628770319089 22573001084800221577739317)
              ·
                refine ⟨2116218851700020772913061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22573001084800221577739317 2116218851700020772913061)
                ·
                  refine ⟨396791034693753894921199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116218851700020772913061 396791034693753894921199)
                  ·
                    rfl

theorem cell22_3477365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_3477365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477365 prefixEnd_3477365 := by exact prefixLift 3477365
  have htrace : WordTrace (prefixWord ++ tailWord_3477365) baseStart_3477365 baseEnd_3477365 := by
    simpa [prefixWord, tailWord_3477365, baseEnd_3477365] using wordTrace_append hprefix tailTrace_3477365
  have hstable : (prefixWord ++ tailWord_3477365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477365).length < 2 ^ (prefixWord ++ tailWord_3477365).sum := by decide
  have hdescent : baseEnd_3477365 < baseStart_3477365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477380 : List Nat := [2, 3, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_3477380 : Nat := 118140960795 + 3477380 * 2 ^ 59
def prefixEnd_3477380 : Nat := 4983230072969 + 3 ^ 40 * 3477380 * 2
def baseEnd_3477380 : Nat := 1190378238887806645638551

theorem tailTrace_3477380 : CollatzResearch.WordTrace tailWord_3477380 prefixEnd_3477380 1190378238887806645638551 := by
  unfold tailWord_3477380
  simp only [CollatzResearch.WordTrace]
  refine ⟨63415234071026812033586797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84553645428035749378115729 63415234071026812033586797)
  ·
    refine ⟨23780712776635054512595049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63415234071026812033586797 23780712776635054512595049)
    ·
      refine ⟨17835534582476290884446287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23780712776635054512595049 17835534582476290884446287)
      ·
        refine ⟨26753301873714436326669431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17835534582476290884446287 26753301873714436326669431)
        ·
          refine ⟨40129952810571654490004147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26753301873714436326669431 40129952810571654490004147)
          ·
            refine ⟨60194929215857481735006221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40129952810571654490004147 60194929215857481735006221)
            ·
              refine ⟨22573098455946555650627333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60194929215857481735006221 22573098455946555650627333)
              ·
                refine ⟨4232455960489979184492625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22573098455946555650627333 4232455960489979184492625)
                ·
                  refine ⟨3174341970367484388369469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232455960489979184492625 3174341970367484388369469)
                  ·
                    refine ⟨1190378238887806645638551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174341970367484388369469 1190378238887806645638551)
                    ·
                      rfl

theorem cell22_3477380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_3477380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477380 prefixEnd_3477380 := by exact prefixLift 3477380
  have htrace : WordTrace (prefixWord ++ tailWord_3477380) baseStart_3477380 baseEnd_3477380 := by
    simpa [prefixWord, tailWord_3477380, baseEnd_3477380] using wordTrace_append hprefix tailTrace_3477380
  have hstable : (prefixWord ++ tailWord_3477380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477380).length < 2 ^ (prefixWord ++ tailWord_3477380).sum := by decide
  have hdescent : baseEnd_3477380 < baseStart_3477380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477455 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 5]
def baseStart_3477455 : Nat := 118140960795 + 3477455 * 2 ^ 59
def prefixEnd_3477455 : Nat := 4983230072969 + 3 ^ 40 * 3477455 * 2
def baseEnd_3477455 : Nat := 396801304306843816671107

theorem tailTrace_3477455 : CollatzResearch.WordTrace tailWord_3477455 prefixEnd_3477455 396801304306843816671107 := by
  unfold tailWord_3477455
  simp only [CollatzResearch.WordTrace]
  refine ⟨126833203616781911876153819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84555469077854607917435879 126833203616781911876153819)
  ·
    refine ⟨190249805425172867814230729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126833203616781911876153819 190249805425172867814230729)
    ·
      refine ⟨142687354068879650860673047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190249805425172867814230729 142687354068879650860673047)
      ·
        refine ⟨214031031103319476291009571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142687354068879650860673047 214031031103319476291009571)
        ·
          refine ⟨321046546654979214436514357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214031031103319476291009571 321046546654979214436514357)
          ·
            refine ⟨30098113748904301353423221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 321046546654979214436514357 30098113748904301353423221)
            ·
              refine ⟨2821698163959778251883427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30098113748904301353423221 2821698163959778251883427)
              ·
                refine ⟨4232547245939667377825141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821698163959778251883427 4232547245939667377825141)
                ·
                  refine ⟨396801304306843816671107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4232547245939667377825141 396801304306843816671107)
                  ·
                    rfl

theorem cell22_3477455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 5].length) (baseStart_3477455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477455 prefixEnd_3477455 := by exact prefixLift 3477455
  have htrace : WordTrace (prefixWord ++ tailWord_3477455) baseStart_3477455 baseEnd_3477455 := by
    simpa [prefixWord, tailWord_3477455, baseEnd_3477455] using wordTrace_append hprefix tailTrace_3477455
  have hstable : (prefixWord ++ tailWord_3477455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477455).length < 2 ^ (prefixWord ++ tailWord_3477455).sum := by decide
  have hdescent : baseEnd_3477455 < baseStart_3477455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477528 : List Nat := [2, 1, 2, 3, 2, 1, 1, 10]
def baseStart_3477528 : Nat := 118140960795 + 3477528 * 2 ^ 59
def prefixEnd_3477528 : Nat := 4983230072969 + 3 ^ 40 * 3477528 * 2
def baseEnd_3477528 : Nat := 132269878034709288104233

theorem tailTrace_3477528 : CollatzResearch.WordTrace tailWord_3477528 prefixEnd_3477528 132269878034709288104233 := by
  unfold tailWord_3477528
  simp only [CollatzResearch.WordTrace]
  refine ⟨63417933072758722671780619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84557244097011630229040825 63417933072758722671780619)
  ·
    refine ⟨95126899609138084007670929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63417933072758722671780619 95126899609138084007670929)
    ·
      refine ⟨71345174706853563005753197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95126899609138084007670929 71345174706853563005753197)
      ·
        refine ⟨26754440515070086127157449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71345174706853563005753197 26754440515070086127157449)
        ·
          refine ⟨20065830386302564595368087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26754440515070086127157449 20065830386302564595368087)
          ·
            refine ⟨30098745579453846893052131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20065830386302564595368087 30098745579453846893052131)
            ·
              refine ⟨45148118369180770339578197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30098745579453846893052131 45148118369180770339578197)
              ·
                refine ⟨132269878034709288104233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45148118369180770339578197 132269878034709288104233)
                ·
                  rfl

theorem cell22_3477528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_3477528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477528 prefixEnd_3477528 := by exact prefixLift 3477528
  have htrace : WordTrace (prefixWord ++ tailWord_3477528) baseStart_3477528 baseEnd_3477528 := by
    simpa [prefixWord, tailWord_3477528, baseEnd_3477528] using wordTrace_append hprefix tailTrace_3477528
  have hstable : (prefixWord ++ tailWord_3477528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477528).length < 2 ^ (prefixWord ++ tailWord_3477528).sum := by decide
  have hdescent : baseEnd_3477528 < baseStart_3477528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477530 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_3477530 : Nat := 118140960795 + 3477530 * 2 ^ 59
def prefixEnd_3477530 : Nat := 4983230072969 + 3 ^ 40 * 3477530 * 2
def baseEnd_3477530 : Nat := 1190429586953256254388091

theorem tailTrace_3477530 : CollatzResearch.WordTrace tailWord_3477530 prefixEnd_3477530 1190429586953256254388091 := by
  unfold tailWord_3477530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31708984772877549921283511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84557292727673466456756029 31708984772877549921283511)
  ·
    refine ⟨47563477159316324881925267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31708984772877549921283511 47563477159316324881925267)
    ·
      refine ⟨71345215738974487322887901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47563477159316324881925267 71345215738974487322887901)
      ·
        refine ⟨26754455902115432746082963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71345215738974487322887901 26754455902115432746082963)
        ·
          refine ⟨40131683853173149119124445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26754455902115432746082963 40131683853173149119124445)
          ·
            refine ⟨15049381444939930919671667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40131683853173149119124445 15049381444939930919671667)
            ·
              refine ⟨22574072167409896379507501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049381444939930919671667 22574072167409896379507501)
              ·
                refine ⟨8465277062778711142315313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22574072167409896379507501 8465277062778711142315313)
                ·
                  refine ⟨6348957797084033356736485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8465277062778711142315313 6348957797084033356736485)
                  ·
                    refine ⟨1190429586953256254388091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6348957797084033356736485 1190429586953256254388091)
                    ·
                      rfl

theorem cell22_3477530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_3477530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477530 prefixEnd_3477530 := by exact prefixLift 3477530
  have htrace : WordTrace (prefixWord ++ tailWord_3477530) baseStart_3477530 baseEnd_3477530 := by
    simpa [prefixWord, tailWord_3477530, baseEnd_3477530] using wordTrace_append hprefix tailTrace_3477530
  have hstable : (prefixWord ++ tailWord_3477530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477530).length < 2 ^ (prefixWord ++ tailWord_3477530).sum := by decide
  have hdescent : baseEnd_3477530 < baseStart_3477530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477573 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 9]
def baseStart_3477573 : Nat := 118140960795 + 3477573 * 2 ^ 59
def prefixEnd_3477573 : Nat := 4983230072969 + 3 ^ 40 * 3477573 * 2
def baseEnd_3477573 : Nat := 396814768910672825187653

theorem tailTrace_3477573 : CollatzResearch.WordTrace tailWord_3477573 prefixEnd_3477573 396814768910672825187653 := by
  unfold tailWord_3477573
  simp only [CollatzResearch.WordTrace]
  refine ⟨126837507430354418028949373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84558338286902945352632915 126837507430354418028949373)
  ·
    refine ⟨47564065286382906760856015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126837507430354418028949373 47564065286382906760856015)
    ·
      refine ⟨71346097929574360141284023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47564065286382906760856015 71346097929574360141284023)
      ·
        refine ⟨107019146894361540211926035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71346097929574360141284023 107019146894361540211926035)
        ·
          refine ⟨160528720341542310317889053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107019146894361540211926035 160528720341542310317889053)
          ·
            refine ⟨60198270128078366369208395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160528720341542310317889053 60198270128078366369208395)
            ·
              refine ⟨90297405192117549553812593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60198270128078366369208395 90297405192117549553812593)
              ·
                refine ⟨67723053894088162165359445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90297405192117549553812593 67723053894088162165359445)
                ·
                  refine ⟨396814768910672825187653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67723053894088162165359445 396814768910672825187653)
                  ·
                    rfl

theorem cell22_3477573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_3477573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477573 prefixEnd_3477573 := by exact prefixLift 3477573
  have htrace : WordTrace (prefixWord ++ tailWord_3477573) baseStart_3477573 baseEnd_3477573 := by
    simpa [prefixWord, tailWord_3477573, baseEnd_3477573] using wordTrace_append hprefix tailTrace_3477573
  have hstable : (prefixWord ++ tailWord_3477573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477573).length < 2 ^ (prefixWord ++ tailWord_3477573).sum := by decide
  have hdescent : baseEnd_3477573 < baseStart_3477573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477594 : List Nat := [3, 1, 1, 2, 1, 1, 6, 3, 1, 3]
def baseStart_3477594 : Nat := 118140960795 + 3477594 * 2 ^ 59
def prefixEnd_3477594 : Nat := 4983230072969 + 3 ^ 40 * 3477594 * 2
def baseEnd_3477594 : Nat := 1190451495461181420787895

theorem tailTrace_3477594 : CollatzResearch.WordTrace tailWord_3477594 prefixEnd_3477594 1190451495461181420787895 := by
  unfold tailWord_3477594
  simp only [CollatzResearch.WordTrace]
  refine ⟨31709568340819584653865959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84558848908852225743642557 31709568340819584653865959)
  ·
    refine ⟨47564352511229376980798939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31709568340819584653865959 47564352511229376980798939)
    ·
      refine ⟨71346528766844065471198409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47564352511229376980798939 71346528766844065471198409)
      ·
        refine ⟨53509896575133049103398807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71346528766844065471198409 53509896575133049103398807)
        ·
          refine ⟨80264844862699573655098211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53509896575133049103398807 80264844862699573655098211)
          ·
            refine ⟨120397267294049360482647317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80264844862699573655098211 120397267294049360482647317)
            ·
              refine ⟨5643621904408563772624093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120397267294049360482647317 5643621904408563772624093)
              ·
                refine ⟨2116358214153211414734035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5643621904408563772624093 2116358214153211414734035)
                ·
                  refine ⟨3174537321229817122101053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116358214153211414734035 3174537321229817122101053)
                  ·
                    refine ⟨1190451495461181420787895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174537321229817122101053 1190451495461181420787895)
                    ·
                      rfl

theorem cell22_3477594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 1, 3].length) (baseStart_3477594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477594 prefixEnd_3477594 := by exact prefixLift 3477594
  have htrace : WordTrace (prefixWord ++ tailWord_3477594) baseStart_3477594 baseEnd_3477594 := by
    simpa [prefixWord, tailWord_3477594, baseEnd_3477594] using wordTrace_append hprefix tailTrace_3477594
  have hstable : (prefixWord ++ tailWord_3477594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477594).length < 2 ^ (prefixWord ++ tailWord_3477594).sum := by decide
  have hdescent : baseEnd_3477594 < baseStart_3477594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477605 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_3477605 : Nat := 118140960795 + 3477605 * 2 ^ 59
def prefixEnd_3477605 : Nat := 4983230072969 + 3 ^ 40 * 3477605 * 2
def baseEnd_3477605 : Nat := 1190455260985981058762861

theorem tailTrace_3477605 : CollatzResearch.WordTrace tailWord_3477605 prefixEnd_3477605 1190455260985981058762861 := by
  unfold tailWord_3477605
  simp only [CollatzResearch.WordTrace]
  refine ⟨126838674566238487494114269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84559116377492324996076179 126838674566238487494114269)
  ·
    refine ⟨47564502962339432810292851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126838674566238487494114269 47564502962339432810292851)
    ·
      refine ⟨71346754443509149215439277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47564502962339432810292851 71346754443509149215439277)
      ·
        refine ⟨26755032916315930955789729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71346754443509149215439277 26755032916315930955789729)
        ·
          refine ⟨20066274687236948216842297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26755032916315930955789729 20066274687236948216842297)
          ·
            refine ⟨15049706015427711162631723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20066274687236948216842297 15049706015427711162631723)
            ·
              refine ⟨22574559023141566743947585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049706015427711162631723 22574559023141566743947585)
              ·
                refine ⟨16930919267356175057960689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22574559023141566743947585 16930919267356175057960689)
                ·
                  refine ⟨12698189450517131293470517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16930919267356175057960689 12698189450517131293470517)
                  ·
                    refine ⟨1190455260985981058762861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12698189450517131293470517 1190455260985981058762861)
                    ·
                      rfl

theorem cell22_3477605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_3477605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477605 prefixEnd_3477605 := by exact prefixLift 3477605
  have htrace : WordTrace (prefixWord ++ tailWord_3477605) baseStart_3477605 baseEnd_3477605 := by
    simpa [prefixWord, tailWord_3477605, baseEnd_3477605] using wordTrace_append hprefix tailTrace_3477605
  have hstable : (prefixWord ++ tailWord_3477605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477605).length < 2 ^ (prefixWord ++ tailWord_3477605).sum := by decide
  have hdescent : baseEnd_3477605 < baseStart_3477605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477622 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3477622 : Nat := 118140960795 + 3477622 * 2 ^ 59
def prefixEnd_3477622 : Nat := 4983230072969 + 3 ^ 40 * 3477622 * 2
def baseEnd_3477622 : Nat := 1190461080433398681087809

theorem tailTrace_3477622 : CollatzResearch.WordTrace tailWord_3477622 prefixEnd_3477622 1190461080433398681087809 := by
  unfold tailWord_3477622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927455912948556212342695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84559529738117932931655413 7927455912948556212342695)
  ·
    refine ⟨11891183869422834318514043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7927455912948556212342695 11891183869422834318514043)
    ·
      refine ⟨17836775804134251477771065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11891183869422834318514043 17836775804134251477771065)
      ·
        refine ⟨13377581853100688608328299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17836775804134251477771065 13377581853100688608328299)
        ·
          refine ⟨20066372779651032912492449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13377581853100688608328299 20066372779651032912492449)
          ·
            refine ⟨15049779584738274684369337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20066372779651032912492449 15049779584738274684369337)
            ·
              refine ⟨11287334688553706013277003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15049779584738274684369337 11287334688553706013277003)
              ·
                refine ⟨16931002032830559019915505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11287334688553706013277003 16931002032830559019915505)
                ·
                  refine ⟨12698251524622919264936629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16931002032830559019915505 12698251524622919264936629)
                  ·
                    refine ⟨1190461080433398681087809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12698251524622919264936629 1190461080433398681087809)
                    ·
                      rfl

theorem cell22_3477622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3477622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477622 prefixEnd_3477622 := by exact prefixLift 3477622
  have htrace : WordTrace (prefixWord ++ tailWord_3477622) baseStart_3477622 baseEnd_3477622 := by
    simpa [prefixWord, tailWord_3477622, baseEnd_3477622] using wordTrace_append hprefix tailTrace_3477622
  have hstable : (prefixWord ++ tailWord_3477622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477622).length < 2 ^ (prefixWord ++ tailWord_3477622).sum := by decide
  have hdescent : baseEnd_3477622 < baseStart_3477622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477635 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 6]
def baseStart_3477635 : Nat := 118140960795 + 3477635 * 2 ^ 59
def prefixEnd_3477635 : Nat := 4983230072969 + 3 ^ 40 * 3477635 * 2
def baseEnd_3477635 : Nat := 396821843533023660170923

theorem tailTrace_3477635 : CollatzResearch.WordTrace tailWord_3477635 prefixEnd_3477635 396821843533023660170923 := by
  unfold tailWord_3477635
  simp only [CollatzResearch.WordTrace]
  refine ⟨126839768756129802617706359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84559845837419868411804239 126839768756129802617706359)
  ·
    refine ⟨190259653134194703926559539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126839768756129802617706359 190259653134194703926559539)
    ·
      refine ⟨285389479701292055889839309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190259653134194703926559539 285389479701292055889839309)
      ·
        refine ⟨107021054887984520958689741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285389479701292055889839309 107021054887984520958689741)
        ·
          refine ⟨40132895582994195359508653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107021054887984520958689741 40132895582994195359508653)
          ·
            refine ⟨15049835843622823259815745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40132895582994195359508653 15049835843622823259815745)
            ·
              refine ⟨11287376882717117444861809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15049835843622823259815745 11287376882717117444861809)
              ·
                refine ⟨8465532662037838083646357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11287376882717117444861809 8465532662037838083646357)
                ·
                  refine ⟨396821843533023660170923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8465532662037838083646357 396821843533023660170923)
                  ·
                    rfl

theorem cell22_3477635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 6].length) (baseStart_3477635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477635 prefixEnd_3477635 := by exact prefixLift 3477635
  have htrace : WordTrace (prefixWord ++ tailWord_3477635) baseStart_3477635 baseEnd_3477635 := by
    simpa [prefixWord, tailWord_3477635, baseEnd_3477635] using wordTrace_append hprefix tailTrace_3477635
  have hstable : (prefixWord ++ tailWord_3477635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477635).length < 2 ^ (prefixWord ++ tailWord_3477635).sum := by decide
  have hdescent : baseEnd_3477635 < baseStart_3477635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477637 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_3477637 : Nat := 118140960795 + 3477637 * 2 ^ 59
def prefixEnd_3477637 : Nat := 4983230072969 + 3 ^ 40 * 3477637 * 2
def baseEnd_3477637 : Nat := 1190466215239943641962763

theorem tailTrace_3477637 : CollatzResearch.WordTrace tailWord_3477637 prefixEnd_3477637 1190466215239943641962763 := by
  unfold tailWord_3477637
  simp only [CollatzResearch.WordTrace]
  refine ⟨126839841702122556959279165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84559894468081704639519443 126839841702122556959279165)
  ·
    refine ⟨47564940638295958859729687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126839841702122556959279165 47564940638295958859729687)
    ·
      refine ⟨71347410957443938289594531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47564940638295958859729687 71347410957443938289594531)
      ·
        refine ⟨107021116436165907434391797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71347410957443938289594531 107021116436165907434391797)
        ·
          refine ⟨10033229665890553821974231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107021116436165907434391797 10033229665890553821974231)
          ·
            refine ⟨15049844498835830732961347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033229665890553821974231 15049844498835830732961347)
            ·
              refine ⟨22574766748253746099442021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15049844498835830732961347 22574766748253746099442021)
              ·
                refine ⟨4232768765297577393645379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22574766748253746099442021 4232768765297577393645379)
                ·
                  refine ⟨6349153147946366090468069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4232768765297577393645379 6349153147946366090468069)
                  ·
                    refine ⟨1190466215239943641962763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6349153147946366090468069 1190466215239943641962763)
                    ·
                      rfl

theorem cell22_3477637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_3477637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477637 prefixEnd_3477637 := by exact prefixLift 3477637
  have htrace : WordTrace (prefixWord ++ tailWord_3477637) baseStart_3477637 baseEnd_3477637 := by
    simpa [prefixWord, tailWord_3477637, baseEnd_3477637] using wordTrace_append hprefix tailTrace_3477637
  have hstable : (prefixWord ++ tailWord_3477637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477637).length < 2 ^ (prefixWord ++ tailWord_3477637).sum := by decide
  have hdescent : baseEnd_3477637 < baseStart_3477637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477669 : List Nat := [1, 3, 1, 2, 1, 3, 5, 2, 4]
def baseStart_3477669 : Nat := 118140960795 + 3477669 * 2 ^ 59
def prefixEnd_3477669 : Nat := 4983230072969 + 3 ^ 40 * 3477669 * 2
def baseEnd_3477669 : Nat := 396825723164635408387555

theorem tailTrace_3477669 : CollatzResearch.WordTrace tailWord_3477669 prefixEnd_3477669 396825723164635408387555 := by
  unfold tailWord_3477669
  simp only [CollatzResearch.WordTrace]
  refine ⟨126841008838006626424444061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84560672558671084282962707 126841008838006626424444061)
  ·
    refine ⟨47565378314252484909166523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126841008838006626424444061 47565378314252484909166523)
    ·
      refine ⟨71348067471378727363749785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47565378314252484909166523 71348067471378727363749785)
      ·
        refine ⟨53511050603534045522812339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71348067471378727363749785 53511050603534045522812339)
        ·
          refine ⟨80266575905301068284218509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53511050603534045522812339 80266575905301068284218509)
          ·
            refine ⟨30099965964487900606581941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80266575905301068284218509 30099965964487900606581941)
            ·
              refine ⟨2821871809170740681867057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30099965964487900606581941 2821871809170740681867057)
              ·
                refine ⟨2116403856878055511400293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2821871809170740681867057 2116403856878055511400293)
                ·
                  refine ⟨396825723164635408387555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116403856878055511400293 396825723164635408387555)
                  ·
                    rfl

theorem cell22_3477669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_3477669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477669 prefixEnd_3477669 := by exact prefixLift 3477669
  have htrace : WordTrace (prefixWord ++ tailWord_3477669) baseStart_3477669 baseEnd_3477669 := by
    simpa [prefixWord, tailWord_3477669, baseEnd_3477669] using wordTrace_append hprefix tailTrace_3477669
  have hstable : (prefixWord ++ tailWord_3477669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477669).length < 2 ^ (prefixWord ++ tailWord_3477669).sum := by decide
  have hdescent : baseEnd_3477669 < baseStart_3477669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477718 : List Nat := [5, 2, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3477718 : Nat := 118140960795 + 3477718 * 2 ^ 59
def prefixEnd_3477718 : Nat := 4983230072969 + 3 ^ 40 * 3477718 * 2
def baseEnd_3477718 : Nat := 1190493943195286430687515

theorem tailTrace_3477718 : CollatzResearch.WordTrace tailWord_3477718 prefixEnd_3477718 1190493943195286430687515 := by
  unfold tailWord_3477718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927674750926819237061113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 84561864009886071861985205 7927674750926819237061113)
  ·
    refine ⟨5945756063195114427795835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7927674750926819237061113 5945756063195114427795835)
    ·
      refine ⟨8918634094792671641693753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5945756063195114427795835 8918634094792671641693753)
      ·
        refine ⟨6688975571094503731270315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8918634094792671641693753 6688975571094503731270315)
        ·
          refine ⟨10033463356641755596905473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6688975571094503731270315 10033463356641755596905473)
          ·
            refine ⟨7525097517481316697679105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10033463356641755596905473 7525097517481316697679105)
            ·
              refine ⟨5643823138110987523259329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7525097517481316697679105 5643823138110987523259329)
              ·
                refine ⟨4232867353583240642444497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5643823138110987523259329 4232867353583240642444497)
                ·
                  refine ⟨3174650515187430481833373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4232867353583240642444497 3174650515187430481833373)
                  ·
                    refine ⟨1190493943195286430687515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174650515187430481833373 1190493943195286430687515)
                    ·
                      rfl

theorem cell22_3477718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3477718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477718 prefixEnd_3477718 := by exact prefixLift 3477718
  have htrace : WordTrace (prefixWord ++ tailWord_3477718) baseStart_3477718 baseEnd_3477718 := by
    simpa [prefixWord, tailWord_3477718, baseEnd_3477718] using wordTrace_append hprefix tailTrace_3477718
  have hstable : (prefixWord ++ tailWord_3477718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477718).length < 2 ^ (prefixWord ++ tailWord_3477718).sum := by decide
  have hdescent : baseEnd_3477718 < baseStart_3477718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477731 : List Nat := [1, 1, 1, 8, 2, 1, 1, 7]
def baseStart_3477731 : Nat := 118140960795 + 3477731 * 2 ^ 59
def prefixEnd_3477731 : Nat := 4983230072969 + 3 ^ 40 * 3477731 * 2
def baseEnd_3477731 : Nat := 132277599262328747790275

theorem tailTrace_3477731 : CollatzResearch.WordTrace tailWord_3477731 prefixEnd_3477731 132277599262328747790275 := by
  unfold tailWord_3477731
  simp only [CollatzResearch.WordTrace]
  refine ⟨126843270163782011013201047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84562180109188007342134031 126843270163782011013201047)
  ·
    refine ⟨190264905245673016519801571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126843270163782011013201047 190264905245673016519801571)
    ·
      refine ⟨285397357868509524779702357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190264905245673016519801571 285397357868509524779702357)
      ·
        refine ⟨3344500287521595993512137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 285397357868509524779702357 3344500287521595993512137)
        ·
          refine ⟨2508375215641196995134103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344500287521595993512137 2508375215641196995134103)
          ·
            refine ⟨3762562823461795492701155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508375215641196995134103 3762562823461795492701155)
            ·
              refine ⟨5643844235192693239051733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762562823461795492701155 5643844235192693239051733)
              ·
                refine ⟨132277599262328747790275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5643844235192693239051733 132277599262328747790275)
                ·
                  rfl

theorem cell22_3477731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 7].length) (baseStart_3477731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477731 prefixEnd_3477731 := by exact prefixLift 3477731
  have htrace : WordTrace (prefixWord ++ tailWord_3477731) baseStart_3477731 baseEnd_3477731 := by
    simpa [prefixWord, tailWord_3477731, baseEnd_3477731] using wordTrace_append hprefix tailTrace_3477731
  have hstable : (prefixWord ++ tailWord_3477731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477731).length < 2 ^ (prefixWord ++ tailWord_3477731).sum := by decide
  have hdescent : baseEnd_3477731 < baseStart_3477731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477785 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_3477785 : Nat := 118140960795 + 3477785 * 2 ^ 59
def prefixEnd_3477785 : Nat := 4983230072969 + 3 ^ 40 * 3477785 * 2
def baseEnd_3477785 : Nat := 1190516878664520589262309

theorem tailTrace_3477785 : CollatzResearch.WordTrace tailWord_3477785 prefixEnd_3477785 1190516878664520589262309 := by
  unfold tailWord_3477785
  simp only [CollatzResearch.WordTrace]
  refine ⟨126845239705586378235666809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84563493137057585490444539 126845239705586378235666809)
  ·
    refine ⟨95133929779189783676750107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126845239705586378235666809 95133929779189783676750107)
    ·
      refine ⟨142700894668784675515125161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95133929779189783676750107 142700894668784675515125161)
      ·
        refine ⟨107025671001588506636343871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142700894668784675515125161 107025671001588506636343871)
        ·
          refine ⟨160538506502382759954515807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107025671001588506636343871 160538506502382759954515807)
          ·
            refine ⟨240807759753574139931773711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160538506502382759954515807 240807759753574139931773711)
            ·
              refine ⟨361211639630361209897660567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240807759753574139931773711 361211639630361209897660567)
              ·
                refine ⟨541817459445541814846490851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361211639630361209897660567 541817459445541814846490851)
                ·
                  refine ⟨812726189168312722269736277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541817459445541814846490851 812726189168312722269736277)
                  ·
                    refine ⟨1190516878664520589262309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 812726189168312722269736277 1190516878664520589262309)
                    ·
                      rfl

theorem cell22_3477785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_3477785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477785 prefixEnd_3477785 := by exact prefixLift 3477785
  have htrace : WordTrace (prefixWord ++ tailWord_3477785) baseStart_3477785 baseEnd_3477785 := by
    simpa [prefixWord, tailWord_3477785, baseEnd_3477785] using wordTrace_append hprefix tailTrace_3477785
  have hstable : (prefixWord ++ tailWord_3477785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477785).length < 2 ^ (prefixWord ++ tailWord_3477785).sum := by decide
  have hdescent : baseEnd_3477785 < baseStart_3477785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477881 : List Nat := [1, 2, 1, 3, 2, 1, 1, 7, 1, 3]
def baseStart_3477881 : Nat := 118140960795 + 3477881 * 2 ^ 59
def prefixEnd_3477881 : Nat := 4983230072969 + 3 ^ 40 * 3477881 * 2
def baseEnd_3477881 : Nat := 1190549741426408338862015

theorem tailTrace_3477881 : CollatzResearch.WordTrace tailWord_3477881 prefixEnd_3477881 1190549741426408338862015 := by
  unfold tailWord_3477881
  simp only [CollatzResearch.WordTrace]
  refine ⟨126848741113238586631161497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84565827408825724420774331 126848741113238586631161497)
  ·
    refine ⟨95136555834928939973371123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126848741113238586631161497 95136555834928939973371123)
    ·
      refine ⟨142704833752393409960056685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95136555834928939973371123 142704833752393409960056685)
      ·
        refine ⟨53514312657147528735021257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142704833752393409960056685 53514312657147528735021257)
        ·
          refine ⟨40135734492860646551265943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53514312657147528735021257 40135734492860646551265943)
          ·
            refine ⟨60203601739290969826898915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40135734492860646551265943 60203601739290969826898915)
            ·
              refine ⟨90305402608936454740348373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60203601739290969826898915 90305402608936454740348373)
              ·
                refine ⟨2116532873646948157976915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 90305402608936454740348373 2116532873646948157976915)
                ·
                  refine ⟨3174799310470422236965373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2116532873646948157976915 3174799310470422236965373)
                  ·
                    refine ⟨1190549741426408338862015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3174799310470422236965373 1190549741426408338862015)
                    ·
                      rfl

theorem cell22_3477881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 1, 3].length) (baseStart_3477881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477881 prefixEnd_3477881 := by exact prefixLift 3477881
  have htrace : WordTrace (prefixWord ++ tailWord_3477881) baseStart_3477881 baseEnd_3477881 := by
    simpa [prefixWord, tailWord_3477881, baseEnd_3477881] using wordTrace_append hprefix tailTrace_3477881
  have hstable : (prefixWord ++ tailWord_3477881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477881).length < 2 ^ (prefixWord ++ tailWord_3477881).sum := by decide
  have hdescent : baseEnd_3477881 < baseStart_3477881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477924 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_3477924 : Nat := 118140960795 + 3477924 * 2 ^ 59
def prefixEnd_3477924 : Nat := 4983230072969 + 3 ^ 40 * 3477924 * 2
def baseEnd_3477924 : Nat := 1190564461205170560036883

theorem tailTrace_3477924 : CollatzResearch.WordTrace tailWord_3477924 prefixEnd_3477924 1190564461205170560036883 := by
  unfold tailWord_3477924
  simp only [CollatzResearch.WordTrace]
  refine ⟨63425154726041402487488413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84566872968055203316651217 63425154726041402487488413)
  ·
    refine ⟨23784433022265525932808155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63425154726041402487488413 23784433022265525932808155)
    ·
      refine ⟨35676649533398288899212233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23784433022265525932808155 35676649533398288899212233)
      ·
        refine ⟨26757487150048716674409175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35676649533398288899212233 26757487150048716674409175)
        ·
          refine ⟨40136230725073075011613763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26757487150048716674409175 40136230725073075011613763)
          ·
            refine ⟨60204346087609612517420645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40136230725073075011613763 60204346087609612517420645)
            ·
              refine ⟨11288314891426802347016371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60204346087609612517420645 11288314891426802347016371)
              ·
                refine ⟨16932472337140203520524557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11288314891426802347016371 16932472337140203520524557)
                ·
                  refine ⟨6349677126427576320196709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16932472337140203520524557 6349677126427576320196709)
                  ·
                    refine ⟨1190564461205170560036883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6349677126427576320196709 1190564461205170560036883)
                    ·
                      rfl

theorem cell22_3477924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_3477924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477924 prefixEnd_3477924 := by exact prefixLift 3477924
  have htrace : WordTrace (prefixWord ++ tailWord_3477924) baseStart_3477924 baseEnd_3477924 := by
    simpa [prefixWord, tailWord_3477924, baseEnd_3477924] using wordTrace_append hprefix tailTrace_3477924
  have hstable : (prefixWord ++ tailWord_3477924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477924).length < 2 ^ (prefixWord ++ tailWord_3477924).sum := by decide
  have hdescent : baseEnd_3477924 < baseStart_3477924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3477967 : List Nat := [1, 1, 2, 1, 1, 4, 1, 11]
def baseStart_3477967 : Nat := 118140960795 + 3477967 * 2 ^ 59
def prefixEnd_3477967 : Nat := 4983230072969 + 3 ^ 40 * 3477967 * 2
def baseEnd_3477967 : Nat := 132286575664881420134639

theorem tailTrace_3477967 : CollatzResearch.WordTrace tailWord_3477967 prefixEnd_3477967 132286575664881420134639 := by
  unfold tailWord_3477967
  simp only [CollatzResearch.WordTrace]
  refine ⟨126851877790927023318792155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84567918527284682212528103 126851877790927023318792155)
  ·
    refine ⟨190277816686390534978188233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126851877790927023318792155 190277816686390534978188233)
    ·
      refine ⟨142708362514792901233641175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190277816686390534978188233 142708362514792901233641175)
      ·
        refine ⟨214062543772189351850461763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142708362514792901233641175 214062543772189351850461763)
        ·
          refine ⟨321093815658284027775692645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214062543772189351850461763 321093815658284027775692645)
          ·
            refine ⟨60205090435928255207942371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321093815658284027775692645 60205090435928255207942371)
            ·
              refine ⟨90307635653892382811913557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60205090435928255207942371 90307635653892382811913557)
              ·
                refine ⟨132286575664881420134639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 90307635653892382811913557 132286575664881420134639)
                ·
                  rfl

theorem cell22_3477967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 11].length) (baseStart_3477967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3477967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3477967 prefixEnd_3477967 := by exact prefixLift 3477967
  have htrace : WordTrace (prefixWord ++ tailWord_3477967) baseStart_3477967 baseEnd_3477967 := by
    simpa [prefixWord, tailWord_3477967, baseEnd_3477967] using wordTrace_append hprefix tailTrace_3477967
  have hstable : (prefixWord ++ tailWord_3477967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3477967).length < 2 ^ (prefixWord ++ tailWord_3477967).sum := by decide
  have hdescent : baseEnd_3477967 < baseStart_3477967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3477967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478018 : List Nat := [3, 4, 1, 2, 2, 1, 2, 7]
def baseStart_3478018 : Nat := 118140960795 + 3478018 * 2 ^ 59
def prefixEnd_3478018 : Nat := 4983230072969 + 3 ^ 40 * 3478018 * 2
def baseEnd_3478018 : Nat := 132288515480687294242955

theorem tailTrace_3478018 : CollatzResearch.WordTrace tailWord_3478018 prefixEnd_3478018 132288515480687294242955 := by
  unfold tailWord_3478018
  simp only [CollatzResearch.WordTrace]
  refine ⟨31713434478435564757224677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84569158609161506019265805 31713434478435564757224677)
  ·
    refine ⟨5946268964706668391979627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31713434478435564757224677 5946268964706668391979627)
    ·
      refine ⟨8919403447060002587969441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946268964706668391979627 8919403447060002587969441)
      ·
        refine ⟨6689552585295001940977081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8919403447060002587969441 6689552585295001940977081)
        ·
          refine ⟨5017164438971251455732811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6689552585295001940977081 5017164438971251455732811)
          ·
            refine ⟨7525746658456877183599217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5017164438971251455732811 7525746658456877183599217)
            ·
              refine ⟨5644309993842657887699413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7525746658456877183599217 5644309993842657887699413)
              ·
                refine ⟨132288515480687294242955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5644309993842657887699413 132288515480687294242955)
                ·
                  rfl

theorem cell22_3478018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 7].length) (baseStart_3478018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478018 prefixEnd_3478018 := by exact prefixLift 3478018
  have htrace : WordTrace (prefixWord ++ tailWord_3478018) baseStart_3478018 baseEnd_3478018 := by
    simpa [prefixWord, tailWord_3478018, baseEnd_3478018] using wordTrace_append hprefix tailTrace_3478018
  have hstable : (prefixWord ++ tailWord_3478018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478018).length < 2 ^ (prefixWord ++ tailWord_3478018).sum := by decide
  have hdescent : baseEnd_3478018 < baseStart_3478018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478076 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_3478076 : Nat := 118140960795 + 3478076 * 2 ^ 59
def prefixEnd_3478076 : Nat := 4983230072969 + 3 ^ 40 * 3478076 * 2
def baseEnd_3478076 : Nat := 1190616493911492830236417

theorem tailTrace_3478076 : CollatzResearch.WordTrace tailWord_3478076 prefixEnd_3478076 1190616493911492830236417 := by
  unfold tailWord_3478076
  simp only [CollatzResearch.WordTrace]
  refine ⟨63427926673766067467255041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 84570568898354756623006721 63427926673766067467255041)
  ·
    refine ⟨47570945005324550600441281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63427926673766067467255041 47570945005324550600441281)
    ·
      refine ⟨35678208753993412950330961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47570945005324550600441281 35678208753993412950330961)
      ·
        refine ⟨26758656565495059712748221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35678208753993412950330961 26758656565495059712748221)
        ·
          refine ⟨10034496212060647392280583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26758656565495059712748221 10034496212060647392280583)
          ·
            refine ⟨15051744318090971088420875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10034496212060647392280583 15051744318090971088420875)
            ·
              refine ⟨22577616477136456632631313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15051744318090971088420875 22577616477136456632631313)
              ·
                refine ⟨16933212357852342474473485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22577616477136456632631313 16933212357852342474473485)
                ·
                  refine ⟨6349954634194628427927557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16933212357852342474473485 6349954634194628427927557)
                  ·
                    refine ⟨1190616493911492830236417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6349954634194628427927557 1190616493911492830236417)
                    ·
                      rfl

theorem cell22_3478076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_3478076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478076 prefixEnd_3478076 := by exact prefixLift 3478076
  have htrace : WordTrace (prefixWord ++ tailWord_3478076) baseStart_3478076 baseEnd_3478076 := by
    simpa [prefixWord, tailWord_3478076, baseEnd_3478076] using wordTrace_append hprefix tailTrace_3478076
  have hstable : (prefixWord ++ tailWord_3478076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478076).length < 2 ^ (prefixWord ++ tailWord_3478076).sum := by decide
  have hdescent : baseEnd_3478076 < baseStart_3478076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478093 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3478093 : Nat := 118140960795 + 3478093 * 2 ^ 59
def prefixEnd_3478093 : Nat := 4983230072969 + 3 ^ 40 * 3478093 * 2
def baseEnd_3478093 : Nat := 1190622313358910452561365

theorem tailTrace_3478093 : CollatzResearch.WordTrace tailWord_3478093 prefixEnd_3478093 1190622313358910452561365 := by
  unfold tailWord_3478093
  simp only [CollatzResearch.WordTrace]
  refine ⟨126856473388470546837878933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84570982258980364558585955 126856473388470546837878933)
  ·
    refine ⟨5946397190084556883025575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 126856473388470546837878933 5946397190084556883025575)
    ·
      refine ⟨8919595785126835324538363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946397190084556883025575 8919595785126835324538363)
      ·
        refine ⟨13379393677690252986807545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8919595785126835324538363 13379393677690252986807545)
        ·
          refine ⟨10034545258267689740105659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13379393677690252986807545 10034545258267689740105659)
          ·
            refine ⟨15051817887401534610158489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10034545258267689740105659 15051817887401534610158489)
            ·
              refine ⟨11288863415551150957618867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15051817887401534610158489 11288863415551150957618867)
              ·
                refine ⟨16933295123326726436428301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11288863415551150957618867 16933295123326726436428301)
                ·
                  refine ⟨6349985671247522413660613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16933295123326726436428301 6349985671247522413660613)
                  ·
                    refine ⟨1190622313358910452561365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6349985671247522413660613 1190622313358910452561365)
                    ·
                      rfl

theorem cell22_3478093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3478093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478093 prefixEnd_3478093 := by exact prefixLift 3478093
  have htrace : WordTrace (prefixWord ++ tailWord_3478093) baseStart_3478093 baseEnd_3478093 := by
    simpa [prefixWord, tailWord_3478093, baseEnd_3478093] using wordTrace_append hprefix tailTrace_3478093
  have hstable : (prefixWord ++ tailWord_3478093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478093).length < 2 ^ (prefixWord ++ tailWord_3478093).sum := by decide
  have hdescent : baseEnd_3478093 < baseStart_3478093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478170 : List Nat := [3, 1, 1, 6, 2, 1, 8]
def baseStart_3478170 : Nat := 118140960795 + 3478170 * 2 ^ 59
def prefixEnd_3478170 : Nat := 4983230072969 + 3 ^ 40 * 3478170 * 2
def baseEnd_3478170 : Nat := 44098098964166959940227

theorem tailTrace_3478170 : CollatzResearch.WordTrace tailWord_3478170 prefixEnd_3478170 44098098964166959940227 := by
  unfold tailWord_3478170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31714820452297897247107991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 84572854539461059325621309 31714820452297897247107991)
  ·
    refine ⟨47572230678446845870661987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31714820452297897247107991 47572230678446845870661987)
    ·
      refine ⟨71358346017670268805992981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47572230678446845870661987 71358346017670268805992981)
      ·
        refine ⟨3344922469578293850280921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71358346017670268805992981 3344922469578293850280921)
        ·
          refine ⟨2508691852183720387710691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344922469578293850280921 2508691852183720387710691)
          ·
            refine ⟨3763037778275580581566037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508691852183720387710691 3763037778275580581566037)
            ·
              refine ⟨44098098964166959940227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3763037778275580581566037 44098098964166959940227)
              ·
                rfl

theorem cell22_3478170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 8].length) (baseStart_3478170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478170 prefixEnd_3478170 := by exact prefixLift 3478170
  have htrace : WordTrace (prefixWord ++ tailWord_3478170) baseStart_3478170 baseEnd_3478170 := by
    simpa [prefixWord, tailWord_3478170, baseEnd_3478170] using wordTrace_append hprefix tailTrace_3478170
  have hstable : (prefixWord ++ tailWord_3478170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478170).length < 2 ^ (prefixWord ++ tailWord_3478170).sum := by decide
  have hdescent : baseEnd_3478170 < baseStart_3478170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3478181 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 5]
def baseStart_3478181 : Nat := 118140960795 + 3478181 * 2 ^ 59
def prefixEnd_3478181 : Nat := 4983230072969 + 3 ^ 40 * 3478181 * 2
def baseEnd_3478181 : Nat := 396884145852435852120365

theorem tailTrace_3478181 : CollatzResearch.WordTrace tailWord_3478181 prefixEnd_3478181 396884145852435852120365 := by
  unfold tailWord_3478181
  simp only [CollatzResearch.WordTrace]
  refine ⟨126859683012151737867082397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 84573122008101158578054931 126859683012151737867082397)
  ·
    refine ⟨47572381129556901700155899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126859683012151737867082397 47572381129556901700155899)
    ·
      refine ⟨71358571694335352550233849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47572381129556901700155899 71358571694335352550233849)
      ·
        refine ⟨53518928770751514412675387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71358571694335352550233849 53518928770751514412675387)
        ·
          refine ⟨80278393156127271619013081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53518928770751514412675387 80278393156127271619013081)
          ·
            refine ⟨60208794867095453714259811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80278393156127271619013081 60208794867095453714259811)
            ·
              refine ⟨90313192300643180571389717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60208794867095453714259811 90313192300643180571389717)
              ·
                refine ⟨4233430889092649089283893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90313192300643180571389717 4233430889092649089283893)
                ·
                  refine ⟨396884145852435852120365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4233430889092649089283893 396884145852435852120365)
                  ·
                    rfl

theorem cell22_3478181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_3478181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3478181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3478181 prefixEnd_3478181 := by exact prefixLift 3478181
  have htrace : WordTrace (prefixWord ++ tailWord_3478181) baseStart_3478181 baseEnd_3478181 := by
    simpa [prefixWord, tailWord_3478181, baseEnd_3478181] using wordTrace_append hprefix tailTrace_3478181
  have hstable : (prefixWord ++ tailWord_3478181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3478181).length < 2 ^ (prefixWord ++ tailWord_3478181).sum := by decide
  have hdescent : baseEnd_3478181 < baseStart_3478181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3478181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
