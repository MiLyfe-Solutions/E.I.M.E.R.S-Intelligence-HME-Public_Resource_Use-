import V185TrunkScan23Chunk0612

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3625430 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_3625430 : Nat := 118140960795 + 3625430 * 2 ^ 59
def prefixEnd_3625430 : Nat := 4983230072969 + 3 ^ 40 * 3625430 * 2
def baseEnd_3625430 : Nat := 620529389743285240717319

theorem tailTrace_3625430 : CollatzResearch.WordTrace tailWord_3625430 prefixEnd_3625430 620529389743285240717319 := by
  unfold tailWord_3625430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8264393453480859937133609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88153530170462505996091829 8264393453480859937133609)
  ·
    refine ⟨6198295090110644952850207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8264393453480859937133609 6198295090110644952850207)
    ·
      refine ⟨9297442635165967429275311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6198295090110644952850207 9297442635165967429275311)
      ·
        refine ⟨13946163952748951143912967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9297442635165967429275311 13946163952748951143912967)
        ·
          refine ⟨20919245929123426715869451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13946163952748951143912967 20919245929123426715869451)
          ·
            refine ⟨31378868893685140073804177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20919245929123426715869451 31378868893685140073804177)
            ·
              refine ⟨23534151670263855055353133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31378868893685140073804177 23534151670263855055353133)
              ·
                refine ⟨8825306876348945645757425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23534151670263855055353133 8825306876348945645757425)
                ·
                  refine ⟨6618980157261709234318069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8825306876348945645757425 6618980157261709234318069)
                  ·
                    refine ⟨620529389743285240717319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6618980157261709234318069 620529389743285240717319)
                    ·
                      rfl

theorem cell23_3625430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_3625430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625430 prefixEnd_3625430 := by exact prefixLift 3625430
  have htrace : WordTrace (prefixWord ++ tailWord_3625430) baseStart_3625430 baseEnd_3625430 := by
    simpa [prefixWord, tailWord_3625430, baseEnd_3625430] using wordTrace_append hprefix tailTrace_3625430
  have hstable : (prefixWord ++ tailWord_3625430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625430).length < 2 ^ (prefixWord ++ tailWord_3625430).sum := by decide
  have hdescent : baseEnd_3625430 < baseStart_3625430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625433 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_3625433 : Nat := 118140960795 + 3625433 * 2 ^ 59
def prefixEnd_3625433 : Nat := 4983230072969 + 3 ^ 40 * 3625433 * 2
def baseEnd_3625433 : Nat := 1861589709671819210414443

theorem tailTrace_3625433 : CollatzResearch.WordTrace tailWord_3625433 prefixEnd_3625433 1861589709671819210414443 := by
  unfold tailWord_3625433
  simp only [CollatzResearch.WordTrace]
  refine ⟨132230404674682890506496953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88153603116455260337664635 132230404674682890506496953)
  ·
    refine ⟨99172803506012167879872715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132230404674682890506496953 99172803506012167879872715)
    ·
      refine ⟨148759205259018251819809073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99172803506012167879872715 148759205259018251819809073)
      ·
        refine ⟨111569403944263688864856805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148759205259018251819809073 111569403944263688864856805)
        ·
          refine ⟨20919263239549441662160651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111569403944263688864856805 20919263239549441662160651)
          ·
            refine ⟨31378894859324162493240977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20919263239549441662160651 31378894859324162493240977)
            ·
              refine ⟨23534171144493121869930733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31378894859324162493240977 23534171144493121869930733)
              ·
                refine ⟨8825314179184920701224025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23534171144493121869930733 8825314179184920701224025)
                ·
                  refine ⟨6618985634388690525918019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8825314179184920701224025 6618985634388690525918019)
                  ·
                    refine ⟨9928478451583035788877029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6618985634388690525918019 9928478451583035788877029)
                    ·
                      refine ⟨1861589709671819210414443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9928478451583035788877029 1861589709671819210414443)
                      ·
                        rfl

theorem cell23_3625433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_3625433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625433 prefixEnd_3625433 := by exact prefixLift 3625433
  have htrace : WordTrace (prefixWord ++ tailWord_3625433) baseStart_3625433 baseEnd_3625433 := by
    simpa [prefixWord, tailWord_3625433, baseEnd_3625433] using wordTrace_append hprefix tailTrace_3625433
  have hstable : (prefixWord ++ tailWord_3625433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625433).length < 2 ^ (prefixWord ++ tailWord_3625433).sum := by decide
  have hdescent : baseEnd_3625433 < baseStart_3625433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625450 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_3625450 : Nat := 118140960795 + 3625450 * 2 ^ 59
def prefixEnd_3625450 : Nat := 4983230072969 + 3 ^ 40 * 3625450 * 2
def baseEnd_3625450 : Nat := 1861598438842945643901865

theorem tailTrace_3625450 : CollatzResearch.WordTrace tailWord_3625450 prefixEnd_3625450 1861598438842945643901865 := by
  unfold tailWord_3625450
  simp only [CollatzResearch.WordTrace]
  refine ⟨33057756178905325602466451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88154016477080868273243869 33057756178905325602466451)
  ·
    refine ⟨49586634268357988403699677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33057756178905325602466451 49586634268357988403699677)
    ·
      refine ⟨18594987850634245651387379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49586634268357988403699677 18594987850634245651387379)
      ·
        refine ⟨27892481775951368477081069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18594987850634245651387379 27892481775951368477081069)
        ·
          refine ⟨10459680665981763178905401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27892481775951368477081069 10459680665981763178905401)
          ·
            refine ⟨7844760499486322384179051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10459680665981763178905401 7844760499486322384179051)
            ·
              refine ⟨11767140749229483576268577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7844760499486322384179051 11767140749229483576268577)
              ·
                refine ⟨8825355561922112682201433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11767140749229483576268577 8825355561922112682201433)
                ·
                  refine ⟨6619016671441584511651075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8825355561922112682201433 6619016671441584511651075)
                  ·
                    refine ⟨9928525007162376767476613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6619016671441584511651075 9928525007162376767476613)
                    ·
                      refine ⟨1861598438842945643901865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9928525007162376767476613 1861598438842945643901865)
                      ·
                        rfl

theorem cell23_3625450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_3625450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625450 prefixEnd_3625450 := by exact prefixLift 3625450
  have htrace : WordTrace (prefixWord ++ tailWord_3625450) baseStart_3625450 baseEnd_3625450 := by
    simpa [prefixWord, tailWord_3625450, baseEnd_3625450] using wordTrace_append hprefix tailTrace_3625450
  have hstable : (prefixWord ++ tailWord_3625450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625450).length < 2 ^ (prefixWord ++ tailWord_3625450).sum := by decide
  have hdescent : baseEnd_3625450 < baseStart_3625450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625456 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 8]
def baseStart_3625456 : Nat := 118140960795 + 3625456 * 2 ^ 59
def prefixEnd_3625456 : Nat := 4983230072969 + 3 ^ 40 * 3625456 * 2
def baseEnd_3625456 : Nat := 206844613302985846714093

theorem tailTrace_3625456 : CollatzResearch.WordTrace tailWord_3625456 prefixEnd_3625456 206844613302985846714093 := by
  unfold tailWord_3625456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66115621776799782717292111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88154162369066376956389481 66115621776799782717292111)
  ·
    refine ⟨99173432665199674075938167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66115621776799782717292111 99173432665199674075938167)
    ·
      refine ⟨148760148997799511113907251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99173432665199674075938167 148760148997799511113907251)
      ·
        refine ⟨223140223496699266670860877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148760148997799511113907251 223140223496699266670860877)
        ·
          refine ⟨83677583811262225001572829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223140223496699266670860877 83677583811262225001572829)
          ·
            refine ⟨31379093929223334375589811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83677583811262225001572829 31379093929223334375589811)
            ·
              refine ⟨47068640893835001563384717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31379093929223334375589811 47068640893835001563384717)
              ·
                refine ⟨17650740335188125586269269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47068640893835001563384717 17650740335188125586269269)
                ·
                  refine ⟨206844613302985846714093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17650740335188125586269269 206844613302985846714093)
                  ·
                    rfl

theorem cell23_3625456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 8].length) (baseStart_3625456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625456 prefixEnd_3625456 := by exact prefixLift 3625456
  have htrace : WordTrace (prefixWord ++ tailWord_3625456) baseStart_3625456 baseEnd_3625456 := by
    simpa [prefixWord, tailWord_3625456, baseEnd_3625456] using wordTrace_append hprefix tailTrace_3625456
  have hstable : (prefixWord ++ tailWord_3625456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625456).length < 2 ^ (prefixWord ++ tailWord_3625456).sum := by decide
  have hdescent : baseEnd_3625456 < baseStart_3625456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625511 : List Nat := [1, 1, 7, 2, 1, 1, 1, 4, 1, 4]
def baseStart_3625511 : Nat := 118140960795 + 3625511 * 2 ^ 59
def prefixEnd_3625511 : Nat := 4983230072969 + 3 ^ 40 * 3625511 * 2
def baseEnd_3625511 : Nat := 620543253720956635079695

theorem tailTrace_3625511 : CollatzResearch.WordTrace tailWord_3625511 prefixEnd_3625511 620543253720956635079695 := by
  unfold tailWord_3625511
  simp only [CollatzResearch.WordTrace]
  refine ⟨132233249568400309827836387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88155499712266873218557591 132233249568400309827836387)
  ·
    refine ⟨198349874352600464741754581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132233249568400309827836387 198349874352600464741754581)
    ·
      refine ⟨4648825180139073392384873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 198349874352600464741754581 4648825180139073392384873)
      ·
        refine ⟨3486618885104305044288655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4648825180139073392384873 3486618885104305044288655)
        ·
          refine ⟨5229928327656457566432983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486618885104305044288655 5229928327656457566432983)
          ·
            refine ⟨7844892491484686349649475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5229928327656457566432983 7844892491484686349649475)
            ·
              refine ⟨11767338737227029524474213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7844892491484686349649475 11767338737227029524474213)
              ·
                refine ⟨2206376013230068035838915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11767338737227029524474213 2206376013230068035838915)
                ·
                  refine ⟨3309564019845102053758373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206376013230068035838915 3309564019845102053758373)
                  ·
                    refine ⟨620543253720956635079695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309564019845102053758373 620543253720956635079695)
                    ·
                      rfl

theorem cell23_3625511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_3625511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625511 prefixEnd_3625511 := by exact prefixLift 3625511
  have htrace : WordTrace (prefixWord ++ tailWord_3625511) baseStart_3625511 baseEnd_3625511 := by
    simpa [prefixWord, tailWord_3625511, baseEnd_3625511] using wordTrace_append hprefix tailTrace_3625511
  have hstable : (prefixWord ++ tailWord_3625511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625511).length < 2 ^ (prefixWord ++ tailWord_3625511).sum := by decide
  have hdescent : baseEnd_3625511 < baseStart_3625511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625523 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 4]
def baseStart_3625523 : Nat := 118140960795 + 3625523 * 2 ^ 59
def prefixEnd_3625523 : Nat := 4983230072969 + 3 ^ 40 * 3625523 * 2
def baseEnd_3625523 : Nat := 1861635922930723858289029

theorem tailTrace_3625523 : CollatzResearch.WordTrace tailWord_3625523 prefixEnd_3625523 1861635922930723858289029 := by
  unfold tailWord_3625523
  simp only [CollatzResearch.WordTrace]
  refine ⟨132233687244356835877273223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88155791496237890584848815 132233687244356835877273223)
  ·
    refine ⟨198350530866535253815909835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132233687244356835877273223 198350530866535253815909835)
    ·
      refine ⟨297525796299802880723864753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198350530866535253815909835 297525796299802880723864753)
      ·
        refine ⟨223144347224852160542898565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297525796299802880723864753 223144347224852160542898565)
        ·
          refine ⟨41839565104659780101793481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223144347224852160542898565 41839565104659780101793481)
          ·
            refine ⟨31379673828494835076345111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41839565104659780101793481 31379673828494835076345111)
            ·
              refine ⟨47069510742742252614517667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31379673828494835076345111 47069510742742252614517667)
              ·
                refine ⟨70604266114113378921776501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47069510742742252614517667 70604266114113378921776501)
                ·
                  refine ⟨6619149948198129273916547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70604266114113378921776501 6619149948198129273916547)
                  ·
                    refine ⟨9928724922297193910874821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6619149948198129273916547 9928724922297193910874821)
                    ·
                      refine ⟨1861635922930723858289029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9928724922297193910874821 1861635922930723858289029)
                      ·
                        rfl

theorem cell23_3625523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_3625523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625523 prefixEnd_3625523 := by exact prefixLift 3625523
  have htrace : WordTrace (prefixWord ++ tailWord_3625523) baseStart_3625523 baseEnd_3625523 := by
    simpa [prefixWord, tailWord_3625523, baseEnd_3625523] using wordTrace_append hprefix tailTrace_3625523
  have hstable : (prefixWord ++ tailWord_3625523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625523).length < 2 ^ (prefixWord ++ tailWord_3625523).sum := by decide
  have hdescent : baseEnd_3625523 < baseStart_3625523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625557 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_3625557 : Nat := 118140960795 + 3625557 * 2 ^ 59
def prefixEnd_3625557 : Nat := 4983230072969 + 3 ^ 40 * 3625557 * 2
def baseEnd_3625557 : Nat := 1861653381272976725263873

theorem tailTrace_3625557 : CollatzResearch.WordTrace tailWord_3625557 prefixEnd_3625557 1861653381272976725263873 := by
  unfold tailWord_3625557
  simp only [CollatzResearch.WordTrace]
  refine ⟨132234927326233659684010925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88156618217489106456007283 132234927326233659684010925)
  ·
    refine ⟨49588097747337622381504097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132234927326233659684010925 49588097747337622381504097)
    ·
      refine ⟨37191073310503216786128073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49588097747337622381504097 37191073310503216786128073)
      ·
        refine ⟨27893304982877412589596055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37191073310503216786128073 27893304982877412589596055)
        ·
          refine ⟨41839957474316118884394083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27893304982877412589596055 41839957474316118884394083)
          ·
            refine ⟨62759936211474178326591125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41839957474316118884394083 62759936211474178326591125)
            ·
              refine ⟨2941872009912852109058959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62759936211474178326591125 2941872009912852109058959)
              ·
                refine ⟨4412808014869278163588439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941872009912852109058959 4412808014869278163588439)
                ·
                  refine ⟨6619212022303917245382659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4412808014869278163588439 6619212022303917245382659)
                  ·
                    refine ⟨9928818033455875868073989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6619212022303917245382659 9928818033455875868073989)
                    ·
                      refine ⟨1861653381272976725263873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9928818033455875868073989 1861653381272976725263873)
                      ·
                        rfl

theorem cell23_3625557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_3625557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625557 prefixEnd_3625557 := by exact prefixLift 3625557
  have htrace : WordTrace (prefixWord ++ tailWord_3625557) baseStart_3625557 baseEnd_3625557 := by
    simpa [prefixWord, tailWord_3625557, baseEnd_3625557] using wordTrace_append hprefix tailTrace_3625557
  have hstable : (prefixWord ++ tailWord_3625557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625557).length < 2 ^ (prefixWord ++ tailWord_3625557).sum := by decide
  have hdescent : baseEnd_3625557 < baseStart_3625557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625584 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 2, 4]
def baseStart_3625584 : Nat := 118140960795 + 3625584 * 2 ^ 59
def prefixEnd_3625584 : Nat := 4983230072969 + 3 ^ 40 * 3625584 * 2
def baseEnd_3625584 : Nat := 620555748416882706542083

theorem tailTrace_3625584 : CollatzResearch.WordTrace tailWord_3625584 prefixEnd_3625584 620555748416882706542083 := by
  unfold tailWord_3625584
  simp only [CollatzResearch.WordTrace]
  refine ⟨66117956048567921647621903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88157274731423895530162537 66117956048567921647621903)
  ·
    refine ⟨99176934072851882471432855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66117956048567921647621903 99176934072851882471432855)
    ·
      refine ⟨148765401109277823707149283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99176934072851882471432855 148765401109277823707149283)
      ·
        refine ⟨223148101663916735560723925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148765401109277823707149283 223148101663916735560723925)
        ·
          refine ⟨5230033632748048489704467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 223148101663916735560723925 5230033632748048489704467)
          ·
            refine ⟨7845050449122072734556701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230033632748048489704467 7845050449122072734556701)
            ·
              refine ⟨2941893918420777275458763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7845050449122072734556701 2941893918420777275458763)
              ·
                refine ⟨4412840877631165913188145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2941893918420777275458763 4412840877631165913188145)
                ·
                  refine ⟨3309630658223374434891109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4412840877631165913188145 3309630658223374434891109)
                  ·
                    refine ⟨620555748416882706542083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309630658223374434891109 620555748416882706542083)
                    ·
                      rfl

theorem cell23_3625584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 4].length) (baseStart_3625584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625584 prefixEnd_3625584 := by exact prefixLift 3625584
  have htrace : WordTrace (prefixWord ++ tailWord_3625584) baseStart_3625584 baseEnd_3625584 := by
    simpa [prefixWord, tailWord_3625584, baseEnd_3625584] using wordTrace_append hprefix tailTrace_3625584
  have hstable : (prefixWord ++ tailWord_3625584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625584).length < 2 ^ (prefixWord ++ tailWord_3625584).sum := by decide
  have hdescent : baseEnd_3625584 < baseStart_3625584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625597 : List Nat := [1, 4, 1, 1, 5, 2, 2, 7]
def baseStart_3625597 : Nat := 118140960795 + 3625597 * 2 ^ 59
def prefixEnd_3625597 : Nat := 4983230072969 + 3 ^ 40 * 3625597 * 2
def baseEnd_3625597 : Nat := 68950885944413206250507

theorem tailTrace_3625597 : CollatzResearch.WordTrace tailWord_3625597 prefixEnd_3625597 68950885944413206250507 := by
  unfold tailWord_3625597
  simp only [CollatzResearch.WordTrace]
  refine ⟨132236386246088746515467045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88157590830725831010311363 132236386246088746515467045)
  ·
    refine ⟨24794322421141639971650071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132236386246088746515467045 24794322421141639971650071)
    ·
      refine ⟨37191483631712459957475107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24794322421141639971650071 37191483631712459957475107)
      ·
        refine ⟨55787225447568689936212661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37191483631712459957475107 55787225447568689936212661)
        ·
          refine ⟨5230052385709564681519937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55787225447568689936212661 5230052385709564681519937)
          ·
            refine ⟨3922539289282173511139953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230052385709564681519937 3922539289282173511139953)
            ·
              refine ⟨2941904466961630133354965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922539289282173511139953 2941904466961630133354965)
              ·
                refine ⟨68950885944413206250507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2941904466961630133354965 68950885944413206250507)
                ·
                  rfl

theorem cell23_3625597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 7].length) (baseStart_3625597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625597 prefixEnd_3625597 := by exact prefixLift 3625597
  have htrace : WordTrace (prefixWord ++ tailWord_3625597) baseStart_3625597 baseEnd_3625597 := by
    simpa [prefixWord, tailWord_3625597, baseEnd_3625597] using wordTrace_append hprefix tailTrace_3625597
  have hstable : (prefixWord ++ tailWord_3625597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625597).length < 2 ^ (prefixWord ++ tailWord_3625597).sum := by decide
  have hdescent : baseEnd_3625597 < baseStart_3625597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625602 : List Nat := [3, 4, 3, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3625602 : Nat := 118140960795 + 3625602 * 2 ^ 59
def prefixEnd_3625602 : Nat := 4983230072969 + 3 ^ 40 * 3625602 * 2
def baseEnd_3625602 : Nat := 1861676487902429049201167

theorem tailTrace_3625602 : CollatzResearch.WordTrace tailWord_3625602 prefixEnd_3625602 1861676487902429049201167 := by
  unfold tailWord_3625602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33059142152767658092349765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88157712407380421579599373 33059142152767658092349765)
  ·
    refine ⟨6198589153643935892315581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33059142152767658092349765 6198589153643935892315581)
    ·
      refine ⟨2324470932616475959618343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6198589153643935892315581 2324470932616475959618343)
      ·
        refine ⟨3486706398924713939427515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324470932616475959618343 3486706398924713939427515)
        ·
          refine ⟨5230059598387070909141273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486706398924713939427515 5230059598387070909141273)
          ·
            refine ⟨3922544698790303181855955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230059598387070909141273 3922544698790303181855955)
            ·
              refine ⟨5883817048185454772783933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922544698790303181855955 5883817048185454772783933)
              ·
                refine ⟨2206431393069545539793975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5883817048185454772783933 2206431393069545539793975)
                ·
                  refine ⟨3309647089604318309690963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206431393069545539793975 3309647089604318309690963)
                  ·
                    refine ⟨4964470634406477464536445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3309647089604318309690963 4964470634406477464536445)
                    ·
                      refine ⟨1861676487902429049201167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4964470634406477464536445 1861676487902429049201167)
                      ·
                        rfl

theorem cell23_3625602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3625602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625602 prefixEnd_3625602 := by exact prefixLift 3625602
  have htrace : WordTrace (prefixWord ++ tailWord_3625602) baseStart_3625602 baseEnd_3625602 := by
    simpa [prefixWord, tailWord_3625602, baseEnd_3625602] using wordTrace_append hprefix tailTrace_3625602
  have hstable : (prefixWord ++ tailWord_3625602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625602).length < 2 ^ (prefixWord ++ tailWord_3625602).sum := by decide
  have hdescent : baseEnd_3625602 < baseStart_3625602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625603 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5]
def baseStart_3625603 : Nat := 118140960795 + 3625603 * 2 ^ 59
def prefixEnd_3625603 : Nat := 4983230072969 + 3 ^ 40 * 3625603 * 2
def baseEnd_3625603 : Nat := 1861677001383083545288661

theorem tailTrace_3625603 : CollatzResearch.WordTrace tailWord_3625603 prefixEnd_3625603 1861677001383083545288661 := by
  unfold tailWord_3625603
  simp only [CollatzResearch.WordTrace]
  refine ⟨132236605084067009540185463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88157736722711339693456975 132236605084067009540185463)
  ·
    refine ⟨198354907626100514310278195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132236605084067009540185463 198354907626100514310278195)
    ·
      refine ⟨297532361439150771465417293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198354907626100514310278195 297532361439150771465417293)
      ·
        refine ⟨111574635539681539299531485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297532361439150771465417293 111574635539681539299531485)
        ·
          refine ⟨41840488327380577237324307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111574635539681539299531485 41840488327380577237324307)
          ·
            refine ⟨62760732491070865855986461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41840488327380577237324307 62760732491070865855986461)
            ·
              refine ⟨23535274684151574695994923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62760732491070865855986461 23535274684151574695994923)
              ·
                refine ⟨35302912026227362043992385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23535274684151574695994923 35302912026227362043992385)
                ·
                  refine ⟨26477184019670521532994289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35302912026227362043992385 26477184019670521532994289)
                  ·
                    refine ⟨19857888014752891149745717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26477184019670521532994289 19857888014752891149745717)
                    ·
                      refine ⟨1861677001383083545288661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19857888014752891149745717 1861677001383083545288661)
                      ·
                        rfl

theorem cell23_3625603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_3625603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625603 prefixEnd_3625603 := by exact prefixLift 3625603
  have htrace : WordTrace (prefixWord ++ tailWord_3625603) baseStart_3625603 baseEnd_3625603 := by
    simpa [prefixWord, tailWord_3625603, baseEnd_3625603] using wordTrace_append hprefix tailTrace_3625603
  have hstable : (prefixWord ++ tailWord_3625603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625603).length < 2 ^ (prefixWord ++ tailWord_3625603).sum := by decide
  have hdescent : baseEnd_3625603 < baseStart_3625603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625687 : List Nat := [1, 1, 3, 2, 1, 5, 1, 4, 5]
def baseStart_3625687 : Nat := 118140960795 + 3625687 * 2 ^ 59
def prefixEnd_3625687 : Nat := 4983230072969 + 3 ^ 40 * 3625687 * 2
def baseEnd_3625687 : Nat := 206857792639784579626475

theorem tailTrace_3625687 : CollatzResearch.WordTrace tailWord_3625687 prefixEnd_3625687 206857792639784579626475 := by
  unfold tailWord_3625687
  simp only [CollatzResearch.WordTrace]
  refine ⟨132239668815762691886243315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88159779210508461257495543 132239668815762691886243315)
  ·
    refine ⟨198359503223644037829364973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132239668815762691886243315 198359503223644037829364973)
    ·
      refine ⟨74384813708866514186011865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198359503223644037829364973 74384813708866514186011865)
      ·
        refine ⟨55788610281649885639508899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74384813708866514186011865 55788610281649885639508899)
        ·
          refine ⟨83682915422474828459263349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55788610281649885639508899 83682915422474828459263349)
          ·
            refine ⟨7845273320857015168055939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83682915422474828459263349 7845273320857015168055939)
            ·
              refine ⟨11767909981285522752083909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845273320857015168055939 11767909981285522752083909)
              ·
                refine ⟨2206483121491035516015733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11767909981285522752083909 2206483121491035516015733)
                ·
                  refine ⟨206857792639784579626475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2206483121491035516015733 206857792639784579626475)
                  ·
                    rfl

theorem cell23_3625687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 5].length) (baseStart_3625687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625687 prefixEnd_3625687 := by exact prefixLift 3625687
  have htrace : WordTrace (prefixWord ++ tailWord_3625687) baseStart_3625687 baseEnd_3625687 := by
    simpa [prefixWord, tailWord_3625687, baseEnd_3625687] using wordTrace_append hprefix tailTrace_3625687
  have hstable : (prefixWord ++ tailWord_3625687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625687).length < 2 ^ (prefixWord ++ tailWord_3625687).sum := by decide
  have hdescent : baseEnd_3625687 < baseStart_3625687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625697 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3625697 : Nat := 118140960795 + 3625697 * 2 ^ 59
def prefixEnd_3625697 : Nat := 4983230072969 + 3 ^ 40 * 3625697 * 2
def baseEnd_3625697 : Nat := 1861725268564606177513229

theorem tailTrace_3625697 : CollatzResearch.WordTrace tailWord_3625697 prefixEnd_3625697 1861725268564606177513229 := by
  unfold tailWord_3625697
  simp only [CollatzResearch.WordTrace]
  refine ⟨132240033545726463594107345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88160022363817642396071563 132240033545726463594107345)
  ·
    refine ⟨99180025159294847695580509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132240033545726463594107345 99180025159294847695580509)
    ·
      refine ⟨37192509434735567885842691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99180025159294847695580509 37192509434735567885842691)
      ·
        refine ⟨55788764152103351828764037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37192509434735567885842691 55788764152103351828764037)
        ·
          refine ⟨10460393278519378467893257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55788764152103351828764037 10460393278519378467893257)
          ·
            refine ⟨7845294958889533850919943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10460393278519378467893257 7845294958889533850919943)
            ·
              refine ⟨11767942438334300776379915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845294958889533850919943 11767942438334300776379915)
              ·
                refine ⟨17651913657501451164569873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11767942438334300776379915 17651913657501451164569873)
                ·
                  refine ⟨13238935243126088373427405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17651913657501451164569873 13238935243126088373427405)
                  ·
                    refine ⟨4964600716172283140035277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13238935243126088373427405 4964600716172283140035277)
                    ·
                      refine ⟨1861725268564606177513229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4964600716172283140035277 1861725268564606177513229)
                      ·
                        rfl

theorem cell23_3625697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3625697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625697 prefixEnd_3625697 := by exact prefixLift 3625697
  have htrace : WordTrace (prefixWord ++ tailWord_3625697) baseStart_3625697 baseEnd_3625697 := by
    simpa [prefixWord, tailWord_3625697, baseEnd_3625697] using wordTrace_append hprefix tailTrace_3625697
  have hstable : (prefixWord ++ tailWord_3625697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625697).length < 2 ^ (prefixWord ++ tailWord_3625697).sum := by decide
  have hdescent : baseEnd_3625697 < baseStart_3625697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625720 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_3625720 : Nat := 118140960795 + 3625720 * 2 ^ 59
def prefixEnd_3625720 : Nat := 4983230072969 + 3 ^ 40 * 3625720 * 2
def baseEnd_3625720 : Nat := 1861737078619659587525623

theorem tailTrace_3625720 : CollatzResearch.WordTrace tailWord_3625720 prefixEnd_3625720 1861737078619659587525623 := by
  unfold tailWord_3625720
  simp only [CollatzResearch.WordTrace]
  refine ⟨66120436212321569261097307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88160581616428759014796409 66120436212321569261097307)
  ·
    refine ⟨99180654318482353891645961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66120436212321569261097307 99180654318482353891645961)
    ·
      refine ⟨74385490738861765418734471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99180654318482353891645961 74385490738861765418734471)
      ·
        refine ⟨111578236108292648128101707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74385490738861765418734471 111578236108292648128101707)
        ·
          refine ⟨167367354162438972192152561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111578236108292648128101707 167367354162438972192152561)
          ·
            refine ⟨125525515621829229144114421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167367354162438972192152561 125525515621829229144114421)
            ·
              refine ⟨11768017089546490232260727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125525515621829229144114421 11768017089546490232260727)
              ·
                refine ⟨17652025634319735348391091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768017089546490232260727 17652025634319735348391091)
                ·
                  refine ⟨26478038451479603022586637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17652025634319735348391091 26478038451479603022586637)
                  ·
                    refine ⟨9929264419304851133469989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26478038451479603022586637 9929264419304851133469989)
                    ·
                      refine ⟨1861737078619659587525623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9929264419304851133469989 1861737078619659587525623)
                      ·
                        rfl

theorem cell23_3625720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_3625720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625720 prefixEnd_3625720 := by exact prefixLift 3625720
  have htrace : WordTrace (prefixWord ++ tailWord_3625720) baseStart_3625720 baseEnd_3625720 := by
    simpa [prefixWord, tailWord_3625720, baseEnd_3625720] using wordTrace_append hprefix tailTrace_3625720
  have hstable : (prefixWord ++ tailWord_3625720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625720).length < 2 ^ (prefixWord ++ tailWord_3625720).sum := by decide
  have hdescent : baseEnd_3625720 < baseStart_3625720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625737 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 2, 4, 2]
def baseStart_3625737 : Nat := 118140960795 + 3625737 * 2 ^ 59
def prefixEnd_3625737 : Nat := 4983230072969 + 3 ^ 40 * 3625737 * 2
def baseEnd_3625737 : Nat := 1861745807790786021013045

theorem tailTrace_3625737 : CollatzResearch.WordTrace tailWord_3625737 prefixEnd_3625737 1861745807790786021013045 := by
  unfold tailWord_3625737
  simp only [CollatzResearch.WordTrace]
  refine ⟨132241492465581550425563465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88160994977054366950375643 132241492465581550425563465)
  ·
    refine ⟨99181119349186162819172599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132241492465581550425563465 99181119349186162819172599)
    ·
      refine ⟨148771679023779244228758899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99181119349186162819172599 148771679023779244228758899)
      ·
        refine ⟨223157518535668866343138349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148771679023779244228758899 223157518535668866343138349)
        ·
          refine ⟨83684069450875824878676881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223157518535668866343138349 83684069450875824878676881)
          ·
            refine ⟨62763052088156868659007661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83684069450875824878676881 62763052088156868659007661)
            ·
              refine ⟨23536144533058825747127873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62763052088156868659007661 23536144533058825747127873)
              ·
                refine ⟨17652108399794119310345905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23536144533058825747127873 17652108399794119310345905)
                ·
                  refine ⟨13239081299845589482759429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17652108399794119310345905 13239081299845589482759429)
                  ·
                    refine ⟨2482327743721048028017393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13239081299845589482759429 2482327743721048028017393)
                    ·
                      refine ⟨1861745807790786021013045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482327743721048028017393 1861745807790786021013045)
                      ·
                        rfl

theorem cell23_3625737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 4, 2].length) (baseStart_3625737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625737 prefixEnd_3625737 := by exact prefixLift 3625737
  have htrace : WordTrace (prefixWord ++ tailWord_3625737) baseStart_3625737 baseEnd_3625737 := by
    simpa [prefixWord, tailWord_3625737, baseEnd_3625737] using wordTrace_append hprefix tailTrace_3625737
  have hstable : (prefixWord ++ tailWord_3625737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625737).length < 2 ^ (prefixWord ++ tailWord_3625737).sum := by decide
  have hdescent : baseEnd_3625737 < baseStart_3625737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625747 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 3, 4]
def baseStart_3625747 : Nat := 118140960795 + 3625747 * 2 ^ 59
def prefixEnd_3625747 : Nat := 4983230072969 + 3 ^ 40 * 3625747 * 2
def baseEnd_3625747 : Nat := 620583647532443660629333

theorem tailTrace_3625747 : CollatzResearch.WordTrace tailWord_3625747 prefixEnd_3625747 620583647532443660629333 := by
  unfold tailWord_3625747
  simp only [CollatzResearch.WordTrace]
  refine ⟨132241857195545322133427495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88161238130363548088951663 132241857195545322133427495)
  ·
    refine ⟨198362785793317983200141243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132241857195545322133427495 198362785793317983200141243)
    ·
      refine ⟨297544178689976974800211865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198362785793317983200141243 297544178689976974800211865)
      ·
        refine ⟨223158134017482731100158899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297544178689976974800211865 223158134017482731100158899)
        ·
          refine ⟨334737201026224096650238349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223158134017482731100158899 334737201026224096650238349)
          ·
            refine ⟨125526450384834036243839381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334737201026224096650238349 125526450384834036243839381)
            ·
              refine ⟨5884052361789095448929971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 125526450384834036243839381 5884052361789095448929971)
              ·
                refine ⟨8826078542683643173394957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884052361789095448929971 8826078542683643173394957)
                ·
                  refine ⟨3309779453506366190023109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8826078542683643173394957 3309779453506366190023109)
                  ·
                    refine ⟨620583647532443660629333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309779453506366190023109 620583647532443660629333)
                    ·
                      rfl

theorem cell23_3625747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 4].length) (baseStart_3625747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625747 prefixEnd_3625747 := by exact prefixLift 3625747
  have htrace : WordTrace (prefixWord ++ tailWord_3625747) baseStart_3625747 baseEnd_3625747 := by
    simpa [prefixWord, tailWord_3625747, baseEnd_3625747] using wordTrace_append hprefix tailTrace_3625747
  have hstable : (prefixWord ++ tailWord_3625747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625747).length < 2 ^ (prefixWord ++ tailWord_3625747).sum := by decide
  have hdescent : baseEnd_3625747 < baseStart_3625747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625774 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3625774 : Nat := 118140960795 + 3625774 * 2 ^ 59
def prefixEnd_3625774 : Nat := 4983230072969 + 3 ^ 40 * 3625774 * 2
def baseEnd_3625774 : Nat := 1861764806575002376250375

theorem tailTrace_3625774 : CollatzResearch.WordTrace tailWord_3625774 prefixEnd_3625774 1861764806575002376250375 := by
  unfold tailWord_3625774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530355245805938218082547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88161894644298337163106917 16530355245805938218082547)
  ·
    refine ⟨24795532868708907327123821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16530355245805938218082547 24795532868708907327123821)
    ·
      refine ⟨9298324825765840247671433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24795532868708907327123821 9298324825765840247671433)
      ·
        refine ⟨6973743619324380185753575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9298324825765840247671433 6973743619324380185753575)
        ·
          refine ⟨10460615428986570278630363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6973743619324380185753575 10460615428986570278630363)
          ·
            refine ⟨15690923143479855417945545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10460615428986570278630363 15690923143479855417945545)
            ·
              refine ⟨11768192357609891563459159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15690923143479855417945545 11768192357609891563459159)
              ·
                refine ⟨17652288536414837345188739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768192357609891563459159 17652288536414837345188739)
                ·
                  refine ⟨26478432804622256017783109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17652288536414837345188739 26478432804622256017783109)
                  ·
                    refine ⟨4964706150866673003334333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26478432804622256017783109 4964706150866673003334333)
                    ·
                      refine ⟨1861764806575002376250375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4964706150866673003334333 1861764806575002376250375)
                      ·
                        rfl

theorem cell23_3625774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3625774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625774 prefixEnd_3625774 := by exact prefixLift 3625774
  have htrace : WordTrace (prefixWord ++ tailWord_3625774) baseStart_3625774 baseEnd_3625774 := by
    simpa [prefixWord, tailWord_3625774, baseEnd_3625774] using wordTrace_append hprefix tailTrace_3625774
  have hstable : (prefixWord ++ tailWord_3625774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625774).length < 2 ^ (prefixWord ++ tailWord_3625774).sum := by decide
  have hdescent : baseEnd_3625774 < baseStart_3625774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625781 : List Nat := [1, 3, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_3625781 : Nat := 118140960795 + 3625781 * 2 ^ 59
def prefixEnd_3625781 : Nat := 4983230072969 + 3 ^ 40 * 3625781 * 2
def baseEnd_3625781 : Nat := 620589466979861282954281

theorem tailTrace_3625781 : CollatzResearch.WordTrace tailWord_3625781 prefixEnd_3625781 620589466979861282954281 := by
  unfold tailWord_3625781
  simp only [CollatzResearch.WordTrace]
  refine ⟨132243097277422145940165197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88162064851614763960110131 132243097277422145940165197)
  ·
    refine ⟨49591161479033304727561949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132243097277422145940165197 49591161479033304727561949)
    ·
      refine ⟨18596685554637489272835731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49591161479033304727561949 18596685554637489272835731)
      ·
        refine ⟨27895028331956233909253597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18596685554637489272835731 27895028331956233909253597)
        ·
          refine ⟨10460635624483587715970099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27895028331956233909253597 10460635624483587715970099)
          ·
            refine ⟨15690953436725381573955149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10460635624483587715970099 15690953436725381573955149)
            ·
              refine ⟨5884107538772018090233181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15690953436725381573955149 5884107538772018090233181)
              ·
                refine ⟨2206540327039506783837443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5884107538772018090233181 2206540327039506783837443)
                ·
                  refine ⟨3309810490559260175756165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206540327039506783837443 3309810490559260175756165)
                  ·
                    refine ⟨620589466979861282954281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3309810490559260175756165 620589466979861282954281)
                    ·
                      rfl

theorem cell23_3625781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_3625781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625781 prefixEnd_3625781 := by exact prefixLift 3625781
  have htrace : WordTrace (prefixWord ++ tailWord_3625781) baseStart_3625781 baseEnd_3625781 := by
    simpa [prefixWord, tailWord_3625781, baseEnd_3625781] using wordTrace_append hprefix tailTrace_3625781
  have hstable : (prefixWord ++ tailWord_3625781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625781).length < 2 ^ (prefixWord ++ tailWord_3625781).sum := by decide
  have hdescent : baseEnd_3625781 < baseStart_3625781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625797 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 3, 5, 2]
def baseStart_3625797 : Nat := 118140960795 + 3625797 * 2 ^ 59
def prefixEnd_3625797 : Nat := 4983230072969 + 3 ^ 40 * 3625797 * 2
def baseEnd_3625797 : Nat := 1861776616630055786262769

theorem tailTrace_3625797 : CollatzResearch.WordTrace tailWord_3625797 prefixEnd_3625797 1861776616630055786262769 := by
  unfold tailWord_3625797
  simp only [CollatzResearch.WordTrace]
  refine ⟨132243680845364180672747645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88162453896909453781831763 132243680845364180672747645)
  ·
    refine ⟨49591380317011567752280367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132243680845364180672747645 49591380317011567752280367)
    ·
      refine ⟨74387070475517351628420551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49591380317011567752280367 74387070475517351628420551)
      ·
        refine ⟨111580605713276027442630827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74387070475517351628420551 111580605713276027442630827)
        ·
          refine ⟨167370908569914041163946241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111580605713276027442630827 167370908569914041163946241)
          ·
            refine ⟨125528181427435530872959681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167370908569914041163946241 125528181427435530872959681)
            ·
              refine ⟨94146136070576648154719761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125528181427435530872959681 94146136070576648154719761)
              ·
                refine ⟨70609602052932486116039821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94146136070576648154719761 70609602052932486116039821)
                ·
                  refine ⟨26478600769849682293514933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70609602052932486116039821 26478600769849682293514933)
                  ·
                    refine ⟨2482368822173407715017025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26478600769849682293514933 2482368822173407715017025)
                    ·
                      refine ⟨1861776616630055786262769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482368822173407715017025 1861776616630055786262769)
                      ·
                        rfl

theorem cell23_3625797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_3625797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625797 prefixEnd_3625797 := by exact prefixLift 3625797
  have htrace : WordTrace (prefixWord ++ tailWord_3625797) baseStart_3625797 baseEnd_3625797 := by
    simpa [prefixWord, tailWord_3625797, baseEnd_3625797] using wordTrace_append hprefix tailTrace_3625797
  have hstable : (prefixWord ++ tailWord_3625797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625797).length < 2 ^ (prefixWord ++ tailWord_3625797).sum := by decide
  have hdescent : baseEnd_3625797 < baseStart_3625797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625831 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_3625831 : Nat := 118140960795 + 3625831 * 2 ^ 59
def prefixEnd_3625831 : Nat := 4983230072969 + 3 ^ 40 * 3625831 * 2
def baseEnd_3625831 : Nat := 1861794074972308653237613

theorem tailTrace_3625831 : CollatzResearch.WordTrace tailWord_3625831 prefixEnd_3625831 1861794074972308653237613 := by
  unfold tailWord_3625831
  simp only [CollatzResearch.WordTrace]
  refine ⟨132244920927241004479485347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88163280618160669652990231 132244920927241004479485347)
  ·
    refine ⟨198367381390861506719228021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132244920927241004479485347 198367381390861506719228021)
    ·
      refine ⟨18596942005393266254927627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198367381390861506719228021 18596942005393266254927627)
      ·
        refine ⟨27895413008089899382391441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18596942005393266254927627 27895413008089899382391441)
        ·
          refine ⟨20921559756067424536793581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27895413008089899382391441 20921559756067424536793581)
          ·
            refine ⟨7845584908525284201297593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20921559756067424536793581 7845584908525284201297593)
            ·
              refine ⟨5884188681393963150973195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7845584908525284201297593 5884188681393963150973195)
              ·
                refine ⟨8826283022090944726459793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884188681393963150973195 8826283022090944726459793)
                ·
                  refine ⟨6619712266568208544844845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8826283022090944726459793 6619712266568208544844845)
                  ·
                    refine ⟨2482392099963078204316817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6619712266568208544844845 2482392099963078204316817)
                    ·
                      refine ⟨1861794074972308653237613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482392099963078204316817 1861794074972308653237613)
                      ·
                        rfl

theorem cell23_3625831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_3625831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625831 prefixEnd_3625831 := by exact prefixLift 3625831
  have htrace : WordTrace (prefixWord ++ tailWord_3625831) baseStart_3625831 baseEnd_3625831 := by
    simpa [prefixWord, tailWord_3625831, baseEnd_3625831] using wordTrace_append hprefix tailTrace_3625831
  have hstable : (prefixWord ++ tailWord_3625831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625831).length < 2 ^ (prefixWord ++ tailWord_3625831).sum := by decide
  have hdescent : baseEnd_3625831 < baseStart_3625831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625864 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3625864 : Nat := 118140960795 + 3625864 * 2 ^ 59
def prefixEnd_3625864 : Nat := 4983230072969 + 3 ^ 40 * 3625864 * 2
def baseEnd_3625864 : Nat := 1861811019833907024124961

theorem tailTrace_3625864 : CollatzResearch.WordTrace tailWord_3625864 prefixEnd_3625864 1861811019833907024124961 := by
  unfold tailWord_3625864
  simp only [CollatzResearch.WordTrace]
  refine ⟨66123062268060725557718323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88164083024080967410291097 66123062268060725557718323)
  ·
    refine ⟨99184593402091088336577485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66123062268060725557718323 99184593402091088336577485)
    ·
      refine ⟨37194222525784158126216557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99184593402091088336577485 37194222525784158126216557)
      ·
        refine ⟨13947833447169059297331209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37194222525784158126216557 13947833447169059297331209)
        ·
          refine ⟨10460875085376794472998407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13947833447169059297331209 10460875085376794472998407)
          ·
            refine ⟨15691312628065191709497611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10460875085376794472998407 15691312628065191709497611)
            ·
              refine ⟨23536968942097787564246417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15691312628065191709497611 23536968942097787564246417)
              ·
                refine ⟨17652726706573340673184813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23536968942097787564246417 17652726706573340673184813)
                ·
                  refine ⟨6619772514965002752444305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17652726706573340673184813 6619772514965002752444305)
                  ·
                    refine ⟨4964829386223752064333229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6619772514965002752444305 4964829386223752064333229)
                    ·
                      refine ⟨1861811019833907024124961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4964829386223752064333229 1861811019833907024124961)
                      ·
                        rfl

theorem cell23_3625864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3625864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625864 prefixEnd_3625864 := by exact prefixLift 3625864
  have htrace : WordTrace (prefixWord ++ tailWord_3625864) baseStart_3625864 baseEnd_3625864 := by
    simpa [prefixWord, tailWord_3625864, baseEnd_3625864] using wordTrace_append hprefix tailTrace_3625864
  have hstable : (prefixWord ++ tailWord_3625864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625864).length < 2 ^ (prefixWord ++ tailWord_3625864).sum := by decide
  have hdescent : baseEnd_3625864 < baseStart_3625864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625878 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3625878 : Nat := 118140960795 + 3625878 * 2 ^ 59
def prefixEnd_3625878 : Nat := 4983230072969 + 3 ^ 40 * 3625878 * 2
def baseEnd_3625878 : Nat := 1861818208563069969349897

theorem tailTrace_3625878 : CollatzResearch.WordTrace tailWord_3625878 prefixEnd_3625878 1861818208563069969349897 := by
  unfold tailWord_3625878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265414697379420719152893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88164423438713821004297525 8265414697379420719152893)
  ·
    refine ⟨3099530511517282769682335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8265414697379420719152893 3099530511517282769682335)
    ·
      refine ⟨4649295767275924154523503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099530511517282769682335 4649295767275924154523503)
      ·
        refine ⟨6973943650913886231785255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649295767275924154523503 6973943650913886231785255)
        ·
          refine ⟨10460915476370829347677883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6973943650913886231785255 10460915476370829347677883)
          ·
            refine ⟨15691373214556244021516825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10460915476370829347677883 15691373214556244021516825)
            ·
              refine ⟨11768529910917183016137619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15691373214556244021516825 11768529910917183016137619)
              ·
                refine ⟨17652794866375774524206429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768529910917183016137619 17652794866375774524206429)
                ·
                  refine ⟨6619798074890915446577411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17652794866375774524206429 6619798074890915446577411)
                  ·
                    refine ⟨9929697112336373169866117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6619798074890915446577411 9929697112336373169866117)
                    ·
                      refine ⟨1861818208563069969349897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9929697112336373169866117 1861818208563069969349897)
                      ·
                        rfl

theorem cell23_3625878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3625878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625878 prefixEnd_3625878 := by exact prefixLift 3625878
  have htrace : WordTrace (prefixWord ++ tailWord_3625878) baseStart_3625878 baseEnd_3625878 := by
    simpa [prefixWord, tailWord_3625878, baseEnd_3625878] using wordTrace_append hprefix tailTrace_3625878
  have hstable : (prefixWord ++ tailWord_3625878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625878).length < 2 ^ (prefixWord ++ tailWord_3625878).sum := by decide
  have hdescent : baseEnd_3625878 < baseStart_3625878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625895 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_3625895 : Nat := 118140960795 + 3625895 * 2 ^ 59
def prefixEnd_3625895 : Nat := 4983230072969 + 3 ^ 40 * 3625895 * 2
def baseEnd_3625895 : Nat := 1861826937734196402837319

theorem tailTrace_3625895 : CollatzResearch.WordTrace tailWord_3625895 prefixEnd_3625895 1861826937734196402837319 := by
  unfold tailWord_3625895
  simp only [CollatzResearch.WordTrace]
  refine ⟨132247255199009143409815139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88164836799339428939876759 132247255199009143409815139)
  ·
    refine ⟨198370882798513715114722709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132247255199009143409815139 198370882798513715114722709)
    ·
      refine ⟨9298635131180330396002627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198370882798513715114722709 9298635131180330396002627)
      ·
        refine ⟨13947952696770495594003941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9298635131180330396002627 13947952696770495594003941)
        ·
          refine ⟨2615241130644467923875739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13947952696770495594003941 2615241130644467923875739)
          ·
            refine ⟨3922861695966701885813609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615241130644467923875739 3922861695966701885813609)
            ·
              refine ⟨2942146271975026414360207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922861695966701885813609 2942146271975026414360207)
              ·
                refine ⟨4413219407962539621540311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942146271975026414360207 4413219407962539621540311)
                ·
                  refine ⟨6619829111943809432310467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413219407962539621540311 6619829111943809432310467)
                  ·
                    refine ⟨9929743667915714148465701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6619829111943809432310467 9929743667915714148465701)
                    ·
                      refine ⟨1861826937734196402837319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9929743667915714148465701 1861826937734196402837319)
                      ·
                        rfl

theorem cell23_3625895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_3625895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625895 prefixEnd_3625895 := by exact prefixLift 3625895
  have htrace : WordTrace (prefixWord ++ tailWord_3625895) baseStart_3625895 baseEnd_3625895 := by
    simpa [prefixWord, tailWord_3625895, baseEnd_3625895] using wordTrace_append hprefix tailTrace_3625895
  have hstable : (prefixWord ++ tailWord_3625895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625895).length < 2 ^ (prefixWord ++ tailWord_3625895).sum := by decide
  have hdescent : baseEnd_3625895 < baseStart_3625895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625911 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_3625911 : Nat := 118140960795 + 3625911 * 2 ^ 59
def prefixEnd_3625911 : Nat := 4983230072969 + 3 ^ 40 * 3625911 * 2
def baseEnd_3625911 : Nat := 1861835153424668340237245

theorem tailTrace_3625911 : CollatzResearch.WordTrace tailWord_3625911 prefixEnd_3625911 1861835153424668340237245 := by
  unfold tailWord_3625911
  simp only [CollatzResearch.WordTrace]
  refine ⟨132247838766951178142397587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88165225844634118761598391 132247838766951178142397587)
  ·
    refine ⟨198371758150426767213596381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132247838766951178142397587 198371758150426767213596381)
    ·
      refine ⟨74389409306410037705098643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198371758150426767213596381 74389409306410037705098643)
      ·
        refine ⟨111584113959615056557647965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74389409306410037705098643 111584113959615056557647965)
        ·
          refine ⟨41844042734855646209117987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111584113959615056557647965 41844042734855646209117987)
          ·
            refine ⟨62766064102283469313676981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41844042734855646209117987 62766064102283469313676981)
            ·
              refine ⟨5884318509589075248157217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62766064102283469313676981 5884318509589075248157217)
              ·
                refine ⟨4413238882191806436117913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5884318509589075248157217 4413238882191806436117913)
                ·
                  refine ⟨3309929161643854827088435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4413238882191806436117913 3309929161643854827088435)
                  ·
                    refine ⟨4964893742465782240632653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3309929161643854827088435 4964893742465782240632653)
                    ·
                      refine ⟨1861835153424668340237245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4964893742465782240632653 1861835153424668340237245)
                      ·
                        rfl

theorem cell23_3625911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_3625911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625911 prefixEnd_3625911 := by exact prefixLift 3625911
  have htrace : WordTrace (prefixWord ++ tailWord_3625911) baseStart_3625911 baseEnd_3625911 := by
    simpa [prefixWord, tailWord_3625911, baseEnd_3625911] using wordTrace_append hprefix tailTrace_3625911
  have hstable : (prefixWord ++ tailWord_3625911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625911).length < 2 ^ (prefixWord ++ tailWord_3625911).sum := by decide
  have hdescent : baseEnd_3625911 < baseStart_3625911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625927 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 2, 6]
def baseStart_3625927 : Nat := 118140960795 + 3625927 * 2 ^ 59
def prefixEnd_3625927 : Nat := 4983230072969 + 3 ^ 40 * 3625927 * 2
def baseEnd_3625927 : Nat := 620614456371713425879057

theorem tailTrace_3625927 : CollatzResearch.WordTrace tailWord_3625927 prefixEnd_3625927 620614456371713425879057 := by
  unfold tailWord_3625927
  simp only [CollatzResearch.WordTrace]
  refine ⟨132248422334893212874980035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88165614889928808583320023 132248422334893212874980035)
  ·
    refine ⟨198372633502339819312470053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132248422334893212874980035 198372633502339819312470053)
    ·
      refine ⟨37194868781688716121088135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198372633502339819312470053 37194868781688716121088135)
      ·
        refine ⟨55792303172533074181632203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37194868781688716121088135 55792303172533074181632203)
        ·
          refine ⟨83688454758799611272448305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55792303172533074181632203 83688454758799611272448305)
          ·
            refine ⟨62766341069099708454336229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83688454758799611272448305 62766341069099708454336229)
            ·
              refine ⟨11768688950456195335188043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62766341069099708454336229 11768688950456195335188043)
              ·
                refine ⟨17653033425684293002782065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11768688950456195335188043 17653033425684293002782065)
                ·
                  refine ⟨13239775069263219752086549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17653033425684293002782065 13239775069263219752086549)
                  ·
                    refine ⟨620614456371713425879057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13239775069263219752086549 620614456371713425879057)
                    ·
                      rfl

theorem cell23_3625927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_3625927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625927 prefixEnd_3625927 := by exact prefixLift 3625927
  have htrace : WordTrace (prefixWord ++ tailWord_3625927) baseStart_3625927 baseEnd_3625927 := by
    simpa [prefixWord, tailWord_3625927, baseEnd_3625927] using wordTrace_append hprefix tailTrace_3625927
  have hstable : (prefixWord ++ tailWord_3625927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625927).length < 2 ^ (prefixWord ++ tailWord_3625927).sum := by decide
  have hdescent : baseEnd_3625927 < baseStart_3625927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625928 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 1, 3, 3]
def baseStart_3625928 : Nat := 118140960795 + 3625928 * 2 ^ 59
def prefixEnd_3625928 : Nat := 4983230072969 + 3 ^ 40 * 3625928 * 2
def baseEnd_3625928 : Nat := 1861843882595794773724667

theorem tailTrace_3625928 : CollatzResearch.WordTrace tailWord_3625928 prefixEnd_3625928 1861843882595794773724667 := by
  unfold tailWord_3625928
  simp only [CollatzResearch.WordTrace]
  refine ⟨66124229403944795022883219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88165639205259726697177625 66124229403944795022883219)
  ·
    refine ⟨99186344105917192534324829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66124229403944795022883219 99186344105917192534324829)
    ·
      refine ⟨37194879039718947200371811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99186344105917192534324829 37194879039718947200371811)
      ·
        refine ⟨55792318559578420800557717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37194879039718947200371811 55792318559578420800557717)
        ·
          refine ⟨2615264932480238475026143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55792318559578420800557717 2615264932480238475026143)
          ·
            refine ⟨3922897398720357712539215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615264932480238475026143 3922897398720357712539215)
            ·
              refine ⟨5884346098080536568808823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922897398720357712539215 5884346098080536568808823)
              ·
                refine ⟨8826519147120804853213235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884346098080536568808823 8826519147120804853213235)
                ·
                  refine ⟨13239778720681207279819853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8826519147120804853213235 13239778720681207279819853)
                  ·
                    refine ⟨4964917020255452729932445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13239778720681207279819853 4964917020255452729932445)
                    ·
                      refine ⟨1861843882595794773724667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4964917020255452729932445 1861843882595794773724667)
                      ·
                        rfl

theorem cell23_3625928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_3625928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625928 prefixEnd_3625928 := by exact prefixLift 3625928
  have htrace : WordTrace (prefixWord ++ tailWord_3625928) baseStart_3625928 baseEnd_3625928 := by
    simpa [prefixWord, tailWord_3625928, baseEnd_3625928] using wordTrace_append hprefix tailTrace_3625928
  have hstable : (prefixWord ++ tailWord_3625928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625928).length < 2 ^ (prefixWord ++ tailWord_3625928).sum := by decide
  have hdescent : baseEnd_3625928 < baseStart_3625928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625937 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_3625937 : Nat := 118140960795 + 3625937 * 2 ^ 59
def prefixEnd_3625937 : Nat := 4983230072969 + 3 ^ 40 * 3625937 * 2
def baseEnd_3625937 : Nat := 1861848503921685238512125

theorem tailTrace_3625937 : CollatzResearch.WordTrace tailWord_3625937 prefixEnd_3625937 1861848503921685238512125 := by
  unfold tailWord_3625937
  simp only [CollatzResearch.WordTrace]
  refine ⟨132248787064856984582844065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88165858043237989721896043 132248787064856984582844065)
  ·
    refine ⟨99186590298642738437133049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132248787064856984582844065 99186590298642738437133049)
    ·
      refine ⟨74389942723982053827849787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99186590298642738437133049 74389942723982053827849787)
      ·
        refine ⟨111584914085973080741774681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74389942723982053827849787 111584914085973080741774681)
        ·
          refine ⟨83688685564479810556331011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111584914085973080741774681 83688685564479810556331011)
          ·
            refine ⟨125533028346719715834496517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83688685564479810556331011 125533028346719715834496517)
            ·
              refine ⟨23537442815009946718968097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125533028346719715834496517 23537442815009946718968097)
              ·
                refine ⟨17653082111257460039226073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23537442815009946718968097 17653082111257460039226073)
                ·
                  refine ⟨13239811583443095029419555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17653082111257460039226073 13239811583443095029419555)
                  ·
                    refine ⟨19859717375164642544129333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13239811583443095029419555 19859717375164642544129333)
                    ·
                      refine ⟨1861848503921685238512125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19859717375164642544129333 1861848503921685238512125)
                      ·
                        rfl

theorem cell23_3625937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_3625937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625937 prefixEnd_3625937 := by exact prefixLift 3625937
  have htrace : WordTrace (prefixWord ++ tailWord_3625937) baseStart_3625937 baseEnd_3625937 := by
    simpa [prefixWord, tailWord_3625937, baseEnd_3625937] using wordTrace_append hprefix tailTrace_3625937
  have hstable : (prefixWord ++ tailWord_3625937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625937).length < 2 ^ (prefixWord ++ tailWord_3625937).sum := by decide
  have hdescent : baseEnd_3625937 < baseStart_3625937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625938 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3625938 : Nat := 118140960795 + 3625938 * 2 ^ 59
def prefixEnd_3625938 : Nat := 4983230072969 + 3 ^ 40 * 3625938 * 2
def baseEnd_3625938 : Nat := 1861849017402339734599621

theorem tailTrace_3625938 : CollatzResearch.WordTrace tailWord_3625938 prefixEnd_3625938 1861849017402339734599621 := by
  unfold tailWord_3625938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33062205884463340438407617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88165882358568907835753645 33062205884463340438407617)
  ·
    refine ⟨24796654413347505328805713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33062205884463340438407617 24796654413347505328805713)
    ·
      refine ⟨18597490810010628996604285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24796654413347505328805713 18597490810010628996604285)
      ·
        refine ⟨6974059053753985873726607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18597490810010628996604285 6974059053753985873726607)
        ·
          refine ⟨10461088580630978810589911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974059053753985873726607 10461088580630978810589911)
          ·
            refine ⟨15691632870946468215884867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461088580630978810589911 15691632870946468215884867)
            ·
              refine ⟨23537449306419702323827301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15691632870946468215884867 23537449306419702323827301)
              ·
                refine ⟨4413271744953694185717619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23537449306419702323827301 4413271744953694185717619)
                ·
                  refine ⟨6619907617430541278576429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413271744953694185717619 6619907617430541278576429)
                  ·
                    refine ⟨2482465356536452979466161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6619907617430541278576429 2482465356536452979466161)
                    ·
                      refine ⟨1861849017402339734599621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482465356536452979466161 1861849017402339734599621)
                      ·
                        rfl

theorem cell23_3625938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3625938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625938 prefixEnd_3625938 := by exact prefixLift 3625938
  have htrace : WordTrace (prefixWord ++ tailWord_3625938) baseStart_3625938 baseEnd_3625938 := by
    simpa [prefixWord, tailWord_3625938, baseEnd_3625938] using wordTrace_append hprefix tailTrace_3625938
  have hstable : (prefixWord ++ tailWord_3625938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625938).length < 2 ^ (prefixWord ++ tailWord_3625938).sum := by decide
  have hdescent : baseEnd_3625938 < baseStart_3625938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3625985 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_3625985 : Nat := 118140960795 + 3625985 * 2 ^ 59
def prefixEnd_3625985 : Nat := 4983230072969 + 3 ^ 40 * 3625985 * 2
def baseEnd_3625985 : Nat := 1861873150993101050711905

theorem tailTrace_3625985 : CollatzResearch.WordTrace tailWord_3625985 prefixEnd_3625985 1861873150993101050711905 := by
  unfold tailWord_3625985
  simp only [CollatzResearch.WordTrace]
  refine ⟨132250537768683088780591409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88167025179122059187060939 132250537768683088780591409)
  ·
    refine ⟨99187903326512316585443557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132250537768683088780591409 99187903326512316585443557)
    ·
      refine ⟨18597731873721059359770667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99187903326512316585443557 18597731873721059359770667)
      ·
        refine ⟨27896597810581589039656001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18597731873721059359770667 27896597810581589039656001)
        ·
          refine ⟨20922448357936191779742001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27896597810581589039656001 20922448357936191779742001)
          ·
            refine ⟨15691836268452143834806501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20922448357936191779742001 15691836268452143834806501)
            ·
              refine ⟨2942219300334776969026219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15691836268452143834806501 2942219300334776969026219)
              ·
                refine ⟨4413328950502165453539329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942219300334776969026219 4413328950502165453539329)
                ·
                  refine ⟨3309996712876624090154497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4413328950502165453539329 3309996712876624090154497)
                  ·
                    refine ⟨2482497534657468067615873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3309996712876624090154497 2482497534657468067615873)
                    ·
                      refine ⟨1861873150993101050711905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482497534657468067615873 1861873150993101050711905)
                      ·
                        rfl

theorem cell23_3625985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_3625985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3625985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3625985 prefixEnd_3625985 := by exact prefixLift 3625985
  have htrace : WordTrace (prefixWord ++ tailWord_3625985) baseStart_3625985 baseEnd_3625985 := by
    simpa [prefixWord, tailWord_3625985, baseEnd_3625985] using wordTrace_append hprefix tailTrace_3625985
  have hstable : (prefixWord ++ tailWord_3625985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3625985).length < 2 ^ (prefixWord ++ tailWord_3625985).sum := by decide
  have hdescent : baseEnd_3625985 < baseStart_3625985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3625985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626002 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3626002 : Nat := 118140960795 + 3626002 * 2 ^ 59
def prefixEnd_3626002 : Nat := 4983230072969 + 3 ^ 40 * 3626002 * 2
def baseEnd_3626002 : Nat := 1861881880164227484199327

theorem tailTrace_3626002 : CollatzResearch.WordTrace tailWord_3626002 prefixEnd_3626002 1861881880164227484199327 := by
  unfold tailWord_3626002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33062789452405375170990065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88167438539747667122640173 33062789452405375170990065)
  ·
    refine ⟨24797092089304031378242549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33062789452405375170990065 24797092089304031378242549)
    ·
      refine ⟨2324727383372252941710239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24797092089304031378242549 2324727383372252941710239)
      ·
        refine ⟨3487091075058379412565359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324727383372252941710239 3487091075058379412565359)
        ·
          refine ⟨5230636612587569118848039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487091075058379412565359 5230636612587569118848039)
          ·
            refine ⟨7845954918881353678272059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230636612587569118848039 7845954918881353678272059)
            ·
              refine ⟨11768932378322030517408089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7845954918881353678272059 11768932378322030517408089)
              ·
                refine ⟨8826699283741522888056067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11768932378322030517408089 8826699283741522888056067)
                ·
                  refine ⟨13240048925612284332084101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8826699283741522888056067 13240048925612284332084101)
                  ·
                    refine ⟨2482509173552303312265769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13240048925612284332084101 2482509173552303312265769)
                    ·
                      refine ⟨1861881880164227484199327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482509173552303312265769 1861881880164227484199327)
                      ·
                        rfl

theorem cell23_3626002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3626002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626002 prefixEnd_3626002 := by exact prefixLift 3626002
  have htrace : WordTrace (prefixWord ++ tailWord_3626002) baseStart_3626002 baseEnd_3626002 := by
    simpa [prefixWord, tailWord_3626002, baseEnd_3626002] using wordTrace_append hprefix tailTrace_3626002
  have hstable : (prefixWord ++ tailWord_3626002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626002).length < 2 ^ (prefixWord ++ tailWord_3626002).sum := by decide
  have hdescent : baseEnd_3626002 < baseStart_3626002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626027 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5]
def baseStart_3626027 : Nat := 118140960795 + 3626027 * 2 ^ 59
def prefixEnd_3626027 : Nat := 4983230072969 + 3 ^ 40 * 3626027 * 2
def baseEnd_3626027 : Nat := 1861894717180589886386711

theorem tailTrace_3626027 : CollatzResearch.WordTrace tailWord_3626027 prefixEnd_3626027 1861894717180589886386711 := by
  unfold tailWord_3626027
  simp only [CollatzResearch.WordTrace]
  refine ⟨132252069634530929953620335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88168046423020619969080223 132252069634530929953620335)
  ·
    refine ⟨198378104451796394930430503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132252069634530929953620335 198378104451796394930430503)
    ·
      refine ⟨297567156677694592395645755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198378104451796394930430503 297567156677694592395645755)
      ·
        refine ⟨446350735016541888593468633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297567156677694592395645755 446350735016541888593468633)
        ·
          refine ⟨334763051262406416445101475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446350735016541888593468633 334763051262406416445101475)
          ·
            refine ⟨502144576893609624667652213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334763051262406416445101475 502144576893609624667652213)
            ·
              refine ⟨47076054083775902312592395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 502144576893609624667652213 47076054083775902312592395)
              ·
                refine ⟨70614081125663853468888593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47076054083775902312592395 70614081125663853468888593)
                ·
                  refine ⟨52960560844247890101666445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70614081125663853468888593 52960560844247890101666445)
                  ·
                    refine ⟨19860210316592958788124917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52960560844247890101666445 19860210316592958788124917)
                    ·
                      refine ⟨1861894717180589886386711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19860210316592958788124917 1861894717180589886386711)
                      ·
                        rfl

theorem cell23_3626027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 5].length) (baseStart_3626027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626027 prefixEnd_3626027 := by exact prefixLift 3626027
  have htrace : WordTrace (prefixWord ++ tailWord_3626027) baseStart_3626027 baseEnd_3626027 := by
    simpa [prefixWord, tailWord_3626027, baseEnd_3626027] using wordTrace_append hprefix tailTrace_3626027
  have hstable : (prefixWord ++ tailWord_3626027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626027).length < 2 ^ (prefixWord ++ tailWord_3626027).sum := by decide
  have hdescent : baseEnd_3626027 < baseStart_3626027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626041 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 1, 6, 2]
def baseStart_3626041 : Nat := 118140960795 + 3626041 * 2 ^ 59
def prefixEnd_3626041 : Nat := 4983230072969 + 3 ^ 40 * 3626041 * 2
def baseEnd_3626041 : Nat := 1861901905909752831611647

theorem tailTrace_3626041 : CollatzResearch.WordTrace tailWord_3626041 prefixEnd_3626041 1861901905909752831611647 := by
  unfold tailWord_3626041
  simp only [CollatzResearch.WordTrace]
  refine ⟨132252580256480210344629977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88168386837653473563086651 132252580256480210344629977)
  ·
    refine ⟨99189435192360157758472483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132252580256480210344629977 99189435192360157758472483)
    ·
      refine ⟨148784152788540236637708725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99189435192360157758472483 148784152788540236637708725)
      ·
        refine ⟨13948514323925647184785193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148784152788540236637708725 13948514323925647184785193)
        ·
          refine ⟨10461385742944235388588895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13948514323925647184785193 10461385742944235388588895)
          ·
            refine ⟨15692078614416353082883343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461385742944235388588895 15692078614416353082883343)
            ·
              refine ⟨23538117921624529624325015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15692078614416353082883343 23538117921624529624325015)
              ·
                refine ⟨35307176882436794436487523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23538117921624529624325015 35307176882436794436487523)
                ·
                  refine ⟨52960765323655191654731285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35307176882436794436487523 52960765323655191654731285)
                  ·
                    refine ⟨2482535874546337108815529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52960765323655191654731285 2482535874546337108815529)
                    ·
                      refine ⟨1861901905909752831611647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482535874546337108815529 1861901905909752831611647)
                      ·
                        rfl

theorem cell23_3626041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_3626041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626041 prefixEnd_3626041 := by exact prefixLift 3626041
  have htrace : WordTrace (prefixWord ++ tailWord_3626041) baseStart_3626041 baseEnd_3626041 := by
    simpa [prefixWord, tailWord_3626041, baseEnd_3626041] using wordTrace_append hprefix tailTrace_3626041
  have hstable : (prefixWord ++ tailWord_3626041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626041).length < 2 ^ (prefixWord ++ tailWord_3626041).sum := by decide
  have hdescent : baseEnd_3626041 < baseStart_3626041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626047 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 10]
def baseStart_3626047 : Nat := 118140960795 + 3626047 * 2 ^ 59
def prefixEnd_3626047 : Nat := 4983230072969 + 3 ^ 40 * 3626047 * 2
def baseEnd_3626047 : Nat := 206878331865964423126291

theorem tailTrace_3626047 : CollatzResearch.WordTrace tailWord_3626047 prefixEnd_3626047 206878331865964423126291 := by
  unfold tailWord_3626047
  simp only [CollatzResearch.WordTrace]
  refine ⟨132252799094458473369348395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88168532729638982246232263 132252799094458473369348395)
  ·
    refine ⟨198379198641687710054022593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132252799094458473369348395 198379198641687710054022593)
    ·
      refine ⟨148784398981265782540516945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198379198641687710054022593 148784398981265782540516945)
      ·
        refine ⟨111588299235949336905387709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148784398981265782540516945 111588299235949336905387709)
        ·
          refine ⟨41845612213481001339520391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111588299235949336905387709 41845612213481001339520391)
          ·
            refine ⟨62768418320221502009280587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41845612213481001339520391 62768418320221502009280587)
            ·
              refine ⟨94152627480332253013920881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62768418320221502009280587 94152627480332253013920881)
              ·
                refine ⟨70614470610249189760440661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94152627480332253013920881 70614470610249189760440661)
                ·
                  refine ⟨206878331865964423126291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70614470610249189760440661 206878331865964423126291)
                  ·
                    rfl

theorem cell23_3626047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 10].length) (baseStart_3626047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626047 prefixEnd_3626047 := by exact prefixLift 3626047
  have htrace : WordTrace (prefixWord ++ tailWord_3626047) baseStart_3626047 baseEnd_3626047 := by
    simpa [prefixWord, tailWord_3626047, baseEnd_3626047] using wordTrace_append hprefix tailTrace_3626047
  have hstable : (prefixWord ++ tailWord_3626047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626047).length < 2 ^ (prefixWord ++ tailWord_3626047).sum := by decide
  have hdescent : baseEnd_3626047 < baseStart_3626047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626067 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8]
def baseStart_3626067 : Nat := 118140960795 + 3626067 * 2 ^ 59
def prefixEnd_3626067 : Nat := 4983230072969 + 3 ^ 40 * 3626067 * 2
def baseEnd_3626067 : Nat := 1861915256406769729886527

theorem tailTrace_3626067 : CollatzResearch.WordTrace tailWord_3626067 prefixEnd_3626067 1861915256406769729886527 := by
  unfold tailWord_3626067
  simp only [CollatzResearch.WordTrace]
  refine ⟨132253528554386016785076455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88169019036257344523384303 132253528554386016785076455)
  ·
    refine ⟨198380292831579025177614683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132253528554386016785076455 198380292831579025177614683)
    ·
      refine ⟨297570439247368537766422025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198380292831579025177614683 297570439247368537766422025)
      ·
        refine ⟨223177829435526403324816519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297570439247368537766422025 223177829435526403324816519)
        ·
          refine ⟨334766744153289604987224779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223177829435526403324816519 334766744153289604987224779)
          ·
            refine ⟨502150116229934407480837169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334766744153289604987224779 502150116229934407480837169)
            ·
              refine ⟨376612587172450805610627877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502150116229934407480837169 376612587172450805610627877)
              ·
                refine ⟨70614860094834526051992727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376612587172450805610627877 70614860094834526051992727)
                ·
                  refine ⟨105922290142251789077989091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70614860094834526051992727 105922290142251789077989091)
                  ·
                    refine ⟨158883435213377683616983637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105922290142251789077989091 158883435213377683616983637)
                    ·
                      refine ⟨1861915256406769729886527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 158883435213377683616983637 1861915256406769729886527)
                      ·
                        rfl

theorem cell23_3626067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_3626067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626067 prefixEnd_3626067 := by exact prefixLift 3626067
  have htrace : WordTrace (prefixWord ++ tailWord_3626067) baseStart_3626067 baseEnd_3626067 := by
    simpa [prefixWord, tailWord_3626067, baseEnd_3626067] using wordTrace_append hprefix tailTrace_3626067
  have hstable : (prefixWord ++ tailWord_3626067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626067).length < 2 ^ (prefixWord ++ tailWord_3626067).sum := by decide
  have hdescent : baseEnd_3626067 < baseStart_3626067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626068 : List Nat := [2, 4, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_3626068 : Nat := 118140960795 + 3626068 * 2 ^ 59
def prefixEnd_3626068 : Nat := 4983230072969 + 3 ^ 40 * 3626068 * 2
def baseEnd_3626068 : Nat := 620638589962474741991341

theorem tailTrace_3626068 : CollatzResearch.WordTrace tailWord_3626068 prefixEnd_3626068 620638589962474741991341 := by
  unfold tailWord_3626068
  simp only [CollatzResearch.WordTrace]
  refine ⟨66126782513691196977931429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88169043351588262637241905 66126782513691196977931429)
  ·
    refine ⟨12398771721317099433362143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66126782513691196977931429 12398771721317099433362143)
    ·
      refine ⟨18598157581975649150043215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12398771721317099433362143 18598157581975649150043215)
      ·
        refine ⟨27897236372963473725064823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18598157581975649150043215 27897236372963473725064823)
        ·
          refine ⟨41845854559445210587597235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27897236372963473725064823 41845854559445210587597235)
          ·
            refine ⟨62768781839167815881395853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41845854559445210587597235 62768781839167815881395853)
            ·
              refine ⟨23538293189687930955523445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62768781839167815881395853 23538293189687930955523445)
              ·
                refine ⟨2206714986533243527080323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23538293189687930955523445 2206714986533243527080323)
                ·
                  refine ⟨3310072479799865290620485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206714986533243527080323 3310072479799865290620485)
                  ·
                    refine ⟨620638589962474741991341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310072479799865290620485 620638589962474741991341)
                    ·
                      rfl

theorem cell23_3626068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_3626068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626068 prefixEnd_3626068 := by exact prefixLift 3626068
  have htrace : WordTrace (prefixWord ++ tailWord_3626068) baseStart_3626068 baseEnd_3626068 := by
    simpa [prefixWord, tailWord_3626068, baseEnd_3626068] using wordTrace_append hprefix tailTrace_3626068
  have hstable : (prefixWord ++ tailWord_3626068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626068).length < 2 ^ (prefixWord ++ tailWord_3626068).sum := by decide
  have hdescent : baseEnd_3626068 < baseStart_3626068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626124 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 1, 6]
def baseStart_3626124 : Nat := 118140960795 + 3626124 * 2 ^ 59
def prefixEnd_3626124 : Nat := 4983230072969 + 3 ^ 40 * 3626124 * 2
def baseEnd_3626124 : Nat := 620648174934692002291255

theorem tailTrace_3626124 : CollatzResearch.WordTrace tailWord_3626124 prefixEnd_3626124 620648174934692002291255 := by
  unfold tailWord_3626124
  simp only [CollatzResearch.WordTrace]
  refine ⟨66127803757589757759950713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88170405010119677013267617 66127803757589757759950713)
  ·
    refine ⟨49595852818192318319963035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66127803757589757759950713 49595852818192318319963035)
    ·
      refine ⟨74393779227288477479944553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49595852818192318319963035 74393779227288477479944553)
      ·
        refine ⟨55795334420466358109958415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74393779227288477479944553 55795334420466358109958415)
        ·
          refine ⟨83693001630699537164937623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55795334420466358109958415 83693001630699537164937623)
          ·
            refine ⟨125539502446049305747406435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83693001630699537164937623 125539502446049305747406435)
            ·
              refine ⟨188309253669073958621109653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125539502446049305747406435 188309253669073958621109653)
              ·
                refine ⟨8826996265737841810364515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188309253669073958621109653 8826996265737841810364515)
                ·
                  refine ⟨13240494398606762715546773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8826996265737841810364515 13240494398606762715546773)
                  ·
                    refine ⟨620648174934692002291255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13240494398606762715546773 620648174934692002291255)
                    ·
                      rfl

theorem cell23_3626124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_3626124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626124 prefixEnd_3626124 := by exact prefixLift 3626124
  have htrace : WordTrace (prefixWord ++ tailWord_3626124) baseStart_3626124 baseEnd_3626124 := by
    simpa [prefixWord, tailWord_3626124, baseEnd_3626124] using wordTrace_append hprefix tailTrace_3626124
  have hstable : (prefixWord ++ tailWord_3626124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626124).length < 2 ^ (prefixWord ++ tailWord_3626124).sum := by decide
  have hdescent : baseEnd_3626124 < baseStart_3626124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626131 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 4]
def baseStart_3626131 : Nat := 118140960795 + 3626131 * 2 ^ 59
def prefixEnd_3626131 : Nat := 4983230072969 + 3 ^ 40 * 3626131 * 2
def baseEnd_3626131 : Nat := 1861948119168657479486233

theorem tailTrace_3626131 : CollatzResearch.WordTrace tailWord_3626131 prefixEnd_3626131 1861948119168657479486233 := by
  unfold tailWord_3626131
  simp only [CollatzResearch.WordTrace]
  refine ⟨132255862826154155715406247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88170575217436103810270831 132255862826154155715406247)
  ·
    refine ⟨198383794239231233573109371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132255862826154155715406247 198383794239231233573109371)
    ·
      refine ⟨297575691358846850359664057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198383794239231233573109371 297575691358846850359664057)
      ·
        refine ⟨223181768519135137769748043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297575691358846850359664057 223181768519135137769748043)
        ·
          refine ⟨334772652778702706654622065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223181768519135137769748043 334772652778702706654622065)
          ·
            refine ⟨251079489584027029990966549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334772652778702706654622065 251079489584027029990966549)
            ·
              refine ⟨11769351074251267030826557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 251079489584027029990966549 11769351074251267030826557)
              ·
                refine ⟨4413506652844225136559959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11769351074251267030826557 4413506652844225136559959)
                ·
                  refine ⟨6620259979266337704839939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4413506652844225136559959 6620259979266337704839939)
                  ·
                    refine ⟨9930389968899506557259909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6620259979266337704839939 9930389968899506557259909)
                    ·
                      refine ⟨1861948119168657479486233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9930389968899506557259909 1861948119168657479486233)
                      ·
                        rfl

theorem cell23_3626131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_3626131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626131 prefixEnd_3626131 := by exact prefixLift 3626131
  have htrace : WordTrace (prefixWord ++ tailWord_3626131) baseStart_3626131 baseEnd_3626131 := by
    simpa [prefixWord, tailWord_3626131, baseEnd_3626131] using wordTrace_append hprefix tailTrace_3626131
  have hstable : (prefixWord ++ tailWord_3626131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626131).length < 2 ^ (prefixWord ++ tailWord_3626131).sum := by decide
  have hdescent : baseEnd_3626131 < baseStart_3626131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626141 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3626141 : Nat := 118140960795 + 3626141 * 2 ^ 59
def prefixEnd_3626141 : Nat := 4983230072969 + 3 ^ 40 * 3626141 * 2
def baseEnd_3626141 : Nat := 620651084658400813453729

theorem tailTrace_3626141 : CollatzResearch.WordTrace tailWord_3626141 prefixEnd_3626141 620651084658400813453729 := by
  unfold tailWord_3626141
  simp only [CollatzResearch.WordTrace]
  refine ⟨132256227556117927423270277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88170818370745284948846851 132256227556117927423270277)
  ·
    refine ⟨24798042666772111391863177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132256227556117927423270277 24798042666772111391863177)
    ·
      refine ⟨18598532000079083543897383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24798042666772111391863177 18598532000079083543897383)
      ·
        refine ⟨27897798000118625315846075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18598532000079083543897383 27897798000118625315846075)
        ·
          refine ⟨41846697000177937973769113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27897798000118625315846075 41846697000177937973769113)
          ·
            refine ⟨31385022750133453480326835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41846697000177937973769113 31385022750133453480326835)
            ·
              refine ⟨47077534125200180220490253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31385022750133453480326835 47077534125200180220490253)
              ·
                refine ⟨17654075296950067582683845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47077534125200180220490253 17654075296950067582683845)
                ·
                  refine ⟨3310139118178137671753221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17654075296950067582683845 3310139118178137671753221)
                  ·
                    refine ⟨620651084658400813453729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310139118178137671753221 620651084658400813453729)
                    ·
                      rfl

theorem cell23_3626141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3626141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626141 prefixEnd_3626141 := by exact prefixLift 3626141
  have htrace : WordTrace (prefixWord ++ tailWord_3626141) baseStart_3626141 baseEnd_3626141 := by
    simpa [prefixWord, tailWord_3626141, baseEnd_3626141] using wordTrace_append hprefix tailTrace_3626141
  have hstable : (prefixWord ++ tailWord_3626141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626141).length < 2 ^ (prefixWord ++ tailWord_3626141).sum := by decide
  have hdescent : baseEnd_3626141 < baseStart_3626141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626142 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3626142 : Nat := 118140960795 + 3626142 * 2 ^ 59
def prefixEnd_3626142 : Nat := 4983230072969 + 3 ^ 40 * 3626142 * 2
def baseEnd_3626142 : Nat := 1861953767455856936448683

theorem tailTrace_3626142 : CollatzResearch.WordTrace tailWord_3626142 prefixEnd_3626142 1861953767455856936448683 := by
  unfold tailWord_3626142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532033003639288074257085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88170842686076203062704453 16532033003639288074257085)
  ·
    refine ⟨6199512376364733027846407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16532033003639288074257085 6199512376364733027846407)
    ·
      refine ⟨9299268564547099541769611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6199512376364733027846407 9299268564547099541769611)
      ·
        refine ⟨13948902846820649312654417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9299268564547099541769611 13948902846820649312654417)
        ·
          refine ⟨10461677135115486984490813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13948902846820649312654417 10461677135115486984490813)
          ·
            refine ⟨3923128925668307619184055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10461677135115486984490813 3923128925668307619184055)
            ·
              refine ⟨5884693388502461428776083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923128925668307619184055 5884693388502461428776083)
              ·
                refine ⟨8827040082753692143164125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884693388502461428776083 8827040082753692143164125)
                ·
                  refine ⟨3310140031032634553686547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8827040082753692143164125 3310140031032634553686547)
                  ·
                    refine ⟨4965210046548951830529821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3310140031032634553686547 4965210046548951830529821)
                    ·
                      refine ⟨1861953767455856936448683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4965210046548951830529821 1861953767455856936448683)
                      ·
                        rfl

theorem cell23_3626142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3626142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626142 prefixEnd_3626142 := by exact prefixLift 3626142
  have htrace : WordTrace (prefixWord ++ tailWord_3626142) baseStart_3626142 baseEnd_3626142 := by
    simpa [prefixWord, tailWord_3626142, baseEnd_3626142] using wordTrace_append hprefix tailTrace_3626142
  have hstable : (prefixWord ++ tailWord_3626142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626142).length < 2 ^ (prefixWord ++ tailWord_3626142).sum := by decide
  have hdescent : baseEnd_3626142 < baseStart_3626142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626144 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3626144 : Nat := 118140960795 + 3626144 * 2 ^ 59
def prefixEnd_3626144 : Nat := 4983230072969 + 3 ^ 40 * 3626144 * 2
def baseEnd_3626144 : Nat := 1861954794417165928623673

theorem tailTrace_3626144 : CollatzResearch.WordTrace tailWord_3626144 prefixEnd_3626144 1861954794417165928623673 := by
  unfold tailWord_3626144
  simp only [CollatzResearch.WordTrace]
  refine ⟨66128168487553529467814743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88170891316738039290419657 66128168487553529467814743)
  ·
    refine ⟨99192252731330294201722115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66128168487553529467814743 99192252731330294201722115)
    ·
      refine ⟨148788379096995441302583173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99192252731330294201722115 148788379096995441302583173)
      ·
        refine ⟨27897821080686645244234345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148788379096995441302583173 27897821080686645244234345)
        ·
          refine ⟨20923365810514983933175759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27897821080686645244234345 20923365810514983933175759)
          ·
            refine ⟨31385048715772475899763639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20923365810514983933175759 31385048715772475899763639)
            ·
              refine ⟨47077573073658713849645459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31385048715772475899763639 47077573073658713849645459)
              ·
                refine ⟨70616359610488070774468189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47077573073658713849645459 70616359610488070774468189)
                ·
                  refine ⟨26481134853933026540425571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70616359610488070774468189 26481134853933026540425571)
                  ·
                    refine ⟨39721702280899539810638357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26481134853933026540425571 39721702280899539810638357)
                    ·
                      refine ⟨1861954794417165928623673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39721702280899539810638357 1861954794417165928623673)
                      ·
                        rfl

theorem cell23_3626144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3626144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626144 prefixEnd_3626144 := by exact prefixLift 3626144
  have htrace : WordTrace (prefixWord ++ tailWord_3626144) baseStart_3626144 baseEnd_3626144 := by
    simpa [prefixWord, tailWord_3626144, baseEnd_3626144] using wordTrace_append hprefix tailTrace_3626144
  have hstable : (prefixWord ++ tailWord_3626144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626144).length < 2 ^ (prefixWord ++ tailWord_3626144).sum := by decide
  have hdescent : baseEnd_3626144 < baseStart_3626144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626161 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3626161 : Nat := 118140960795 + 3626161 * 2 ^ 59
def prefixEnd_3626161 : Nat := 4983230072969 + 3 ^ 40 * 3626161 * 2
def baseEnd_3626161 : Nat := 1861963523588292362111095

theorem tailTrace_3626161 : CollatzResearch.WordTrace tailWord_3626161 prefixEnd_3626161 1861963523588292362111095 := by
  unfold tailWord_3626161
  simp only [CollatzResearch.WordTrace]
  refine ⟨132256957016045470838998337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88171304677363647225998891 132256957016045470838998337)
  ·
    refine ⟨99192717762034103129248753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132256957016045470838998337 99192717762034103129248753)
    ·
      refine ⟨74394538321525577346936565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99192717762034103129248753 74394538321525577346936565)
      ·
        refine ⟨6974487967643022876275303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74394538321525577346936565 6974487967643022876275303)
        ·
          refine ⟨10461731951464534314412955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6974487967643022876275303 10461731951464534314412955)
          ·
            refine ⟨15692597927196801471619433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10461731951464534314412955 15692597927196801471619433)
            ·
              refine ⟨11769448445397601103714575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15692597927196801471619433 11769448445397601103714575)
              ·
                refine ⟨17654172668096401655571863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11769448445397601103714575 17654172668096401655571863)
                ·
                  refine ⟨26481259002144602483357795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17654172668096401655571863 26481259002144602483357795)
                  ·
                    refine ⟨39721888503216903725036693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26481259002144602483357795 39721888503216903725036693)
                    ·
                      refine ⟨1861963523588292362111095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39721888503216903725036693 1861963523588292362111095)
                      ·
                        rfl

theorem cell23_3626161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3626161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626161 prefixEnd_3626161 := by exact prefixLift 3626161
  have htrace : WordTrace (prefixWord ++ tailWord_3626161) baseStart_3626161 baseEnd_3626161 := by
    simpa [prefixWord, tailWord_3626161, baseEnd_3626161] using wordTrace_append hprefix tailTrace_3626161
  have hstable : (prefixWord ++ tailWord_3626161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626161).length < 2 ^ (prefixWord ++ tailWord_3626161).sum := by decide
  have hdescent : baseEnd_3626161 < baseStart_3626161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626205 : List Nat := [1, 4, 3, 2, 3, 1, 1, 8]
def baseStart_3626205 : Nat := 118140960795 + 3626205 * 2 ^ 59
def prefixEnd_3626205 : Nat := 4983230072969 + 3 ^ 40 * 3626205 * 2
def baseEnd_3626205 : Nat := 68962448768040377405959

theorem tailTrace_3626205 : CollatzResearch.WordTrace tailWord_3626205 prefixEnd_3626205 68962448768040377405959 := by
  unfold tailWord_3626205
  simp only [CollatzResearch.WordTrace]
  refine ⟨132258561827886066353600069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88172374551924044235733379 132258561827886066353600069)
  ·
    refine ⟨24798480342728637441300013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132258561827886066353600069 24798480342728637441300013)
    ·
      refine ⟨9299430128523239040487505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24798480342728637441300013 9299430128523239040487505)
      ·
        refine ⟨6974572596392429280365629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9299430128523239040487505 6974572596392429280365629)
        ·
          refine ⟨2615464723647160980137111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6974572596392429280365629 2615464723647160980137111)
          ·
            refine ⟨3923197085470741470205667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615464723647160980137111 3923197085470741470205667)
            ·
              refine ⟨5884795628206112205308501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923197085470741470205667 5884795628206112205308501)
              ·
                refine ⟨68962448768040377405959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5884795628206112205308501 68962448768040377405959)
                ·
                  rfl

theorem cell23_3626205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 8].length) (baseStart_3626205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626205 prefixEnd_3626205 := by exact prefixLift 3626205
  have htrace : WordTrace (prefixWord ++ tailWord_3626205) baseStart_3626205 baseEnd_3626205 := by
    simpa [prefixWord, tailWord_3626205, baseEnd_3626205] using wordTrace_append hprefix tailTrace_3626205
  have hstable : (prefixWord ++ tailWord_3626205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626205).length < 2 ^ (prefixWord ++ tailWord_3626205).sum := by decide
  have hdescent : baseEnd_3626205 < baseStart_3626205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626208 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 3, 3, 2]
def baseStart_3626208 : Nat := 118140960795 + 3626208 * 2 ^ 59
def prefixEnd_3626208 : Nat := 4983230072969 + 3 ^ 40 * 3626208 * 2
def baseEnd_3626208 : Nat := 1861987657179053678223379

theorem tailTrace_3626208 : CollatzResearch.WordTrace tailWord_3626208 prefixEnd_3626208 1861987657179053678223379 := by
  unfold tailWord_3626208
  simp only [CollatzResearch.WordTrace]
  refine ⟨66129335623437598932979639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88172447497916798577306185 66129335623437598932979639)
  ·
    refine ⟨99194003435156398399469459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66129335623437598932979639 99194003435156398399469459)
    ·
      refine ⟨148791005152734597599204189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99194003435156398399469459 148791005152734597599204189)
      ·
        refine ⟨55796626932275474099701571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148791005152734597599204189 55796626932275474099701571)
        ·
          refine ⟨83694940398413211149552357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55796626932275474099701571 83694940398413211149552357)
          ·
            refine ⟨15692801324702477090541067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83694940398413211149552357 15692801324702477090541067)
            ·
              refine ⟨23539201987053715635811601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15692801324702477090541067 23539201987053715635811601)
              ·
                refine ⟨17654401490290286726858701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23539201987053715635811601 17654401490290286726858701)
                ·
                  refine ⟨6620400558858857522572013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17654401490290286726858701 6620400558858857522572013)
                  ·
                    refine ⟨2482650209572071570964505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6620400558858857522572013 2482650209572071570964505)
                    ·
                      refine ⟨1861987657179053678223379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482650209572071570964505 1861987657179053678223379)
                      ·
                        rfl

theorem cell23_3626208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_3626208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626208 prefixEnd_3626208 := by exact prefixLift 3626208
  have htrace : WordTrace (prefixWord ++ tailWord_3626208) baseStart_3626208 baseEnd_3626208 := by
    simpa [prefixWord, tailWord_3626208, baseEnd_3626208] using wordTrace_append hprefix tailTrace_3626208
  have hstable : (prefixWord ++ tailWord_3626208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626208).length < 2 ^ (prefixWord ++ tailWord_3626208).sum := by decide
  have hdescent : baseEnd_3626208 < baseStart_3626208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626215 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3626215 : Nat := 118140960795 + 3626215 * 2 ^ 59
def prefixEnd_3626215 : Nat := 4983230072969 + 3 ^ 40 * 3626215 * 2
def baseEnd_3626215 : Nat := 1861991251543635150835847

theorem tailTrace_3626215 : CollatzResearch.WordTrace tailWord_3626215 prefixEnd_3626215 1861991251543635150835847 := by
  unfold tailWord_3626215
  simp only [CollatzResearch.WordTrace]
  refine ⟨132258926557849838061464099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88172617705233225374309399 132258926557849838061464099)
  ·
    refine ⟨198388389836774757092196149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132258926557849838061464099 198388389836774757092196149)
    ·
      refine ⟨18598911547197633477393389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198388389836774757092196149 18598911547197633477393389)
      ·
        refine ⟨6974591830199112554022521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18598911547197633477393389 6974591830199112554022521)
        ·
          refine ⟨5230943872649334415516891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6974591830199112554022521 5230943872649334415516891)
          ·
            refine ⟨7846415808974001623275337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5230943872649334415516891 7846415808974001623275337)
            ·
              refine ⟨5884811856730501217456503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7846415808974001623275337 5884811856730501217456503)
              ·
                refine ⟨8827217785095751826184755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884811856730501217456503 8827217785095751826184755)
                ·
                  refine ⟨13240826677643627739277133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8827217785095751826184755 13240826677643627739277133)
                  ·
                    refine ⟨4965310004116360402228925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13240826677643627739277133 4965310004116360402228925)
                    ·
                      refine ⟨1861991251543635150835847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4965310004116360402228925 1861991251543635150835847)
                      ·
                        rfl

theorem cell23_3626215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3626215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626215 prefixEnd_3626215 := by exact prefixLift 3626215
  have htrace : WordTrace (prefixWord ++ tailWord_3626215) baseStart_3626215 baseEnd_3626215 := by
    simpa [prefixWord, tailWord_3626215, baseEnd_3626215] using wordTrace_append hprefix tailTrace_3626215
  have hstable : (prefixWord ++ tailWord_3626215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626215).length < 2 ^ (prefixWord ++ tailWord_3626215).sum := by decide
  have hdescent : baseEnd_3626215 < baseStart_3626215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626251 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4]
def baseStart_3626251 : Nat := 118140960795 + 3626251 * 2 ^ 59
def prefixEnd_3626251 : Nat := 4983230072969 + 3 ^ 40 * 3626251 * 2
def baseEnd_3626251 : Nat := 1862009736847197009985681

theorem tailTrace_3626251 : CollatzResearch.WordTrace tailWord_3626251 prefixEnd_3626251 1862009736847197009985681 := by
  unfold tailWord_3626251
  simp only [CollatzResearch.WordTrace]
  refine ⟨132260239585719416209774607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88173493057146277473183071 132260239585719416209774607)
  ·
    refine ⟨198390359378579124314661911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132260239585719416209774607 198390359378579124314661911)
    ·
      refine ⟨297585539067868686471992867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198390359378579124314661911 297585539067868686471992867)
      ·
        refine ⟨446378308601803029707989301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297585539067868686471992867 446378308601803029707989301)
        ·
          refine ⟨41847966431419034035123997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446378308601803029707989301 41847966431419034035123997)
          ·
            refine ⟨15692987411782137763171499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41847966431419034035123997 15692987411782137763171499)
            ·
              refine ⟨23539481117673206644757249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15692987411782137763171499 23539481117673206644757249)
              ·
                refine ⟨17654610838254904983567937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23539481117673206644757249 17654610838254904983567937)
                ·
                  refine ⟨13240958128691178737675953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17654610838254904983567937 13240958128691178737675953)
                  ·
                    refine ⟨9930718596518384053256965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13240958128691178737675953 9930718596518384053256965)
                    ·
                      refine ⟨1862009736847197009985681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9930718596518384053256965 1862009736847197009985681)
                      ·
                        rfl

theorem cell23_3626251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 4].length) (baseStart_3626251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626251 prefixEnd_3626251 := by exact prefixLift 3626251
  have htrace : WordTrace (prefixWord ++ tailWord_3626251) baseStart_3626251 baseEnd_3626251 := by
    simpa [prefixWord, tailWord_3626251, baseEnd_3626251] using wordTrace_append hprefix tailTrace_3626251
  have hstable : (prefixWord ++ tailWord_3626251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626251).length < 2 ^ (prefixWord ++ tailWord_3626251).sum := by decide
  have hdescent : baseEnd_3626251 < baseStart_3626251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626272 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 1, 4, 2]
def baseStart_3626272 : Nat := 118140960795 + 3626272 * 2 ^ 59
def prefixEnd_3626272 : Nat := 4983230072969 + 3 ^ 40 * 3626272 * 2
def baseEnd_3626272 : Nat := 1862020519940941427823085

theorem tailTrace_3626272 : CollatzResearch.WordTrace tailWord_3626272 prefixEnd_3626272 1862020519940941427823085 := by
  unfold tailWord_3626272
  simp only [CollatzResearch.WordTrace]
  refine ⟨66130502759321668398144535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88174003679095557864192713 66130502759321668398144535)
  ·
    refine ⟨99195754138982502597216803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66130502759321668398144535 99195754138982502597216803)
    ·
      refine ⟨148793631208473753895825205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99195754138982502597216803 148793631208473753895825205)
      ·
        refine ⟨13949402925794414427733613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148793631208473753895825205 13949402925794414427733613)
        ·
          refine ⟨5231026097172905410400105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13949402925794414427733613 5231026097172905410400105)
          ·
            refine ⟨3923269572879679057800079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5231026097172905410400105 3923269572879679057800079)
            ·
              refine ⟨5884904359319518586700119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923269572879679057800079 5884904359319518586700119)
              ·
                refine ⟨8827356538979277880050179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5884904359319518586700119 8827356538979277880050179)
                ·
                  refine ⟨13241034808468916820075269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8827356538979277880050179 13241034808468916820075269)
                  ·
                    refine ⟨2482694026587921903764113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13241034808468916820075269 2482694026587921903764113)
                    ·
                      refine ⟨1862020519940941427823085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482694026587921903764113 1862020519940941427823085)
                      ·
                        rfl

theorem cell23_3626272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_3626272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626272 prefixEnd_3626272 := by exact prefixLift 3626272
  have htrace : WordTrace (prefixWord ++ tailWord_3626272) baseStart_3626272 baseEnd_3626272 := by
    simpa [prefixWord, tailWord_3626272, baseEnd_3626272] using wordTrace_append hprefix tailTrace_3626272
  have hstable : (prefixWord ++ tailWord_3626272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626272).length < 2 ^ (prefixWord ++ tailWord_3626272).sum := by decide
  have hdescent : baseEnd_3626272 < baseStart_3626272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626291 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 1, 7]
def baseStart_3626291 : Nat := 118140960795 + 3626291 * 2 ^ 59
def prefixEnd_3626291 : Nat := 4983230072969 + 3 ^ 40 * 3626291 * 2
def baseEnd_3626291 : Nat := 620676758691125617828499

theorem tailTrace_3626291 : CollatzResearch.WordTrace tailWord_3626291 prefixEnd_3626291 620676758691125617828499 := by
  unfold tailWord_3626291
  simp only [CollatzResearch.WordTrace]
  refine ⟨132261698505574503041230727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88174465670383002027487151 132261698505574503041230727)
  ·
    refine ⟨198392547758361754561846091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132261698505574503041230727 198392547758361754561846091)
    ·
      refine ⟨297588821637542631842769137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198392547758361754561846091 297588821637542631842769137)
      ·
        refine ⟨223191616228156973882076853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297588821637542631842769137 223191616228156973882076853)
        ·
          refine ⟨20924214021389716301444705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223191616228156973882076853 20924214021389716301444705)
          ·
            refine ⟨15693160516042287226083529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20924214021389716301444705 15693160516042287226083529)
            ·
              refine ⟨11769870387031715419562647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15693160516042287226083529 11769870387031715419562647)
              ·
                refine ⟨17654805580547573129343971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11769870387031715419562647 17654805580547573129343971)
                ·
                  refine ⟨26482208370821359694015957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17654805580547573129343971 26482208370821359694015957)
                  ·
                    refine ⟨620676758691125617828499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26482208370821359694015957 620676758691125617828499)
                    ·
                      rfl

theorem cell23_3626291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 7].length) (baseStart_3626291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626291 prefixEnd_3626291 := by exact prefixLift 3626291
  have htrace : WordTrace (prefixWord ++ tailWord_3626291) baseStart_3626291 baseEnd_3626291 := by
    simpa [prefixWord, tailWord_3626291, baseEnd_3626291] using wordTrace_append hprefix tailTrace_3626291
  have hstable : (prefixWord ++ tailWord_3626291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626291).length < 2 ^ (prefixWord ++ tailWord_3626291).sum := by decide
  have hdescent : baseEnd_3626291 < baseStart_3626291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626328 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 1, 6, 2]
def baseStart_3626328 : Nat := 118140960795 + 3626328 * 2 ^ 59
def prefixEnd_3626328 : Nat := 4983230072969 + 3 ^ 40 * 3626328 * 2
def baseEnd_3626328 : Nat := 1862049274857593208722827

theorem tailTrace_3626328 : CollatzResearch.WordTrace tailWord_3626328 prefixEnd_3626328 1862049274857593208722827 := by
  unfold tailWord_3626328
  simp only [CollatzResearch.WordTrace]
  refine ⟨66131524003220229180163819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88175365337626972240218425 66131524003220229180163819)
  ·
    refine ⟨99197286004830343770245729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66131524003220229180163819 99197286004830343770245729)
    ·
      refine ⟨74397964503622757827684297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99197286004830343770245729 74397964503622757827684297)
      ·
        refine ⟨55798473377717068370763223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74397964503622757827684297 55798473377717068370763223)
        ·
          refine ⟨83697710066575602556144835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55798473377717068370763223 83697710066575602556144835)
          ·
            refine ⟨125546565099863403834217253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83697710066575602556144835 125546565099863403834217253)
            ·
              refine ⟨23539980956224388218915735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125546565099863403834217253 23539980956224388218915735)
              ·
                refine ⟨35309971434336582328373603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23539980956224388218915735 35309971434336582328373603)
                ·
                  refine ⟨52964957151504873492560405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35309971434336582328373603 52964957151504873492560405)
                  ·
                    refine ⟨2482732366476790944963769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52964957151504873492560405 2482732366476790944963769)
                    ·
                      refine ⟨1862049274857593208722827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482732366476790944963769 1862049274857593208722827)
                      ·
                        rfl

theorem cell23_3626328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_3626328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626328 prefixEnd_3626328 := by exact prefixLift 3626328
  have htrace : WordTrace (prefixWord ++ tailWord_3626328) baseStart_3626328 baseEnd_3626328 := by
    simpa [prefixWord, tailWord_3626328, baseEnd_3626328] using wordTrace_append hprefix tailTrace_3626328
  have hstable : (prefixWord ++ tailWord_3626328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626328).length < 2 ^ (prefixWord ++ tailWord_3626328).sum := by decide
  have hdescent : baseEnd_3626328 < baseStart_3626328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626372 : List Nat := [2, 3, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_3626372 : Nat := 118140960795 + 3626372 * 2 ^ 59
def prefixEnd_3626372 : Nat := 4983230072969 + 3 ^ 40 * 3626372 * 2
def baseEnd_3626372 : Nat := 620690622668797012190875

theorem tailTrace_3626372 : CollatzResearch.WordTrace tailWord_3626372 prefixEnd_3626372 620690622668797012190875 := by
  unfold tailWord_3626372
  simp only [CollatzResearch.WordTrace]
  refine ⟨66132326409140526937464685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88176435212187369249952913 66132326409140526937464685)
  ·
    refine ⟨24799622403427697601549257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66132326409140526937464685 24799622403427697601549257)
    ·
      refine ⟨18599716802570773201161943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24799622403427697601549257 18599716802570773201161943)
      ·
        refine ⟨27899575203856159801742915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18599716802570773201161943 27899575203856159801742915)
        ·
          refine ⟨41849362805784239702614373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27899575203856159801742915 41849362805784239702614373)
          ·
            refine ⟨7846755526084544944240195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41849362805784239702614373 7846755526084544944240195)
            ·
              refine ⟨11770133289126817416360293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846755526084544944240195 11770133289126817416360293)
              ·
                refine ⟨2206899991711278265567555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11770133289126817416360293 2206899991711278265567555)
                ·
                  refine ⟨3310349987566917398351333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206899991711278265567555 3310349987566917398351333)
                  ·
                    refine ⟨620690622668797012190875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310349987566917398351333 620690622668797012190875)
                    ·
                      rfl

theorem cell23_3626372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_3626372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626372 prefixEnd_3626372 := by exact prefixLift 3626372
  have htrace : WordTrace (prefixWord ++ tailWord_3626372) baseStart_3626372 baseEnd_3626372 := by
    simpa [prefixWord, tailWord_3626372, baseEnd_3626372] using wordTrace_append hprefix tailTrace_3626372
  have hstable : (prefixWord ++ tailWord_3626372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626372).length < 2 ^ (prefixWord ++ tailWord_3626372).sum := by decide
  have hdescent : baseEnd_3626372 < baseStart_3626372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626391 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_3626391 : Nat := 118140960795 + 3626391 * 2 ^ 59
def prefixEnd_3626391 : Nat := 4983230072969 + 3 ^ 40 * 3626391 * 2
def baseEnd_3626391 : Nat := 1862081624138826462235037

theorem tailTrace_3626391 : CollatzResearch.WordTrace tailWord_3626391 prefixEnd_3626391 1862081624138826462235037 := by
  unfold tailWord_3626391
  simp only [CollatzResearch.WordTrace]
  refine ⟨132265345805212220119871027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88176897203474813413247351 132265345805212220119871027)
  ·
    refine ⟨198398018707818330179806541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132265345805212220119871027 198398018707818330179806541)
    ·
      refine ⟨74399257015431873817427453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198398018707818330179806541 74399257015431873817427453)
      ·
        refine ⟨27899721380786952681535295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74399257015431873817427453 27899721380786952681535295)
        ·
          refine ⟨41849582071180429022302943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27899721380786952681535295 41849582071180429022302943)
          ·
            refine ⟨62774373106770643533454415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41849582071180429022302943 62774373106770643533454415)
            ·
              refine ⟨94161559660155965300181623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62774373106770643533454415 94161559660155965300181623)
              ·
                refine ⟨141242339490233947950272435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94161559660155965300181623 141242339490233947950272435)
                ·
                  refine ⟨211863509235350921925408653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141242339490233947950272435 211863509235350921925408653)
                  ·
                    refine ⟨79448815963256595722028245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211863509235350921925408653 79448815963256595722028245)
                    ·
                      refine ⟨1862081624138826462235037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79448815963256595722028245 1862081624138826462235037)
                      ·
                        rfl

theorem cell23_3626391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_3626391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626391 prefixEnd_3626391 := by exact prefixLift 3626391
  have htrace : WordTrace (prefixWord ++ tailWord_3626391) baseStart_3626391 baseEnd_3626391 := by
    simpa [prefixWord, tailWord_3626391, baseEnd_3626391] using wordTrace_append hprefix tailTrace_3626391
  have hstable : (prefixWord ++ tailWord_3626391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626391).length < 2 ^ (prefixWord ++ tailWord_3626391).sum := by decide
  have hdescent : baseEnd_3626391 < baseStart_3626391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626405 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 2, 3, 2]
def baseStart_3626405 : Nat := 118140960795 + 3626405 * 2 ^ 59
def prefixEnd_3626405 : Nat := 4983230072969 + 3 ^ 40 * 3626405 * 2
def baseEnd_3626405 : Nat := 1862088812867989407459973

theorem tailTrace_3626405 : CollatzResearch.WordTrace tailWord_3626405 prefixEnd_3626405 1862088812867989407459973 := by
  unfold tailWord_3626405
  simp only [CollatzResearch.WordTrace]
  refine ⟨132265856427161500510880669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88177237618107667007253779 132265856427161500510880669)
  ·
    refine ⟨49599696160185562691580251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132265856427161500510880669 49599696160185562691580251)
    ·
      refine ⟨74399544240278344037370377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49599696160185562691580251 74399544240278344037370377)
      ·
        refine ⟨55799658180208758028027783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74399544240278344037370377 55799658180208758028027783)
        ·
          refine ⟨83699487270313137042041675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55799658180208758028027783 83699487270313137042041675)
          ·
            refine ⟨125549230905469705563062513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83699487270313137042041675 125549230905469705563062513)
            ·
              refine ⟨94161923179102279172296885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125549230905469705563062513 94161923179102279172296885)
              ·
                refine ⟨8827680298040838672402833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94161923179102279172296885 8827680298040838672402833)
                ·
                  refine ⟨6620760223530629004302125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8827680298040838672402833 6620760223530629004302125)
                  ·
                    refine ⟨2482785083823985876613297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6620760223530629004302125 2482785083823985876613297)
                    ·
                      refine ⟨1862088812867989407459973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482785083823985876613297 1862088812867989407459973)
                      ·
                        rfl

theorem cell23_3626405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_3626405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626405 prefixEnd_3626405 := by exact prefixLift 3626405
  have htrace : WordTrace (prefixWord ++ tailWord_3626405) baseStart_3626405 baseEnd_3626405 := by
    simpa [prefixWord, tailWord_3626405, baseEnd_3626405] using wordTrace_append hprefix tailTrace_3626405
  have hstable : (prefixWord ++ tailWord_3626405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626405).length < 2 ^ (prefixWord ++ tailWord_3626405).sum := by decide
  have hdescent : baseEnd_3626405 < baseStart_3626405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626411 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 7, 6]
def baseStart_3626411 : Nat := 118140960795 + 3626411 * 2 ^ 59
def prefixEnd_3626411 : Nat := 4983230072969 + 3 ^ 40 * 3626411 * 2
def baseEnd_3626411 : Nat := 620697297917305461328315

theorem tailTrace_3626411 : CollatzResearch.WordTrace tailWord_3626411 prefixEnd_3626411 620697297917305461328315 := by
  unfold tailWord_3626411
  simp only [CollatzResearch.WordTrace]
  refine ⟨132266075265139763535599087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88177383510093175690399391 132266075265139763535599087)
  ·
    refine ⟨198399112897709645303398631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132266075265139763535599087 198399112897709645303398631)
    ·
      refine ⟨297598669346564467955097947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198399112897709645303398631 297598669346564467955097947)
      ·
        refine ⟨446398004019846701932646921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297598669346564467955097947 446398004019846701932646921)
        ·
          refine ⟨334798503014885026449485191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446398004019846701932646921 334798503014885026449485191)
          ·
            refine ⟨502197754522327539674227787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334798503014885026449485191 502197754522327539674227787)
            ·
              refine ⟨753296631783491309511341681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502197754522327539674227787 753296631783491309511341681)
              ·
                refine ⟨564972473837618482133506261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753296631783491309511341681 564972473837618482133506261)
                ·
                  refine ⟨13241542355569183175004053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 564972473837618482133506261 13241542355569183175004053)
                  ·
                    refine ⟨620697297917305461328315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13241542355569183175004053 620697297917305461328315)
                    ·
                      rfl

theorem cell23_3626411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 6].length) (baseStart_3626411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626411 prefixEnd_3626411 := by exact prefixLift 3626411
  have htrace : WordTrace (prefixWord ++ tailWord_3626411) baseStart_3626411 baseEnd_3626411 := by
    simpa [prefixWord, tailWord_3626411, baseEnd_3626411] using wordTrace_append hprefix tailTrace_3626411
  have hstable : (prefixWord ++ tailWord_3626411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626411).length < 2 ^ (prefixWord ++ tailWord_3626411).sum := by decide
  have hdescent : baseEnd_3626411 < baseStart_3626411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626412 : List Nat := [2, 2, 1, 1, 1, 1, 5, 5, 1, 1, 3]
def baseStart_3626412 : Nat := 118140960795 + 3626412 * 2 ^ 59
def prefixEnd_3626412 : Nat := 4983230072969 + 3 ^ 40 * 3626412 * 2
def baseEnd_3626412 : Nat := 1862092407232570880072441

theorem tailTrace_3626412 : CollatzResearch.WordTrace tailWord_3626412 prefixEnd_3626412 1862092407232570880072441 := by
  unfold tailWord_3626412
  simp only [CollatzResearch.WordTrace]
  refine ⟨66133055869068070353192745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88177407825424093804256993 66133055869068070353192745)
  ·
    refine ⟨49599791901801052764894559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66133055869068070353192745 49599791901801052764894559)
    ·
      refine ⟨74399687852701579147341839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49599791901801052764894559 74399687852701579147341839)
      ·
        refine ⟨111599531779052368721012759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74399687852701579147341839 111599531779052368721012759)
        ·
          refine ⟨167399297668578553081519139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111599531779052368721012759 167399297668578553081519139)
          ·
            refine ⟨251098946502867829622278709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167399297668578553081519139 251098946502867829622278709)
            ·
              refine ⟨23540526234643859027088629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251098946502867829622278709 23540526234643859027088629)
              ·
                refine ⟨2206924334497861783789559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23540526234643859027088629 2206924334497861783789559)
                ·
                  refine ⟨3310386501746792675684339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2206924334497861783789559 3310386501746792675684339)
                  ·
                    refine ⟨4965579752620189013526509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3310386501746792675684339 4965579752620189013526509)
                    ·
                      refine ⟨1862092407232570880072441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4965579752620189013526509 1862092407232570880072441)
                      ·
                        rfl

theorem cell23_3626412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 1, 1, 3].length) (baseStart_3626412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626412 prefixEnd_3626412 := by exact prefixLift 3626412
  have htrace : WordTrace (prefixWord ++ tailWord_3626412) baseStart_3626412 baseEnd_3626412 := by
    simpa [prefixWord, tailWord_3626412, baseEnd_3626412] using wordTrace_append hprefix tailTrace_3626412
  have hstable : (prefixWord ++ tailWord_3626412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626412).length < 2 ^ (prefixWord ++ tailWord_3626412).sum := by decide
  have hdescent : baseEnd_3626412 < baseStart_3626412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626418 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_3626418 : Nat := 118140960795 + 3626418 * 2 ^ 59
def prefixEnd_3626418 : Nat := 4983230072969 + 3 ^ 40 * 3626418 * 2
def baseEnd_3626418 : Nat := 1862095488116497856597413

theorem tailTrace_3626418 : CollatzResearch.WordTrace tailWord_3626418 prefixEnd_3626418 1862095488116497856597413 := by
  unfold tailWord_3626418
  simp only [CollatzResearch.WordTrace]
  refine ⟨33066582644028600932775977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88177553717409602487402605 33066582644028600932775977)
  ·
    refine ⟨24799936983021450699581983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33066582644028600932775977 24799936983021450699581983)
    ·
      refine ⟨37199905474532176049372975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24799936983021450699581983 37199905474532176049372975)
      ·
        refine ⟨55799858211798264074059463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37199905474532176049372975 55799858211798264074059463)
        ·
          refine ⟨83699787317697396111089195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55799858211798264074059463 83699787317697396111089195)
          ·
            refine ⟨125549680976546094166633793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83699787317697396111089195 125549680976546094166633793)
            ·
              refine ⟨94162260732409570624975345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125549680976546094166633793 94162260732409570624975345)
              ·
                refine ⟨70621695549307177968731509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94162260732409570624975345 70621695549307177968731509)
                ·
                  refine ⟨6620783957747547934568579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70621695549307177968731509 6620783957747547934568579)
                  ·
                    refine ⟨9931175936621321901852869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6620783957747547934568579 9931175936621321901852869)
                    ·
                      refine ⟨1862095488116497856597413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9931175936621321901852869 1862095488116497856597413)
                      ·
                        rfl

theorem cell23_3626418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_3626418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626418 prefixEnd_3626418 := by exact prefixLift 3626418
  have htrace : WordTrace (prefixWord ++ tailWord_3626418) baseStart_3626418 baseEnd_3626418 := by
    simpa [prefixWord, tailWord_3626418, baseEnd_3626418] using wordTrace_append hprefix tailTrace_3626418
  have hstable : (prefixWord ++ tailWord_3626418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626418).length < 2 ^ (prefixWord ++ tailWord_3626418).sum := by decide
  have hdescent : baseEnd_3626418 < baseStart_3626418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626441 : List Nat := [1, 2, 1, 1, 2, 1, 3, 12]
def baseStart_3626441 : Nat := 118140960795 + 3626441 * 2 ^ 59
def prefixEnd_3626441 : Nat := 4983230072969 + 3 ^ 40 * 3626441 * 2
def baseEnd_3626441 : Nat := 68966936969316713578141

theorem tailTrace_3626441 : CollatzResearch.WordTrace tailWord_3626441 prefixEnd_3626441 68966936969316713578141 := by
  unfold tailWord_3626441
  simp only [CollatzResearch.WordTrace]
  refine ⟨132267169455031078659191177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88178112970020719106127451 132267169455031078659191177)
  ·
    refine ⟨99200377091273308994393383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132267169455031078659191177 99200377091273308994393383)
    ·
      refine ⟨148800565636909963491590075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99200377091273308994393383 148800565636909963491590075)
      ·
        refine ⟨223200848455364945237385113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148800565636909963491590075 223200848455364945237385113)
        ·
          refine ⟨167400636341523708928038835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223200848455364945237385113 167400636341523708928038835)
          ·
            refine ⟨251100954512285563392058253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167400636341523708928038835 251100954512285563392058253)
            ·
              refine ⟨94162857942107086272021845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251100954512285563392058253 94162857942107086272021845)
              ·
                refine ⟨68966936969316713578141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 94162857942107086272021845 68966936969316713578141)
                ·
                  rfl

theorem cell23_3626441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 12].length) (baseStart_3626441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626441 prefixEnd_3626441 := by exact prefixLift 3626441
  have htrace : WordTrace (prefixWord ++ tailWord_3626441) baseStart_3626441 baseEnd_3626441 := by
    simpa [prefixWord, tailWord_3626441, baseEnd_3626441] using wordTrace_append hprefix tailTrace_3626441
  have hstable : (prefixWord ++ tailWord_3626441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626441).length < 2 ^ (prefixWord ++ tailWord_3626441).sum := by decide
  have hdescent : baseEnd_3626441 < baseStart_3626441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626451 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9]
def baseStart_3626451 : Nat := 118140960795 + 3626451 * 2 ^ 59
def prefixEnd_3626451 : Nat := 4983230072969 + 3 ^ 40 * 3626451 * 2
def baseEnd_3626451 : Nat := 1862112432978096227484761

theorem tailTrace_3626451 : CollatzResearch.WordTrace tailWord_3626451 prefixEnd_3626451 1862112432978096227484761 := by
  unfold tailWord_3626451
  simp only [CollatzResearch.WordTrace]
  refine ⟨132267534184994850367055207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88178356123329900244703471 132267534184994850367055207)
  ·
    refine ⟨198401301277492275550582811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132267534184994850367055207 198401301277492275550582811)
    ·
      refine ⟨297601951916238413325874217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198401301277492275550582811 297601951916238413325874217)
      ·
        refine ⟨223201463937178809994405663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297601951916238413325874217 223201463937178809994405663)
        ·
          refine ⟨334802195905768214991608495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223201463937178809994405663 334802195905768214991608495)
          ·
            refine ⟨502203293858652322487412743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334802195905768214991608495 502203293858652322487412743)
            ·
              refine ⟨753304940787978483731119115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502203293858652322487412743 753304940787978483731119115)
              ·
                refine ⟨1129957411181967725596678673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753304940787978483731119115 1129957411181967725596678673)
                ·
                  refine ⟨847468058386475794197509005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1129957411181967725596678673 847468058386475794197509005)
                  ·
                    refine ⟨317800521894928422824065877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 847468058386475794197509005 317800521894928422824065877)
                    ·
                      refine ⟨1862112432978096227484761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 317800521894928422824065877 1862112432978096227484761)
                      ·
                        rfl

theorem cell23_3626451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_3626451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626451 prefixEnd_3626451 := by exact prefixLift 3626451
  have htrace : WordTrace (prefixWord ++ tailWord_3626451) baseStart_3626451 baseEnd_3626451 := by
    simpa [prefixWord, tailWord_3626451, baseEnd_3626451] using wordTrace_append hprefix tailTrace_3626451
  have hstable : (prefixWord ++ tailWord_3626451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626451).length < 2 ^ (prefixWord ++ tailWord_3626451).sum := by decide
  have hdescent : baseEnd_3626451 < baseStart_3626451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626458 : List Nat := [3, 1, 1, 2, 3, 3, 1, 9]
def baseStart_3626458 : Nat := 118140960795 + 3626458 * 2 ^ 59
def prefixEnd_3626458 : Nat := 4983230072969 + 3 ^ 40 * 3626458 * 2
def baseEnd_3626458 : Nat := 68967260271951025929527

theorem tailTrace_3626458 : CollatzResearch.WordTrace tailWord_3626458 prefixEnd_3626458 68967260271951025929527 := by
  unfold tailWord_3626458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33066947373992372640640007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88178526330646327041706685 33066947373992372640640007)
  ·
    refine ⟨49600421060988558960960011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33066947373992372640640007 49600421060988558960960011)
    ·
      refine ⟨74400631591482838441440017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49600421060988558960960011 74400631591482838441440017)
      ·
        refine ⟨55800473693612128831080013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74400631591482838441440017 55800473693612128831080013)
        ·
          refine ⟨20925177635104548311655005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55800473693612128831080013 20925177635104548311655005)
          ·
            refine ⟨7846941613164205616870627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20925177635104548311655005 7846941613164205616870627)
            ·
              refine ⟨11770412419746308425305941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7846941613164205616870627 11770412419746308425305941)
              ·
                refine ⟨68967260271951025929527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11770412419746308425305941 68967260271951025929527)
                ·
                  rfl

theorem cell23_3626458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_3626458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626458 prefixEnd_3626458 := by exact prefixLift 3626458
  have htrace : WordTrace (prefixWord ++ tailWord_3626458) baseStart_3626458 baseEnd_3626458 := by
    simpa [prefixWord, tailWord_3626458, baseEnd_3626458] using wordTrace_append hprefix tailTrace_3626458
  have hstable : (prefixWord ++ tailWord_3626458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626458).length < 2 ^ (prefixWord ++ tailWord_3626458).sum := by decide
  have hdescent : baseEnd_3626458 < baseStart_3626458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626486 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_3626486 : Nat := 118140960795 + 3626486 * 2 ^ 59
def prefixEnd_3626486 : Nat := 4983230072969 + 3 ^ 40 * 3626486 * 2
def baseEnd_3626486 : Nat := 1862130404801003590547101

theorem tailTrace_3626486 : CollatzResearch.WordTrace tailWord_3626486 prefixEnd_3626486 1862130404801003590547101 := by
  unfold tailWord_3626486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266800671241753209036207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88179207159912034229719541 8266800671241753209036207)
  ·
    refine ⟨12400201006862629813554311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8266800671241753209036207 12400201006862629813554311)
    ·
      refine ⟨18600301510293944720331467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12400201006862629813554311 18600301510293944720331467)
      ·
        refine ⟨27900452265440917080497201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18600301510293944720331467 27900452265440917080497201)
        ·
          refine ⟨20925339199080687810372901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27900452265440917080497201 20925339199080687810372901)
          ·
            refine ⟨3923501099827628964444919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20925339199080687810372901 3923501099827628964444919)
            ·
              refine ⟨5885251649741443446667379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923501099827628964444919 5885251649741443446667379)
              ·
                refine ⟨8827877474612165170001069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5885251649741443446667379 8827877474612165170001069)
                ·
                  refine ⟨3310454052979561938750401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8827877474612165170001069 3310454052979561938750401)
                  ·
                    refine ⟨2482840539734671454062801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3310454052979561938750401 2482840539734671454062801)
                    ·
                      refine ⟨1862130404801003590547101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482840539734671454062801 1862130404801003590547101)
                      ·
                        rfl

theorem cell23_3626486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_3626486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626486 prefixEnd_3626486 := by exact prefixLift 3626486
  have htrace : WordTrace (prefixWord ++ tailWord_3626486) baseStart_3626486 baseEnd_3626486 := by
    simpa [prefixWord, tailWord_3626486, baseEnd_3626486] using wordTrace_append hprefix tailTrace_3626486
  have hstable : (prefixWord ++ tailWord_3626486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626486).length < 2 ^ (prefixWord ++ tailWord_3626486).sum := by decide
  have hdescent : baseEnd_3626486 < baseStart_3626486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626536 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3626536 : Nat := 118140960795 + 3626536 * 2 ^ 59
def prefixEnd_3626536 : Nat := 4983230072969 + 3 ^ 40 * 3626536 * 2
def baseEnd_3626536 : Nat := 1862156078833728394921871

theorem tailTrace_3626536 : CollatzResearch.WordTrace tailWord_3626536 prefixEnd_3626536 1862156078833728394921871 := by
  unfold tailWord_3626536
  simp only [CollatzResearch.WordTrace]
  refine ⟨66135317194843454941949731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88180422926457939922599641 66135317194843454941949731)
  ·
    refine ⟨99202975792265182412924597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66135317194843454941949731 99202975792265182412924597)
    ·
      refine ⟨9300278980524860851211681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99202975792265182412924597 9300278980524860851211681)
      ·
        refine ⟨6975209235393645638408761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9300278980524860851211681 6975209235393645638408761)
        ·
          refine ⟨5231406926545234228806571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6975209235393645638408761 5231406926545234228806571)
          ·
            refine ⟨7847110389817851343209857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231406926545234228806571 7847110389817851343209857)
            ·
              refine ⟨5885332792363388507407393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7847110389817851343209857 5885332792363388507407393)
              ·
                refine ⟨4413999594272541380555545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885332792363388507407393 4413999594272541380555545)
                ·
                  refine ⟨3310499695704406035416659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4413999594272541380555545 3310499695704406035416659)
                  ·
                    refine ⟨4965749543556609053124989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3310499695704406035416659 4965749543556609053124989)
                    ·
                      refine ⟨1862156078833728394921871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4965749543556609053124989 1862156078833728394921871)
                      ·
                        rfl

theorem cell23_3626536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3626536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626536 prefixEnd_3626536 := by exact prefixLift 3626536
  have htrace : WordTrace (prefixWord ++ tailWord_3626536) baseStart_3626536 baseEnd_3626536 := by
    simpa [prefixWord, tailWord_3626536, baseEnd_3626536] using wordTrace_append hprefix tailTrace_3626536
  have hstable : (prefixWord ++ tailWord_3626536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626536).length < 2 ^ (prefixWord ++ tailWord_3626536).sum := by decide
  have hdescent : baseEnd_3626536 < baseStart_3626536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626559 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 2, 2, 2]
def baseStart_3626559 : Nat := 118140960795 + 3626559 * 2 ^ 59
def prefixEnd_3626559 : Nat := 4983230072969 + 3 ^ 40 * 3626559 * 2
def baseEnd_3626559 : Nat := 1862167888888781804934265

theorem tailTrace_3626559 : CollatzResearch.WordTrace tailWord_3626559 prefixEnd_3626559 1862167888888781804934265 := by
  unfold tailWord_3626559
  simp only [CollatzResearch.WordTrace]
  refine ⟨132271473268603584811986731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88180982179069056541324487 132271473268603584811986731)
  ·
    refine ⟨198407209902905377217980097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132271473268603584811986731 198407209902905377217980097)
    ·
      refine ⟨148805407427179032913485073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198407209902905377217980097 148805407427179032913485073)
      ·
        refine ⟨111604055570384274685113805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148805407427179032913485073 111604055570384274685113805)
        ·
          refine ⟨41851520838894103006917677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111604055570384274685113805 41851520838894103006917677)
          ·
            refine ⟨15694320314585288627594129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41851520838894103006917677 15694320314585288627594129)
            ·
              refine ⟨11770740235938966470695597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15694320314585288627594129 11770740235938966470695597)
              ·
                refine ⟨4414027588477112426510849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11770740235938966470695597 4414027588477112426510849)
                ·
                  refine ⟨3310520691357834319883137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414027588477112426510849 3310520691357834319883137)
                  ·
                    refine ⟨2482890518518375739912353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3310520691357834319883137 2482890518518375739912353)
                    ·
                      refine ⟨1862167888888781804934265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2482890518518375739912353 1862167888888781804934265)
                      ·
                        rfl

theorem cell23_3626559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_3626559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626559 prefixEnd_3626559 := by exact prefixLift 3626559
  have htrace : WordTrace (prefixWord ++ tailWord_3626559) baseStart_3626559 baseEnd_3626559 := by
    simpa [prefixWord, tailWord_3626559, baseEnd_3626559] using wordTrace_append hprefix tailTrace_3626559
  have hstable : (prefixWord ++ tailWord_3626559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626559).length < 2 ^ (prefixWord ++ tailWord_3626559).sum := by decide
  have hdescent : baseEnd_3626559 < baseStart_3626559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626635 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 3]
def baseStart_3626635 : Nat := 118140960795 + 3626635 * 2 ^ 59
def prefixEnd_3626635 : Nat := 4983230072969 + 3 ^ 40 * 3626635 * 2
def baseEnd_3626635 : Nat := 1862206913418523507583915

theorem tailTrace_3626635 : CollatzResearch.WordTrace tailWord_3626635 prefixEnd_3626635 1862206913418523507583915 := by
  unfold tailWord_3626635
  simp only [CollatzResearch.WordTrace]
  refine ⟨132274245216328249791753359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88182830144218833194502239 132274245216328249791753359)
  ·
    refine ⟨198411367824492374687630039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132274245216328249791753359 198411367824492374687630039)
    ·
      refine ⟨297617051736738562031445059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198411367824492374687630039 297617051736738562031445059)
      ·
        refine ⟨446425577605107843047167589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297617051736738562031445059 446425577605107843047167589)
        ·
          refine ⟨83704795800957720571343923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446425577605107843047167589 83704795800957720571343923)
          ·
            refine ⟨125557193701436580857015885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83704795800957720571343923 125557193701436580857015885)
            ·
              refine ⟨47083947638038717821380957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125557193701436580857015885 47083947638038717821380957)
              ·
                refine ⟨17656480364264519183017859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47083947638038717821380957 17656480364264519183017859)
                ·
                  refine ⟨26484720546396778774526789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17656480364264519183017859 26484720546396778774526789)
                  ·
                    refine ⟨4965885102449396020223773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26484720546396778774526789 4965885102449396020223773)
                    ·
                      refine ⟨1862206913418523507583915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4965885102449396020223773 1862206913418523507583915)
                      ·
                        rfl

theorem cell23_3626635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 3].length) (baseStart_3626635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626635 prefixEnd_3626635 := by exact prefixLift 3626635
  have htrace : WordTrace (prefixWord ++ tailWord_3626635) baseStart_3626635 baseEnd_3626635 := by
    simpa [prefixWord, tailWord_3626635, baseEnd_3626635] using wordTrace_append hprefix tailTrace_3626635
  have hstable : (prefixWord ++ tailWord_3626635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626635).length < 2 ^ (prefixWord ++ tailWord_3626635).sum := by decide
  have hdescent : baseEnd_3626635 < baseStart_3626635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626672 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 6]
def baseStart_3626672 : Nat := 118140960795 + 3626672 * 2 ^ 59
def prefixEnd_3626672 : Nat := 4983230072969 + 3 ^ 40 * 3626672 * 2
def baseEnd_3626672 : Nat := 206913990244748873646805

theorem tailTrace_3626672 : CollatzResearch.WordTrace tailWord_3626672 prefixEnd_3626672 206913990244748873646805 := by
  unfold tailWord_3626672
  simp only [CollatzResearch.WordTrace]
  refine ⟨66137797358597102555425135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88183729811462803407233513 66137797358597102555425135)
  ·
    refine ⟨99206696037895653833137703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66137797358597102555425135 99206696037895653833137703)
    ·
      refine ⟨148810044056843480749706555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99206696037895653833137703 148810044056843480749706555)
      ·
        refine ⟨223215066085265221124559833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148810044056843480749706555 223215066085265221124559833)
        ·
          refine ⟨167411299563948915843419875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223215066085265221124559833 167411299563948915843419875)
          ·
            refine ⟨251116949345923373765129813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167411299563948915843419875 251116949345923373765129813)
            ·
              refine ⟨2942776750147539536310115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 251116949345923373765129813 2942776750147539536310115)
              ·
                refine ⟨4414165125221309304465173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942776750147539536310115 4414165125221309304465173)
                ·
                  refine ⟨206913990244748873646805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4414165125221309304465173 206913990244748873646805)
                  ·
                    rfl

theorem cell23_3626672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 6].length) (baseStart_3626672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626672 prefixEnd_3626672 := by exact prefixLift 3626672
  have htrace : WordTrace (prefixWord ++ tailWord_3626672) baseStart_3626672 baseEnd_3626672 := by
    simpa [prefixWord, tailWord_3626672, baseEnd_3626672] using wordTrace_append hprefix tailTrace_3626672
  have hstable : (prefixWord ++ tailWord_3626672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626672).length < 2 ^ (prefixWord ++ tailWord_3626672).sum := by decide
  have hdescent : baseEnd_3626672 < baseStart_3626672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626710 : List Nat := [5, 2, 1, 3, 1, 1, 1, 4, 1, 4]
def baseStart_3626710 : Nat := 118140960795 + 3626710 * 2 ^ 59
def prefixEnd_3626710 : Nat := 4983230072969 + 3 ^ 40 * 3626710 * 2
def baseEnd_3626710 : Nat := 620748474822536904715357

theorem tailTrace_3626710 : CollatzResearch.WordTrace tailWord_3626710 prefixEnd_3626710 620748474822536904715357 := by
  unfold tailWord_3626710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8267311293191033600045849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88184653794037691733822389 8267311293191033600045849)
  ·
    refine ⟨6200483469893275200034387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8267311293191033600045849 6200483469893275200034387)
    ·
      refine ⟨9300725204839912800051581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6200483469893275200034387 9300725204839912800051581)
      ·
        refine ⟨3487771951814967300019343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9300725204839912800051581 3487771951814967300019343)
        ·
          refine ⟨5231657927722450950029015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487771951814967300019343 5231657927722450950029015)
          ·
            refine ⟨7847486891583676425043523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231657927722450950029015 7847486891583676425043523)
            ·
              refine ⟨11771230337375514637565285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7847486891583676425043523 11771230337375514637565285)
              ·
                refine ⟨2207105688257908994543491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11771230337375514637565285 2207105688257908994543491)
                ·
                  refine ⟨3310658532386863491815237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207105688257908994543491 3310658532386863491815237)
                  ·
                    refine ⟨620748474822536904715357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3310658532386863491815237 620748474822536904715357)
                    ·
                      rfl

theorem cell23_3626710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_3626710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626710 prefixEnd_3626710 := by exact prefixLift 3626710
  have htrace : WordTrace (prefixWord ++ tailWord_3626710) baseStart_3626710 baseEnd_3626710 := by
    simpa [prefixWord, tailWord_3626710, baseEnd_3626710] using wordTrace_append hprefix tailTrace_3626710
  have hstable : (prefixWord ++ tailWord_3626710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626710).length < 2 ^ (prefixWord ++ tailWord_3626710).sum := by decide
  have hdescent : baseEnd_3626710 < baseStart_3626710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626739 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 5, 2, 2]
def baseStart_3626739 : Nat := 118140960795 + 3626739 * 2 ^ 59
def prefixEnd_3626739 : Nat := 4983230072969 + 3 ^ 40 * 3626739 * 2
def baseEnd_3626739 : Nat := 1862260315406591100683437

theorem tailTrace_3626739 : CollatzResearch.WordTrace tailWord_3626739 prefixEnd_3626739 1862260315406591100683437 := by
  unfold tailWord_3626739
  simp only [CollatzResearch.WordTrace]
  refine ⟨132278038407951475553539271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88185358938634317035692847 132278038407951475553539271)
  ·
    refine ⟨198417057611927213330308907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132278038407951475553539271 198417057611927213330308907)
    ·
      refine ⟨297625586417890819995463361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198417057611927213330308907 297625586417890819995463361)
      ·
        refine ⟨223219189813418114996597521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297625586417890819995463361 223219189813418114996597521)
        ·
          refine ⟨167414392360063586247448141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223219189813418114996597521 167414392360063586247448141)
          ·
            refine ⟨62780397135023844842793053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167414392360063586247448141 62780397135023844842793053)
            ·
              refine ⟨23542648925633941816047395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62780397135023844842793053 23542648925633941816047395)
              ·
                refine ⟨35313973388450912724071093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23542648925633941816047395 35313973388450912724071093)
                ·
                  refine ⟨3310685005167273067881665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35313973388450912724071093 3310685005167273067881665)
                  ·
                    refine ⟨2483013753875454800911249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3310685005167273067881665 2483013753875454800911249)
                    ·
                      refine ⟨1862260315406591100683437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483013753875454800911249 1862260315406591100683437)
                      ·
                        rfl

theorem cell23_3626739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 2, 2].length) (baseStart_3626739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626739 prefixEnd_3626739 := by exact prefixLift 3626739
  have htrace : WordTrace (prefixWord ++ tailWord_3626739) baseStart_3626739 baseEnd_3626739 := by
    simpa [prefixWord, tailWord_3626739, baseEnd_3626739] using wordTrace_append hprefix tailTrace_3626739
  have hstable : (prefixWord ++ tailWord_3626739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626739).length < 2 ^ (prefixWord ++ tailWord_3626739).sum := by decide
  have hdescent : baseEnd_3626739 < baseStart_3626739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626750 : List Nat := [4, 2, 2, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_3626750 : Nat := 118140960795 + 3626750 * 2 ^ 59
def prefixEnd_3626750 : Nat := 4983230072969 + 3 ^ 40 * 3626750 * 2
def baseEnd_3626750 : Nat := 1862265963693790557645887

theorem tailTrace_3626750 : CollatzResearch.WordTrace tailWord_3626750 prefixEnd_3626750 1862265963693790557645887 := by
  unfold tailWord_3626750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534804951363953054023713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88185626407274416288126469 16534804951363953054023713)
  ·
    refine ⟨12401103713522964790517785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16534804951363953054023713 12401103713522964790517785)
    ·
      refine ⟨9300827785142223592888339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12401103713522964790517785 9300827785142223592888339)
      ·
        refine ⟨13951241677713335389332509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9300827785142223592888339 13951241677713335389332509)
        ·
          refine ⟨5231715629142500770999691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13951241677713335389332509 5231715629142500770999691)
          ·
            refine ⟨7847573443713751156499537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231715629142500770999691 7847573443713751156499537)
            ·
              refine ⟨5885680082785313367374653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7847573443713751156499537 5885680082785313367374653)
              ·
                refine ⟨2207130031044492512765495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5885680082785313367374653 2207130031044492512765495)
                ·
                  refine ⟨3310695046566738769148243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207130031044492512765495 3310695046566738769148243)
                  ·
                    refine ⟨4966042569850108153722365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3310695046566738769148243 4966042569850108153722365)
                    ·
                      refine ⟨1862265963693790557645887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966042569850108153722365 1862265963693790557645887)
                      ·
                        rfl

theorem cell23_3626750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_3626750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626750 prefixEnd_3626750 := by exact prefixLift 3626750
  have htrace : WordTrace (prefixWord ++ tailWord_3626750) baseStart_3626750 baseEnd_3626750 := by
    simpa [prefixWord, tailWord_3626750, baseEnd_3626750] using wordTrace_append hprefix tailTrace_3626750
  have hstable : (prefixWord ++ tailWord_3626750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626750).length < 2 ^ (prefixWord ++ tailWord_3626750).sum := by decide
  have hdescent : baseEnd_3626750 < baseStart_3626750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626756 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_3626756 : Nat := 118140960795 + 3626756 * 2 ^ 59
def prefixEnd_3626756 : Nat := 4983230072969 + 3 ^ 40 * 3626756 * 2
def baseEnd_3626756 : Nat := 1862269044577717534170859

theorem tailTrace_3626756 : CollatzResearch.WordTrace tailWord_3626756 prefixEnd_3626756 1862269044577717534170859 := by
  unfold tailWord_3626756
  simp only [CollatzResearch.WordTrace]
  refine ⟨66139329224444943728454061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88185772299259924971272081 66139329224444943728454061)
  ·
    refine ⟨24802248459166853898170273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66139329224444943728454061 24802248459166853898170273)
    ·
      refine ⟨18601686344375140423627705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24802248459166853898170273 18601686344375140423627705)
      ·
        refine ⟨13951264758281355317720779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18601686344375140423627705 13951264758281355317720779)
        ·
          refine ⟨20926897137422032976581169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13951264758281355317720779 20926897137422032976581169)
          ·
            refine ⟨15695172853066524732435877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20926897137422032976581169 15695172853066524732435877)
            ·
              refine ⟨2942844909949973387331727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15695172853066524732435877 2942844909949973387331727)
              ·
                refine ⟨4414267364924960080997591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942844909949973387331727 4414267364924960080997591)
                ·
                  refine ⟨6621401047387440121496387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414267364924960080997591 6621401047387440121496387)
                  ·
                    refine ⟨9932101571081160182244581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621401047387440121496387 9932101571081160182244581)
                    ·
                      refine ⟨1862269044577717534170859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9932101571081160182244581 1862269044577717534170859)
                      ·
                        rfl

theorem cell23_3626756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_3626756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626756 prefixEnd_3626756 := by exact prefixLift 3626756
  have htrace : WordTrace (prefixWord ++ tailWord_3626756) baseStart_3626756 baseEnd_3626756 := by
    simpa [prefixWord, tailWord_3626756, baseEnd_3626756] using wordTrace_append hprefix tailTrace_3626756
  have hstable : (prefixWord ++ tailWord_3626756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626756).length < 2 ^ (prefixWord ++ tailWord_3626756).sum := by decide
  have hdescent : baseEnd_3626756 < baseStart_3626756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626773 : List Nat := [1, 3, 2, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_3626773 : Nat := 118140960795 + 3626773 * 2 ^ 59
def prefixEnd_3626773 : Nat := 4983230072969 + 3 ^ 40 * 3626773 * 2
def baseEnd_3626773 : Nat := 1862277773748843967658281

theorem tailTrace_3626773 : CollatzResearch.WordTrace tailWord_3626773 prefixEnd_3626773 1862277773748843967658281 := by
  unfold tailWord_3626773
  simp only [CollatzResearch.WordTrace]
  refine ⟨132279278489828299360276973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88186185659885532906851315 132279278489828299360276973)
  ·
    refine ⟨49604729433685612260103865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132279278489828299360276973 49604729433685612260103865)
    ·
      refine ⟨37203547075264209195077899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49604729433685612260103865 37203547075264209195077899)
      ·
        refine ⟨55805320612896313792616849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37203547075264209195077899 55805320612896313792616849)
        ·
          refine ⟨41853990459672235344462637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55805320612896313792616849 41853990459672235344462637)
          ·
            refine ⟨15695246422377088254173489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41853990459672235344462637 15695246422377088254173489)
            ·
              refine ⟨11771434816782816190630117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15695246422377088254173489 11771434816782816190630117)
              ·
                refine ⟨2207144028146778035743147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11771434816782816190630117 2207144028146778035743147)
                ·
                  refine ⟨3310716042220167053614721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207144028146778035743147 3310716042220167053614721)
                  ·
                    refine ⟨2483037031665125290211041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3310716042220167053614721 2483037031665125290211041)
                    ·
                      refine ⟨1862277773748843967658281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483037031665125290211041 1862277773748843967658281)
                      ·
                        rfl

theorem cell23_3626773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_3626773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626773 prefixEnd_3626773 := by exact prefixLift 3626773
  have htrace : WordTrace (prefixWord ++ tailWord_3626773) baseStart_3626773 baseEnd_3626773 := by
    simpa [prefixWord, tailWord_3626773, baseEnd_3626773] using wordTrace_append hprefix tailTrace_3626773
  have hstable : (prefixWord ++ tailWord_3626773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626773).length < 2 ^ (prefixWord ++ tailWord_3626773).sum := by decide
  have hdescent : baseEnd_3626773 < baseStart_3626773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626789 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_3626789 : Nat := 118140960795 + 3626789 * 2 ^ 59
def prefixEnd_3626789 : Nat := 4983230072969 + 3 ^ 40 * 3626789 * 2
def baseEnd_3626789 : Nat := 1862285989439315905058207

theorem tailTrace_3626789 : CollatzResearch.WordTrace tailWord_3626789 prefixEnd_3626789 1862285989439315905058207 := by
  unfold tailWord_3626789
  simp only [CollatzResearch.WordTrace]
  refine ⟨132279862057770334092859421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88186574705180222728572947 132279862057770334092859421)
  ·
    refine ⟨49604948271663875284822283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132279862057770334092859421 49604948271663875284822283)
    ·
      refine ⟨74407422407495812927233425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49604948271663875284822283 74407422407495812927233425)
      ·
        refine ⟨55805566805621859695425069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74407422407495812927233425 55805566805621859695425069)
        ·
          refine ⟨20927087552108197385784401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55805566805621859695425069 20927087552108197385784401)
          ·
            refine ⟨15695315664081148039338301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20927087552108197385784401 15695315664081148039338301)
            ·
              refine ⟨5885743374030430514751863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15695315664081148039338301 5885743374030430514751863)
              ·
                refine ⟨8828615061045645772127795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5885743374030430514751863 8828615061045645772127795)
                ·
                  refine ⟨13242922591568468658191693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8828615061045645772127795 13242922591568468658191693)
                  ·
                    refine ⟨4966095971838175746821885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13242922591568468658191693 4966095971838175746821885)
                    ·
                      refine ⟨1862285989439315905058207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966095971838175746821885 1862285989439315905058207)
                      ·
                        rfl

theorem cell23_3626789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_3626789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626789 prefixEnd_3626789 := by exact prefixLift 3626789
  have htrace : WordTrace (prefixWord ++ tailWord_3626789) baseStart_3626789 baseEnd_3626789 := by
    simpa [prefixWord, tailWord_3626789, baseEnd_3626789] using wordTrace_append hprefix tailTrace_3626789
  have hstable : (prefixWord ++ tailWord_3626789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626789).length < 2 ^ (prefixWord ++ tailWord_3626789).sum := by decide
  have hdescent : baseEnd_3626789 < baseStart_3626789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626802 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3626802 : Nat := 118140960795 + 3626802 * 2 ^ 59
def prefixEnd_3626802 : Nat := 4983230072969 + 3 ^ 40 * 3626802 * 2
def baseEnd_3626802 : Nat := 1862292664687824354195647

theorem tailTrace_3626802 : CollatzResearch.WordTrace tailWord_3626802 prefixEnd_3626802 1862292664687824354195647 := by
  unfold tailWord_3626802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33070084051680809328270665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88186890804482158208721773 33070084051680809328270665)
  ·
    refine ⟨24802563038760606996202999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33070084051680809328270665 24802563038760606996202999)
    ·
      refine ⟨37203844558140910494304499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24802563038760606996202999 37203844558140910494304499)
      ·
        refine ⟨55805766837211365741456749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37203844558140910494304499 55805766837211365741456749)
        ·
          refine ⟨20927162563954262153046281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55805766837211365741456749 20927162563954262153046281)
          ·
            refine ⟨15695371922965696614784711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20927162563954262153046281 15695371922965696614784711)
            ·
              refine ⟨23543057884448544922177067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15695371922965696614784711 23543057884448544922177067)
              ·
                refine ⟨35314586826672817383265601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23543057884448544922177067 35314586826672817383265601)
                ·
                  refine ⟨26485940120004613037449201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35314586826672817383265601 26485940120004613037449201)
                  ·
                    refine ⟨19864455090003459778086901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26485940120004613037449201 19864455090003459778086901)
                    ·
                      refine ⟨1862292664687824354195647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19864455090003459778086901 1862292664687824354195647)
                      ·
                        rfl

theorem cell23_3626802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3626802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626802 prefixEnd_3626802 := by exact prefixLift 3626802
  have htrace : WordTrace (prefixWord ++ tailWord_3626802) baseStart_3626802 baseEnd_3626802 := by
    simpa [prefixWord, tailWord_3626802, baseEnd_3626802] using wordTrace_append hprefix tailTrace_3626802
  have hstable : (prefixWord ++ tailWord_3626802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626802).length < 2 ^ (prefixWord ++ tailWord_3626802).sum := by decide
  have hdescent : baseEnd_3626802 < baseStart_3626802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626832 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3]
def baseStart_3626832 : Nat := 118140960795 + 3626832 * 2 ^ 59
def prefixEnd_3626832 : Nat := 4983230072969 + 3 ^ 40 * 3626832 * 2
def baseEnd_3626832 : Nat := 1862308069107459236820509

theorem tailTrace_3626832 : CollatzResearch.WordTrace tailWord_3626832 prefixEnd_3626832 1862308069107459236820509 := by
  unfold tailWord_3626832
  simp only [CollatzResearch.WordTrace]
  refine ⟨66140715198307276218337375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88187620264409701624449833 66140715198307276218337375)
  ·
    refine ⟨99211072797460914327506063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66140715198307276218337375 99211072797460914327506063)
    ·
      refine ⟨148816609196191371491259095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99211072797460914327506063 148816609196191371491259095)
      ·
        refine ⟨223224913794287057236888643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148816609196191371491259095 223224913794287057236888643)
        ·
          refine ⟨334837370691430585855332965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223224913794287057236888643 334837370691430585855332965)
          ·
            refine ⟨62782007004643234847874931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334837370691430585855332965 62782007004643234847874931)
            ·
              refine ⟨94173010506964852271812397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62782007004643234847874931 94173010506964852271812397)
              ·
                refine ⟨35314878940111819601929649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94173010506964852271812397 35314878940111819601929649)
                ·
                  refine ⟨26486159205083864701447237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35314878940111819601929649 26486159205083864701447237)
                  ·
                    refine ⟨4966154850953224631521357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26486159205083864701447237 4966154850953224631521357)
                    ·
                      refine ⟨1862308069107459236820509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966154850953224631521357 1862308069107459236820509)
                      ·
                        rfl

theorem cell23_3626832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_3626832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626832 prefixEnd_3626832 := by exact prefixLift 3626832
  have htrace : WordTrace (prefixWord ++ tailWord_3626832) baseStart_3626832 baseEnd_3626832 := by
    simpa [prefixWord, tailWord_3626832, baseEnd_3626832] using wordTrace_append hprefix tailTrace_3626832
  have hstable : (prefixWord ++ tailWord_3626832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626832).length < 2 ^ (prefixWord ++ tailWord_3626832).sum := by decide
  have hdescent : baseEnd_3626832 < baseStart_3626832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626842 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4]
def baseStart_3626842 : Nat := 118140960795 + 3626842 * 2 ^ 59
def prefixEnd_3626842 : Nat := 4983230072969 + 3 ^ 40 * 3626842 * 2
def baseEnd_3626842 : Nat := 1862313203914004197695463

theorem tailTrace_3626842 : CollatzResearch.WordTrace tailWord_3626842 prefixEnd_3626842 1862313203914004197695463 := by
  unfold tailWord_3626842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33070448781644581036134695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88187863417718882763025853 33070448781644581036134695)
  ·
    refine ⟨49605673172466871554202043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33070448781644581036134695 49605673172466871554202043)
    ·
      refine ⟨74408509758700307331303065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49605673172466871554202043 74408509758700307331303065)
      ·
        refine ⟨55806382319025230498477299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74408509758700307331303065 55806382319025230498477299)
        ·
          refine ⟨83709573478537845747715949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55806382319025230498477299 83709573478537845747715949)
          ·
            refine ⟨31391090054451692155393481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83709573478537845747715949 31391090054451692155393481)
            ·
              refine ⟨23543317540838769116545111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31391090054451692155393481 23543317540838769116545111)
              ·
                refine ⟨35314976311258153674817667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23543317540838769116545111 35314976311258153674817667)
                ·
                  refine ⟨52972464466887230512226501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35314976311258153674817667 52972464466887230512226501)
                  ·
                    refine ⟨9932337087541355721042469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52972464466887230512226501 9932337087541355721042469)
                    ·
                      refine ⟨1862313203914004197695463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9932337087541355721042469 1862313203914004197695463)
                      ·
                        rfl

theorem cell23_3626842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_3626842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626842 prefixEnd_3626842 := by exact prefixLift 3626842
  have htrace : WordTrace (prefixWord ++ tailWord_3626842) baseStart_3626842 baseEnd_3626842 := by
    simpa [prefixWord, tailWord_3626842, baseEnd_3626842] using wordTrace_append hprefix tailTrace_3626842
  have hstable : (prefixWord ++ tailWord_3626842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626842).length < 2 ^ (prefixWord ++ tailWord_3626842).sum := by decide
  have hdescent : baseEnd_3626842 < baseStart_3626842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626850 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_3626850 : Nat := 118140960795 + 3626850 * 2 ^ 59
def prefixEnd_3626850 : Nat := 4983230072969 + 3 ^ 40 * 3626850 * 2
def baseEnd_3626850 : Nat := 1862317311759240166395427

theorem tailTrace_3626850 : CollatzResearch.WordTrace tailWord_3626850 prefixEnd_3626850 1862317311759240166395427 := by
  unfold tailWord_3626850
  simp only [CollatzResearch.WordTrace]
  refine ⟨33070521727637335377707501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88188057940366227673886669 33070521727637335377707501)
  ·
    refine ⟨12401445647864000766640313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33070521727637335377707501 12401445647864000766640313)
    ·
      refine ⟨9301084235898000574980235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12401445647864000766640313 9301084235898000574980235)
      ·
        refine ⟨13951626353847000862470353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9301084235898000574980235 13951626353847000862470353)
        ·
          refine ⟨10463719765385250646852765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13951626353847000862470353 10463719765385250646852765)
          ·
            refine ⟨3923894912019468992569787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10463719765385250646852765 3923894912019468992569787)
            ·
              refine ⟨5885842368029203488854681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923894912019468992569787 5885842368029203488854681)
              ·
                refine ⟨4414381776021902616641011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5885842368029203488854681 4414381776021902616641011)
                ·
                  refine ⟨6621572664032853924961517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414381776021902616641011 6621572664032853924961517)
                  ·
                    refine ⟨2483089749012320221860569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6621572664032853924961517 2483089749012320221860569)
                    ·
                      refine ⟨1862317311759240166395427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483089749012320221860569 1862317311759240166395427)
                      ·
                        rfl

theorem cell23_3626850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_3626850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626850 prefixEnd_3626850 := by exact prefixLift 3626850
  have htrace : WordTrace (prefixWord ++ tailWord_3626850) baseStart_3626850 baseEnd_3626850 := by
    simpa [prefixWord, tailWord_3626850, baseEnd_3626850] using wordTrace_append hprefix tailTrace_3626850
  have hstable : (prefixWord ++ tailWord_3626850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626850).length < 2 ^ (prefixWord ++ tailWord_3626850).sum := by decide
  have hdescent : baseEnd_3626850 < baseStart_3626850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626889 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 1, 7, 2]
def baseStart_3626889 : Nat := 118140960795 + 3626889 * 2 ^ 59
def prefixEnd_3626889 : Nat := 4983230072969 + 3 ^ 40 * 3626889 * 2
def baseEnd_3626889 : Nat := 1862337337504765513807747

theorem tailTrace_3626889 : CollatzResearch.WordTrace tailWord_3626889 prefixEnd_3626889 1862337337504765513807747 := by
  unfold tailWord_3626889
  simp only [CollatzResearch.WordTrace]
  refine ⟨132283509357408051171499721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88189006238272034114333147 132283509357408051171499721)
  ·
    refine ⟨99212632018056038378624791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132283509357408051171499721 99212632018056038378624791)
    ·
      refine ⟨148818948027084057567937187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99212632018056038378624791 148818948027084057567937187)
      ·
        refine ⟨223228422040626086351905781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148818948027084057567937187 223228422040626086351905781)
        ·
          refine ⟨20927664566308695595491167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223228422040626086351905781 20927664566308695595491167)
          ·
            refine ⟨31391496849463043393236751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20927664566308695595491167 31391496849463043393236751)
            ·
              refine ⟨47087245274194565089855127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31391496849463043393236751 47087245274194565089855127)
              ·
                refine ⟨70630867911291847634782691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47087245274194565089855127 70630867911291847634782691)
                ·
                  refine ⟨105946301866937771452174037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70630867911291847634782691 105946301866937771452174037)
                  ·
                    refine ⟨2483116450006354018410329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 105946301866937771452174037 2483116450006354018410329)
                    ·
                      refine ⟨1862337337504765513807747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483116450006354018410329 1862337337504765513807747)
                      ·
                        rfl

theorem cell23_3626889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 7, 2].length) (baseStart_3626889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626889 prefixEnd_3626889 := by exact prefixLift 3626889
  have htrace : WordTrace (prefixWord ++ tailWord_3626889) baseStart_3626889 baseEnd_3626889 := by
    simpa [prefixWord, tailWord_3626889, baseEnd_3626889] using wordTrace_append hprefix tailTrace_3626889
  have hstable : (prefixWord ++ tailWord_3626889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626889).length < 2 ^ (prefixWord ++ tailWord_3626889).sum := by decide
  have hdescent : baseEnd_3626889 < baseStart_3626889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626916 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 2, 5]
def baseStart_3626916 : Nat := 118140960795 + 3626916 * 2 ^ 59
def prefixEnd_3626916 : Nat := 4983230072969 + 3 ^ 40 * 3626916 * 2
def baseEnd_3626916 : Nat := 620783733827478969390041

theorem tailTrace_3626916 : CollatzResearch.WordTrace tailWord_3626916 prefixEnd_3626916 620783733827478969390041 := by
  unfold tailWord_3626916
  simp only [CollatzResearch.WordTrace]
  refine ⟨66142247064155117391366301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88189662752206823188488401 66142247064155117391366301)
  ·
    refine ⟨24803342649058169021762363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66142247064155117391366301 24803342649058169021762363)
    ·
      refine ⟨37205013973587253532643545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24803342649058169021762363 37205013973587253532643545)
      ·
        refine ⟨27903760480190440149482659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37205013973587253532643545 27903760480190440149482659)
        ·
          refine ⟨41855640720285660224223989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27903760480190440149482659 41855640720285660224223989)
          ·
            refine ⟨3923966317526780646020999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41855640720285660224223989 3923966317526780646020999)
            ·
              refine ⟨5885949476290170969031499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3923966317526780646020999 5885949476290170969031499)
              ·
                refine ⟨8828924214435256453547249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5885949476290170969031499 8828924214435256453547249)
                ·
                  refine ⟨6621693160826442340160437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8828924214435256453547249 6621693160826442340160437)
                  ·
                    refine ⟨620783733827478969390041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6621693160826442340160437 620783733827478969390041)
                    ·
                      rfl

theorem cell23_3626916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_3626916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626916 prefixEnd_3626916 := by exact prefixLift 3626916
  have htrace : WordTrace (prefixWord ++ tailWord_3626916) baseStart_3626916 baseEnd_3626916 := by
    simpa [prefixWord, tailWord_3626916, baseEnd_3626916] using wordTrace_append hprefix tailTrace_3626916
  have hstable : (prefixWord ++ tailWord_3626916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626916).length < 2 ^ (prefixWord ++ tailWord_3626916).sum := by decide
  have hdescent : baseEnd_3626916 < baseStart_3626916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3626920 : List Nat := [2, 1, 6, 2, 1, 1, 2, 3, 5]
def baseStart_3626920 : Nat := 118140960795 + 3626920 * 2 ^ 59
def prefixEnd_3626920 : Nat := 4983230072969 + 3 ^ 40 * 3626920 * 2
def baseEnd_3626920 : Nat := 206928139489450543613345

theorem tailTrace_3626920 : CollatzResearch.WordTrace tailWord_3626920 prefixEnd_3626920 206928139489450543613345 := by
  unfold tailWord_3626920
  simp only [CollatzResearch.WordTrace]
  refine ⟨66142320010147871732939107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88189760013530495643918809 66142320010147871732939107)
  ·
    refine ⟨99213480015221807599408661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66142320010147871732939107 99213480015221807599408661)
    ·
      refine ⟨4650631875713522231222281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99213480015221807599408661 4650631875713522231222281)
      ·
        refine ⟨3487973906785141673416711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4650631875713522231222281 3487973906785141673416711)
        ·
          refine ⟨5231960860177712510125067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487973906785141673416711 5231960860177712510125067)
          ·
            refine ⟨7847941290266568765187601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231960860177712510125067 7847941290266568765187601)
            ·
              refine ⟨5885955967699926573890701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7847941290266568765187601 5885955967699926573890701)
              ·
                refine ⟨2207233487887472465209013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5885955967699926573890701 2207233487887472465209013)
                ·
                  refine ⟨206928139489450543613345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2207233487887472465209013 206928139489450543613345)
                  ·
                    rfl

theorem cell23_3626920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 5].length) (baseStart_3626920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3626920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3626920 prefixEnd_3626920 := by exact prefixLift 3626920
  have htrace : WordTrace (prefixWord ++ tailWord_3626920) baseStart_3626920 baseEnd_3626920 := by
    simpa [prefixWord, tailWord_3626920, baseEnd_3626920] using wordTrace_append hprefix tailTrace_3626920
  have hstable : (prefixWord ++ tailWord_3626920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3626920).length < 2 ^ (prefixWord ++ tailWord_3626920).sum := by decide
  have hdescent : baseEnd_3626920 < baseStart_3626920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3626920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627003 : List Nat := [1, 1, 1, 1, 1, 3, 4, 6, 1, 1, 3]
def baseStart_3627003 : Nat := 118140960795 + 3627003 * 2 ^ 59
def prefixEnd_3627003 : Nat := 4983230072969 + 3 ^ 40 * 3627003 * 2
def baseEnd_3627003 : Nat := 1862395874299378067782223

theorem tailTrace_3627003 : CollatzResearch.WordTrace tailWord_3627003 prefixEnd_3627003 1862395874299378067782223 := by
  unfold tailWord_3627003
  simp only [CollatzResearch.WordTrace]
  refine ⟨132287667278995048641149663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88191778185996699094099775 132287667278995048641149663)
  ·
    refine ⟨198431500918492572961724495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132287667278995048641149663 198431500918492572961724495)
    ·
      refine ⟨297647251377738859442586743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198431500918492572961724495 297647251377738859442586743)
      ·
        refine ⟨446470877066608289163880115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297647251377738859442586743 446470877066608289163880115)
        ·
          refine ⟨669706315599912433745820173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446470877066608289163880115 669706315599912433745820173)
          ·
            refine ⟨251139868349967162654682565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 669706315599912433745820173 251139868349967162654682565)
            ·
              refine ⟨47088725315618842997752981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251139868349967162654682565 47088725315618842997752981)
              ·
                refine ⟨2207283999169633265519671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47088725315618842997752981 2207283999169633265519671)
                ·
                  refine ⟨3310925998754449898279507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207283999169633265519671 3310925998754449898279507)
                  ·
                    refine ⟨4966388998131674847419261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3310925998754449898279507 4966388998131674847419261)
                    ·
                      refine ⟨1862395874299378067782223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966388998131674847419261 1862395874299378067782223)
                      ·
                        rfl

theorem cell23_3627003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 1, 1, 3].length) (baseStart_3627003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627003 prefixEnd_3627003 := by exact prefixLift 3627003
  have htrace : WordTrace (prefixWord ++ tailWord_3627003) baseStart_3627003 baseEnd_3627003 := by
    simpa [prefixWord, tailWord_3627003, baseEnd_3627003] using wordTrace_append hprefix tailTrace_3627003
  have hstable : (prefixWord ++ tailWord_3627003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627003).length < 2 ^ (prefixWord ++ tailWord_3627003).sum := by decide
  have hdescent : baseEnd_3627003 < baseStart_3627003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627019 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 1, 6]
def baseStart_3627019 : Nat := 118140960795 + 3627019 * 2 ^ 59
def prefixEnd_3627019 : Nat := 4983230072969 + 3 ^ 40 * 3627019 * 2
def baseEnd_3627019 : Nat := 620801363329950001727383

theorem tailTrace_3627019 : CollatzResearch.WordTrace tailWord_3627019 prefixEnd_3627019 620801363329950001727383 := by
  unfold tailWord_3627019
  simp only [CollatzResearch.WordTrace]
  refine ⟨132288250846937083373732111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88192167231291388915821407 132288250846937083373732111)
  ·
    refine ⟨198432376270405625060598167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132288250846937083373732111 198432376270405625060598167)
    ·
      refine ⟨297648564405608437590897251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198432376270405625060598167 297648564405608437590897251)
      ·
        refine ⟨446472846608412656386345877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297648564405608437590897251 446472846608412656386345877)
        ·
          refine ⟨20928414684769343268109963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446472846608412656386345877 20928414684769343268109963)
          ·
            refine ⟨31392622027154014902164945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20928414684769343268109963 31392622027154014902164945)
            ·
              refine ⟨23544466520365511176623709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31392622027154014902164945 23544466520365511176623709)
              ·
                refine ⟨8829174945137066691233891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23544466520365511176623709 8829174945137066691233891)
                ·
                  refine ⟨13243762417705600036850837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829174945137066691233891 13243762417705600036850837)
                  ·
                    refine ⟨620801363329950001727383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13243762417705600036850837 620801363329950001727383)
                    ·
                      rfl

theorem cell23_3627019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 6].length) (baseStart_3627019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627019 prefixEnd_3627019 := by exact prefixLift 3627019
  have htrace : WordTrace (prefixWord ++ tailWord_3627019) baseStart_3627019 baseEnd_3627019 := by
    simpa [prefixWord, tailWord_3627019, baseEnd_3627019] using wordTrace_append hprefix tailTrace_3627019
  have hstable : (prefixWord ++ tailWord_3627019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627019).length < 2 ^ (prefixWord ++ tailWord_3627019).sum := by decide
  have hdescent : baseEnd_3627019 < baseStart_3627019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627036 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 1, 6]
def baseStart_3627036 : Nat := 118140960795 + 3627036 * 2 ^ 59
def prefixEnd_3627036 : Nat := 4983230072969 + 3 ^ 40 * 3627036 * 2
def baseEnd_3627036 : Nat := 620804273053658812889857

theorem tailTrace_3627036 : CollatzResearch.WordTrace tailWord_3627036 prefixEnd_3627036 620804273053658812889857 := by
  unfold tailWord_3627036
  simp only [CollatzResearch.WordTrace]
  refine ⟨66144435443937747638550481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88192580591916996851400641 66144435443937747638550481)
  ·
    refine ⟨49608326582953310728912861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66144435443937747638550481 49608326582953310728912861)
    ·
      refine ⟨18603122468607491523342323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49608326582953310728912861 18603122468607491523342323)
      ·
        refine ⟨27904683702911237285013485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18603122468607491523342323 27904683702911237285013485)
        ·
          refine ⟨10464256388591713981880057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27904683702911237285013485 10464256388591713981880057)
          ·
            refine ⟨7848192291443785486410043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10464256388591713981880057 7848192291443785486410043)
            ·
              refine ⟨11772288437165678229615065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848192291443785486410043 11772288437165678229615065)
              ·
                refine ⟨8829216327874258672211299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11772288437165678229615065 8829216327874258672211299)
                ·
                  refine ⟨13243824491811388008316949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829216327874258672211299 13243824491811388008316949)
                  ·
                    refine ⟨620804273053658812889857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13243824491811388008316949 620804273053658812889857)
                    ·
                      rfl

theorem cell23_3627036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_3627036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627036 prefixEnd_3627036 := by exact prefixLift 3627036
  have htrace : WordTrace (prefixWord ++ tailWord_3627036) baseStart_3627036 baseEnd_3627036 := by
    simpa [prefixWord, tailWord_3627036, baseEnd_3627036] using wordTrace_append hprefix tailTrace_3627036
  have hstable : (prefixWord ++ tailWord_3627036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627036).length < 2 ^ (prefixWord ++ tailWord_3627036).sum := by decide
  have hdescent : baseEnd_3627036 < baseStart_3627036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627043 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 1, 1, 4]
def baseStart_3627043 : Nat := 118140960795 + 3627043 * 2 ^ 59
def prefixEnd_3627043 : Nat := 4983230072969 + 3 ^ 40 * 3627043 * 2
def baseEnd_3627043 : Nat := 1862416413525557911282039

theorem tailTrace_3627043 : CollatzResearch.WordTrace tailWord_3627043 prefixEnd_3627043 1862416413525557911282039 := by
  unfold tailWord_3627043
  simp only [CollatzResearch.WordTrace]
  refine ⟨132289126198850135472605783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88192750799233423648403855 132289126198850135472605783)
  ·
    refine ⟨198433689298275203208908675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132289126198850135472605783 198433689298275203208908675)
    ·
      refine ⟨297650533947412804813363013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198433689298275203208908675 297650533947412804813363013)
      ·
        refine ⟨55809475115139900902505565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297650533947412804813363013 55809475115139900902505565)
        ·
          refine ⟨20928553168177462838439587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55809475115139900902505565 20928553168177462838439587)
          ·
            refine ⟨31392829752266194257659381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20928553168177462838439587 31392829752266194257659381)
            ·
              refine ⟨2943077789274955711655567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31392829752266194257659381 2943077789274955711655567)
              ·
                refine ⟨4414616683912433567483351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943077789274955711655567 4414616683912433567483351)
                ·
                  refine ⟨6621925025868650351225027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414616683912433567483351 6621925025868650351225027)
                  ·
                    refine ⟨9932887538802975526837541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6621925025868650351225027 9932887538802975526837541)
                    ·
                      refine ⟨1862416413525557911282039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9932887538802975526837541 1862416413525557911282039)
                      ·
                        rfl

theorem cell23_3627043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_3627043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627043 prefixEnd_3627043 := by exact prefixLift 3627043
  have htrace : WordTrace (prefixWord ++ tailWord_3627043) baseStart_3627043 baseEnd_3627043 := by
    simpa [prefixWord, tailWord_3627043, baseEnd_3627043] using wordTrace_append hprefix tailTrace_3627043
  have hstable : (prefixWord ++ tailWord_3627043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627043).length < 2 ^ (prefixWord ++ tailWord_3627043).sum := by decide
  have hdescent : baseEnd_3627043 < baseStart_3627043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627054 : List Nat := [4, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_3627054 : Nat := 118140960795 + 3627054 * 2 ^ 59
def prefixEnd_3627054 : Nat := 4983230072969 + 3 ^ 40 * 3627054 * 2
def baseEnd_3627054 : Nat := 1862422061812757368244489

theorem tailTrace_3627054 : CollatzResearch.WordTrace tailWord_3627054 prefixEnd_3627054 1862422061812757368244489 := by
  unfold tailWord_3627054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16536190925226285543907027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88193018267873522900837477 16536190925226285543907027)
  ·
    refine ⟨24804286387839428315860541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16536190925226285543907027 24804286387839428315860541)
    ·
      refine ⟨9301607395439785618447703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24804286387839428315860541 9301607395439785618447703)
      ·
        refine ⟨13952411093159678427671555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9301607395439785618447703 13952411093159678427671555)
        ·
          refine ⟨20928616639739517641507333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13952411093159678427671555 20928616639739517641507333)
          ·
            refine ⟨3924115619951159557782625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20928616639739517641507333 3924115619951159557782625)
            ·
              refine ⟨2943086714963369668336969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924115619951159557782625 2943086714963369668336969)
              ·
                refine ⟨2207315036222527251252727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943086714963369668336969 2207315036222527251252727)
                ·
                  refine ⟨3310972554333790876879091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207315036222527251252727 3310972554333790876879091)
                  ·
                    refine ⟨4966458831500686315318637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3310972554333790876879091 4966458831500686315318637)
                    ·
                      refine ⟨1862422061812757368244489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966458831500686315318637 1862422061812757368244489)
                      ·
                        rfl

theorem cell23_3627054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_3627054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627054 prefixEnd_3627054 := by exact prefixLift 3627054
  have htrace : WordTrace (prefixWord ++ tailWord_3627054) baseStart_3627054 baseEnd_3627054 := by
    simpa [prefixWord, tailWord_3627054, baseEnd_3627054] using wordTrace_append hprefix tailTrace_3627054
  have hstable : (prefixWord ++ tailWord_3627054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627054).length < 2 ^ (prefixWord ++ tailWord_3627054).sum := by decide
  have hdescent : baseEnd_3627054 < baseStart_3627054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627073 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_3627073 : Nat := 118140960795 + 3627073 * 2 ^ 59
def prefixEnd_3627073 : Nat := 4983230072969 + 3 ^ 40 * 3627073 * 2
def baseEnd_3627073 : Nat := 1862431817945192793906901

theorem tailTrace_3627073 : CollatzResearch.WordTrace tailWord_3627073 prefixEnd_3627073 1862431817945192793906901 := by
  unfold tailWord_3627073
  simp only [CollatzResearch.WordTrace]
  refine ⟨132290220388741450596197873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88193480259160967064131915 132290220388741450596197873)
  ·
    refine ⟨99217665291556087947148405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132290220388741450596197873 99217665291556087947148405)
    ·
      refine ⟨9301656121083383245045163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99217665291556087947148405 9301656121083383245045163)
      ·
        refine ⟨13952484181625074867567745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9301656121083383245045163 13952484181625074867567745)
        ·
          refine ⟨10464363136218806150675809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13952484181625074867567745 10464363136218806150675809)
          ·
            refine ⟨7848272352164104613006857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10464363136218806150675809 7848272352164104613006857)
            ·
              refine ⟨5886204264123078459755143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7848272352164104613006857 5886204264123078459755143)
              ·
                refine ⟨8829306396184617689632715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886204264123078459755143 8829306396184617689632715)
                ·
                  refine ⟨13243959594276926534449073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8829306396184617689632715 13243959594276926534449073)
                  ·
                    refine ⟨9932969695707694900836805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13243959594276926534449073 9932969695707694900836805)
                    ·
                      refine ⟨1862431817945192793906901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9932969695707694900836805 1862431817945192793906901)
                      ·
                        rfl

theorem cell23_3627073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_3627073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627073 prefixEnd_3627073 := by exact prefixLift 3627073
  have htrace : WordTrace (prefixWord ++ tailWord_3627073) baseStart_3627073 baseEnd_3627073 := by
    simpa [prefixWord, tailWord_3627073, baseEnd_3627073] using wordTrace_append hprefix tailTrace_3627073
  have hstable : (prefixWord ++ tailWord_3627073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627073).length < 2 ^ (prefixWord ++ tailWord_3627073).sum := by decide
  have hdescent : baseEnd_3627073 < baseStart_3627073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627079 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 2, 7]
def baseStart_3627079 : Nat := 118140960795 + 3627079 * 2 ^ 59
def prefixEnd_3627079 : Nat := 4983230072969 + 3 ^ 40 * 3627079 * 2
def baseEnd_3627079 : Nat := 620811632943039923477291

theorem tailTrace_3627079 : CollatzResearch.WordTrace tailWord_3627079 prefixEnd_3627079 620811632943039923477291 := by
  unfold tailWord_3627079
  simp only [CollatzResearch.WordTrace]
  refine ⟨132290439226719713620916291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88193626151146475747277527 132290439226719713620916291)
  ·
    refine ⟨198435658840079570431374437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132290439226719713620916291 198435658840079570431374437)
    ·
      refine ⟨37206686032514919455882707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198435658840079570431374437 37206686032514919455882707)
      ·
        refine ⟨55810029048772379183824061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37206686032514919455882707 55810029048772379183824061)
        ·
          refine ⟨20928760893289642193934023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55810029048772379183824061 20928760893289642193934023)
          ·
            refine ⟨31393141339934463290901035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20928760893289642193934023 31393141339934463290901035)
            ·
              refine ⟨47089712009901694936351553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31393141339934463290901035 47089712009901694936351553)
              ·
                refine ⟨35317284007426271202263665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47089712009901694936351553 35317284007426271202263665)
                ·
                  refine ⟨26487963005569703401697749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35317284007426271202263665 26487963005569703401697749)
                  ·
                    refine ⟨620811632943039923477291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26487963005569703401697749 620811632943039923477291)
                    ·
                      rfl

theorem cell23_3627079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_3627079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627079 prefixEnd_3627079 := by exact prefixLift 3627079
  have htrace : WordTrace (prefixWord ++ tailWord_3627079) baseStart_3627079 baseEnd_3627079 := by
    simpa [prefixWord, tailWord_3627079, baseEnd_3627079] using wordTrace_append hprefix tailTrace_3627079
  have hstable : (prefixWord ++ tailWord_3627079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627079).length < 2 ^ (prefixWord ++ tailWord_3627079).sum := by decide
  have hdescent : baseEnd_3627079 < baseStart_3627079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627089 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3627089 : Nat := 118140960795 + 3627089 * 2 ^ 59
def prefixEnd_3627089 : Nat := 4983230072969 + 3 ^ 40 * 3627089 * 2
def baseEnd_3627089 : Nat := 1862440033635664731306827

theorem tailTrace_3627089 : CollatzResearch.WordTrace tailWord_3627089 prefixEnd_3627089 1862440033635664731306827 := by
  unfold tailWord_3627089
  simp only [CollatzResearch.WordTrace]
  refine ⟨132290803956683485328780321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88193869304455656885853547 132290803956683485328780321)
  ·
    refine ⟨99218102967512613996585241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132290803956683485328780321 99218102967512613996585241)
    ·
      refine ⟨74413577225634460497438931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99218102967512613996585241 74413577225634460497438931)
      ·
        refine ⟨111620365838451690746158397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74413577225634460497438931 111620365838451690746158397)
        ·
          refine ⟨41857637189419384029809399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111620365838451690746158397 41857637189419384029809399)
          ·
            refine ⟨62786455784129076044714099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41857637189419384029809399 62786455784129076044714099)
            ·
              refine ⟨94179683676193614067071149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62786455784129076044714099 94179683676193614067071149)
              ·
                refine ⟨35317381378572605275151681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94179683676193614067071149 35317381378572605275151681)
                ·
                  refine ⟨26488036033929453956363761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35317381378572605275151681 26488036033929453956363761)
                  ·
                    refine ⟨19866027025447090467272821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26488036033929453956363761 19866027025447090467272821)
                    ·
                      refine ⟨1862440033635664731306827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19866027025447090467272821 1862440033635664731306827)
                      ·
                        rfl

theorem cell23_3627089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3627089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627089 prefixEnd_3627089 := by exact prefixLift 3627089
  have htrace : WordTrace (prefixWord ++ tailWord_3627089) baseStart_3627089 baseEnd_3627089 := by
    simpa [prefixWord, tailWord_3627089, baseEnd_3627089] using wordTrace_append hprefix tailTrace_3627089
  have hstable : (prefixWord ++ tailWord_3627089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627089).length < 2 ^ (prefixWord ++ tailWord_3627089).sum := by decide
  have hdescent : baseEnd_3627089 < baseStart_3627089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627094 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_3627094 : Nat := 118140960795 + 3627094 * 2 ^ 59
def prefixEnd_3627094 : Nat := 4983230072969 + 3 ^ 40 * 3627094 * 2
def baseEnd_3627094 : Nat := 1862442601038937211744305

theorem tailTrace_3627094 : CollatzResearch.WordTrace tailWord_3627094 prefixEnd_3627094 1862442601038937211744305 := by
  unfold tailWord_3627094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8268186645104085698919521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88193990881110247455141557 8268186645104085698919521)
  ·
    refine ⟨6201139983828064274189641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8268186645104085698919521 6201139983828064274189641)
    ·
      refine ⟨4650854987871048205642231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6201139983828064274189641 4650854987871048205642231)
      ·
        refine ⟨6976282481806572308463347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650854987871048205642231 6976282481806572308463347)
        ·
          refine ⟨10464423722709858462695021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976282481806572308463347 10464423722709858462695021)
          ·
            refine ⟨3924158896016196923510633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10464423722709858462695021 3924158896016196923510633)
            ·
              refine ⟨2943119172012147692632975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924158896016196923510633 2943119172012147692632975)
              ·
                refine ⟨4414678758018221538949463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943119172012147692632975 4414678758018221538949463)
                ·
                  refine ⟨6622018137027332308424195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414678758018221538949463 6622018137027332308424195)
                  ·
                    refine ⟨9933027205540998462636293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6622018137027332308424195 9933027205540998462636293)
                    ·
                      refine ⟨1862442601038937211744305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9933027205540998462636293 1862442601038937211744305)
                      ·
                        rfl

theorem cell23_3627094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_3627094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627094 prefixEnd_3627094 := by exact prefixLift 3627094
  have htrace : WordTrace (prefixWord ++ tailWord_3627094) baseStart_3627094 baseEnd_3627094 := by
    simpa [prefixWord, tailWord_3627094, baseEnd_3627094] using wordTrace_append hprefix tailTrace_3627094
  have hstable : (prefixWord ++ tailWord_3627094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627094).length < 2 ^ (prefixWord ++ tailWord_3627094).sum := by decide
  have hdescent : baseEnd_3627094 < baseStart_3627094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627137 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_3627137 : Nat := 118140960795 + 3627137 * 2 ^ 59
def prefixEnd_3627137 : Nat := 4983230072969 + 3 ^ 40 * 3627137 * 2
def baseEnd_3627137 : Nat := 1862464680707080543506607

theorem tailTrace_3627137 : CollatzResearch.WordTrace tailWord_3627137 prefixEnd_3627137 1862464680707080543506607 := by
  unfold tailWord_3627137
  simp only [CollatzResearch.WordTrace]
  refine ⟨132292554660509589526527665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88195036440339726351018443 132292554660509589526527665)
  ·
    refine ⟨99219415995382192144895749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132292554660509589526527665 99219415995382192144895749)
    ·
      refine ⟨18603640499134161027167953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99219415995382192144895749 18603640499134161027167953)
      ·
        refine ⟨13952730374350620770375965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18603640499134161027167953 13952730374350620770375965)
        ·
          refine ⟨5232273890381482788890987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13952730374350620770375965 5232273890381482788890987)
          ·
            refine ⟨7848410835572224183336481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232273890381482788890987 7848410835572224183336481)
            ·
              refine ⟨5886308126679168137502361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7848410835572224183336481 5886308126679168137502361)
              ·
                refine ⟨4414731095009376103126771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886308126679168137502361 4414731095009376103126771)
                ·
                  refine ⟨6622096642514064154690157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414731095009376103126771 6622096642514064154690157)
                  ·
                    refine ⟨2483286240942774058008809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6622096642514064154690157 2483286240942774058008809)
                    ·
                      refine ⟨1862464680707080543506607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483286240942774058008809 1862464680707080543506607)
                      ·
                        rfl

theorem cell23_3627137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_3627137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627137 prefixEnd_3627137 := by exact prefixLift 3627137
  have htrace : WordTrace (prefixWord ++ tailWord_3627137) baseStart_3627137 baseEnd_3627137 := by
    simpa [prefixWord, tailWord_3627137, baseEnd_3627137] using wordTrace_append hprefix tailTrace_3627137
  have hstable : (prefixWord ++ tailWord_3627137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627137).length < 2 ^ (prefixWord ++ tailWord_3627137).sum := by decide
  have hdescent : baseEnd_3627137 < baseStart_3627137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627186 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3627186 : Nat := 118140960795 + 3627186 * 2 ^ 59
def prefixEnd_3627186 : Nat := 4983230072969 + 3 ^ 40 * 3627186 * 2
def baseEnd_3627186 : Nat := 620829947086383617264627

theorem tailTrace_3627186 : CollatzResearch.WordTrace tailWord_3627186 prefixEnd_3627186 620829947086383617264627 := by
  unfold tailWord_3627186
  simp only [CollatzResearch.WordTrace]
  refine ⟨33073585459333017723765353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88196227891554713930040941 33073585459333017723765353)
  ·
    refine ⟨24805189094499763292824015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33073585459333017723765353 24805189094499763292824015)
    ·
      refine ⟨37207783641749644939236023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24805189094499763292824015 37207783641749644939236023)
      ·
        refine ⟨55811675462624467408854035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37207783641749644939236023 55811675462624467408854035)
        ·
          refine ⟨83717513193936701113281053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55811675462624467408854035 83717513193936701113281053)
          ·
            refine ⟨31394067447726262917480395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83717513193936701113281053 31394067447726262917480395)
            ·
              refine ⟨47091101171589394376220593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31394067447726262917480395 47091101171589394376220593)
              ·
                refine ⟨35318325878692045782165445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47091101171589394376220593 35318325878692045782165445)
                ·
                  refine ⟨6622186102254758584156021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35318325878692045782165445 6622186102254758584156021)
                  ·
                    refine ⟨620829947086383617264627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6622186102254758584156021 620829947086383617264627)
                    ·
                      rfl

theorem cell23_3627186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3627186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627186 prefixEnd_3627186 := by exact prefixLift 3627186
  have htrace : WordTrace (prefixWord ++ tailWord_3627186) baseStart_3627186 baseEnd_3627186 := by
    simpa [prefixWord, tailWord_3627186, baseEnd_3627186] using wordTrace_append hprefix tailTrace_3627186
  have hstable : (prefixWord ++ tailWord_3627186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627186).length < 2 ^ (prefixWord ++ tailWord_3627186).sum := by decide
  have hdescent : baseEnd_3627186 < baseStart_3627186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627188 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_3627188 : Nat := 118140960795 + 3627188 * 2 ^ 59
def prefixEnd_3627188 : Nat := 4983230072969 + 3 ^ 40 * 3627188 * 2
def baseEnd_3627188 : Nat := 1862490868220459843968873

theorem tailTrace_3627188 : CollatzResearch.WordTrace tailWord_3627188 prefixEnd_3627188 1862490868220459843968873 := by
  unfold tailWord_3627188
  simp only [CollatzResearch.WordTrace]
  refine ⟨66147207391662412618317109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88196276522216550157756145 66147207391662412618317109)
  ·
    refine ⟨6201300692968351182967229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66147207391662412618317109 6201300692968351182967229)
    ·
      refine ⟨2325487759863131693612711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6201300692968351182967229 2325487759863131693612711)
      ·
        refine ⟨3488231639794697540419067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325487759863131693612711 3488231639794697540419067)
        ·
          refine ⟨5232347459692046310628601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488231639794697540419067 5232347459692046310628601)
          ·
            refine ⟨3924260594769034732971451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5232347459692046310628601 3924260594769034732971451)
            ·
              refine ⟨5886390892153552099457177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924260594769034732971451 5886390892153552099457177)
              ·
                refine ⟨4414793169115164074592883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886390892153552099457177 4414793169115164074592883)
                ·
                  refine ⟨6622189753672746111889325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4414793169115164074592883 6622189753672746111889325)
                  ·
                    refine ⟨2483321157627279791958497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6622189753672746111889325 2483321157627279791958497)
                    ·
                      refine ⟨1862490868220459843968873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483321157627279791958497 1862490868220459843968873)
                      ·
                        rfl

theorem cell23_3627188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_3627188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627188 prefixEnd_3627188 := by exact prefixLift 3627188
  have htrace : WordTrace (prefixWord ++ tailWord_3627188) baseStart_3627188 baseEnd_3627188 := by
    simpa [prefixWord, tailWord_3627188, baseEnd_3627188] using wordTrace_append hprefix tailTrace_3627188
  have hstable : (prefixWord ++ tailWord_3627188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627188).length < 2 ^ (prefixWord ++ tailWord_3627188).sum := by decide
  have hdescent : baseEnd_3627188 < baseStart_3627188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627223 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 2, 4, 2]
def baseStart_3627223 : Nat := 118140960795 + 3627223 * 2 ^ 59
def prefixEnd_3627223 : Nat := 4983230072969 + 3 ^ 40 * 3627223 * 2
def baseEnd_3627223 : Nat := 1862508840043367207031211

theorem tailTrace_3627223 : CollatzResearch.WordTrace tailWord_3627223 prefixEnd_3627223 1862508840043367207031211 := by
  unfold tailWord_3627223
  simp only [CollatzResearch.WordTrace]
  refine ⟨132295691338198026214158323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88197127558798684142772215 132295691338198026214158323)
  ·
    refine ⟨198443537007297039321237485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132295691338198026214158323 198443537007297039321237485)
    ·
      refine ⟨74416326377736389745464057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198443537007297039321237485 74416326377736389745464057)
      ·
        refine ⟨55812244783302292309098043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74416326377736389745464057 55812244783302292309098043)
        ·
          refine ⟨83718367174953438463647065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55812244783302292309098043 83718367174953438463647065)
          ·
            refine ⟨62788775381215078847735299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83718367174953438463647065 62788775381215078847735299)
            ·
              refine ⟨94183163071822618271602949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62788775381215078847735299 94183163071822618271602949)
              ·
                refine ⟨17659343075966740925925553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94183163071822618271602949 17659343075966740925925553)
                ·
                  refine ⟨13244507306975055694444165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17659343075966740925925553 13244507306975055694444165)
                  ·
                    refine ⟨2483345120057822942708281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13244507306975055694444165 2483345120057822942708281)
                    ·
                      refine ⟨1862508840043367207031211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483345120057822942708281 1862508840043367207031211)
                      ·
                        rfl

theorem cell23_3627223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_3627223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627223 prefixEnd_3627223 := by exact prefixLift 3627223
  have htrace : WordTrace (prefixWord ++ tailWord_3627223) baseStart_3627223 baseEnd_3627223 := by
    simpa [prefixWord, tailWord_3627223, baseEnd_3627223] using wordTrace_append hprefix tailTrace_3627223
  have hstable : (prefixWord ++ tailWord_3627223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627223).length < 2 ^ (prefixWord ++ tailWord_3627223).sum := by decide
  have hdescent : baseEnd_3627223 < baseStart_3627223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627233 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3627233 : Nat := 118140960795 + 3627233 * 2 ^ 59
def prefixEnd_3627233 : Nat := 4983230072969 + 3 ^ 40 * 3627233 * 2
def baseEnd_3627233 : Nat := 620837991616637389302055

theorem tailTrace_3627233 : CollatzResearch.WordTrace tailWord_3627233 prefixEnd_3627233 620837991616637389302055 := by
  unfold tailWord_3627233
  simp only [CollatzResearch.WordTrace]
  refine ⟨132296056068161797922022353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88197370712107865281348235 132296056068161797922022353)
  ·
    refine ⟨99222042051121348441516765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132296056068161797922022353 99222042051121348441516765)
    ·
      refine ⟨37208265769170505665568787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99222042051121348441516765 37208265769170505665568787)
      ·
        refine ⟨55812398653755758498353181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37208265769170505665568787 55812398653755758498353181)
        ·
          refine ⟨20929649495158409436882443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55812398653755758498353181 20929649495158409436882443)
          ·
            refine ⟨31394474242737614155323665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20929649495158409436882443 31394474242737614155323665)
            ·
              refine ⟨23545855682053210616492749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31394474242737614155323665 23545855682053210616492749)
              ·
                refine ⟨8829695880769953981184781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23545855682053210616492749 8829695880769953981184781)
                ·
                  refine ⟨3311135955288732742944293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8829695880769953981184781 3311135955288732742944293)
                  ·
                    refine ⟨620837991616637389302055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311135955288732742944293 620837991616637389302055)
                    ·
                      rfl

theorem cell23_3627233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3627233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627233 prefixEnd_3627233 := by exact prefixLift 3627233
  have htrace : WordTrace (prefixWord ++ tailWord_3627233) baseStart_3627233 baseEnd_3627233 := by
    simpa [prefixWord, tailWord_3627233, baseEnd_3627233] using wordTrace_append hprefix tailTrace_3627233
  have hstable : (prefixWord ++ tailWord_3627233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627233).length < 2 ^ (prefixWord ++ tailWord_3627233).sum := by decide
  have hdescent : baseEnd_3627233 < baseStart_3627233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627234 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3627234 : Nat := 118140960795 + 3627234 * 2 ^ 59
def prefixEnd_3627234 : Nat := 4983230072969 + 3 ^ 40 * 3627234 * 2
def baseEnd_3627234 : Nat := 1862514488330566663993661

theorem tailTrace_3627234 : CollatzResearch.WordTrace tailWord_3627234 prefixEnd_3627234 1862514488330566663993661 := by
  unfold tailWord_3627234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074023135289543773202189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88197395027438783395205837 33074023135289543773202189)
  ·
    refine ⟨12402758675733578914950821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33074023135289543773202189 12402758675733578914950821)
    ·
      refine ⟨2325517251700046046553279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12402758675733578914950821 2325517251700046046553279)
      ·
        refine ⟨3488275877550069069829919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325517251700046046553279 3488275877550069069829919)
        ·
          refine ⟨5232413816325103604744879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488275877550069069829919 5232413816325103604744879)
          ·
            refine ⟨7848620724487655407117319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232413816325103604744879 7848620724487655407117319)
            ·
              refine ⟨11772931086731483110675979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848620724487655407117319 11772931086731483110675979)
              ·
                refine ⟨17659396630097224666013969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11772931086731483110675979 17659396630097224666013969)
                ·
                  refine ⟨13244547472572918499510477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17659396630097224666013969 13244547472572918499510477)
                  ·
                    refine ⟨4966705302214844437316429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13244547472572918499510477 4966705302214844437316429)
                    ·
                      refine ⟨1862514488330566663993661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966705302214844437316429 1862514488330566663993661)
                      ·
                        rfl

theorem cell23_3627234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3627234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627234 prefixEnd_3627234 := by exact prefixLift 3627234
  have htrace : WordTrace (prefixWord ++ tailWord_3627234) baseStart_3627234 baseEnd_3627234 := by
    simpa [prefixWord, tailWord_3627234, baseEnd_3627234] using wordTrace_append hprefix tailTrace_3627234
  have hstable : (prefixWord ++ tailWord_3627234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627234).length < 2 ^ (prefixWord ++ tailWord_3627234).sum := by decide
  have hdescent : baseEnd_3627234 < baseStart_3627234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627236 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3627236 : Nat := 118140960795 + 3627236 * 2 ^ 59
def prefixEnd_3627236 : Nat := 4983230072969 + 3 ^ 40 * 3627236 * 2
def baseEnd_3627236 : Nat := 1862515515291875656168651

theorem tailTrace_3627236 : CollatzResearch.WordTrace tailWord_3627236 prefixEnd_3627236 1862515515291875656168651 := by
  unfold tailWord_3627236
  simp only [CollatzResearch.WordTrace]
  refine ⟨66148082743575464717190781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88197443658100619622921041 66148082743575464717190781)
  ·
    refine ⟨24805531028840799268946543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66148082743575464717190781 24805531028840799268946543)
    ·
      refine ⟨37208296543261198903419815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24805531028840799268946543 37208296543261198903419815)
      ·
        refine ⟨55812444814891798355129723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37208296543261198903419815 55812444814891798355129723)
        ·
          refine ⟨83718667222337697532694585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55812444814891798355129723 83718667222337697532694585)
          ·
            refine ⟨62789000416753273149520939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83718667222337697532694585 62789000416753273149520939)
            ·
              refine ⟨94183500625129909724281409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62789000416753273149520939 94183500625129909724281409)
              ·
                refine ⟨70637625468847432293211057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94183500625129909724281409 70637625468847432293211057)
                ·
                  refine ⟨52978219101635574219908293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70637625468847432293211057 52978219101635574219908293)
                  ·
                    refine ⟨9933416081556670166232805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52978219101635574219908293 9933416081556670166232805)
                    ·
                      refine ⟨1862515515291875656168651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9933416081556670166232805 1862515515291875656168651)
                      ·
                        rfl

theorem cell23_3627236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3627236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627236 prefixEnd_3627236 := by exact prefixLift 3627236
  have htrace : WordTrace (prefixWord ++ tailWord_3627236) baseStart_3627236 baseEnd_3627236 := by
    simpa [prefixWord, tailWord_3627236, baseEnd_3627236] using wordTrace_append hprefix tailTrace_3627236
  have hstable : (prefixWord ++ tailWord_3627236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627236).length < 2 ^ (prefixWord ++ tailWord_3627236).sum := by decide
  have hdescent : baseEnd_3627236 < baseStart_3627236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627240 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_3627240 : Nat := 118140960795 + 3627240 * 2 ^ 59
def prefixEnd_3627240 : Nat := 4983230072969 + 3 ^ 40 * 3627240 * 2
def baseEnd_3627240 : Nat := 1862517569214493640518633

theorem tailTrace_3627240 : CollatzResearch.WordTrace tailWord_3627240 prefixEnd_3627240 1862517569214493640518633 := by
  unfold tailWord_3627240
  simp only [CollatzResearch.WordTrace]
  refine ⟨66148155689568219058763587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88197540919424292078351449 66148155689568219058763587)
  ·
    refine ⟨99222233534352328588145381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66148155689568219058763587 99222233534352328588145381)
    ·
      refine ⟨18604168787691061610277259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99222233534352328588145381 18604168787691061610277259)
      ·
        refine ⟨27906253181536592415415889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18604168787691061610277259 27906253181536592415415889)
        ·
          refine ⟨20929689886152444311561917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27906253181536592415415889 20929689886152444311561917)
          ·
            refine ⟨7848633707307166616835719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20929689886152444311561917 7848633707307166616835719)
            ·
              refine ⟨11772950560960749925253579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848633707307166616835719 11772950560960749925253579)
              ·
                refine ⟨17659425841441124887880369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11772950560960749925253579 17659425841441124887880369)
                ·
                  refine ⟨13244569381080843665910277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17659425841441124887880369 13244569381080843665910277)
                  ·
                    refine ⟨2483356758952658187358177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13244569381080843665910277 2483356758952658187358177)
                    ·
                      refine ⟨1862517569214493640518633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483356758952658187358177 1862517569214493640518633)
                      ·
                        rfl

theorem cell23_3627240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_3627240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627240 prefixEnd_3627240 := by exact prefixLift 3627240
  have htrace : WordTrace (prefixWord ++ tailWord_3627240) baseStart_3627240 baseEnd_3627240 := by
    simpa [prefixWord, tailWord_3627240, baseEnd_3627240] using wordTrace_append hprefix tailTrace_3627240
  have hstable : (prefixWord ++ tailWord_3627240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627240).length < 2 ^ (prefixWord ++ tailWord_3627240).sum := by decide
  have hdescent : baseEnd_3627240 < baseStart_3627240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627246 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_3627246 : Nat := 118140960795 + 3627246 * 2 ^ 59
def prefixEnd_3627246 : Nat := 4983230072969 + 3 ^ 40 * 3627246 * 2
def baseEnd_3627246 : Nat := 206946738899824513004845

theorem tailTrace_3627246 : CollatzResearch.WordTrace tailWord_3627246 prefixEnd_3627246 206946738899824513004845 := by
  unfold tailWord_3627246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537066277139337642780699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88197686811409800761497061 16537066277139337642780699)
  ·
    refine ⟨24805599415709006464171049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16537066277139337642780699 24805599415709006464171049)
    ·
      refine ⟨18604199561781754848128287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24805599415709006464171049 18604199561781754848128287)
      ·
        refine ⟨27906299342672632272192431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18604199561781754848128287 27906299342672632272192431)
        ·
          refine ⟨41859449014008948408288647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27906299342672632272192431 41859449014008948408288647)
          ·
            refine ⟨62789173521013422612432971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41859449014008948408288647 62789173521013422612432971)
            ·
              refine ⟨94183760281520133918649457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62789173521013422612432971 94183760281520133918649457)
              ·
                refine ⟨70637820211140100438987093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94183760281520133918649457 70637820211140100438987093)
                ·
                  refine ⟨206946738899824513004845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 70637820211140100438987093 206946738899824513004845)
                  ·
                    rfl

theorem cell23_3627246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_3627246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627246 prefixEnd_3627246 := by exact prefixLift 3627246
  have htrace : WordTrace (prefixWord ++ tailWord_3627246) baseStart_3627246 baseEnd_3627246 := by
    simpa [prefixWord, tailWord_3627246, baseEnd_3627246] using wordTrace_append hprefix tailTrace_3627246
  have hstable : (prefixWord ++ tailWord_3627246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627246).length < 2 ^ (prefixWord ++ tailWord_3627246).sum := by decide
  have hdescent : baseEnd_3627246 < baseStart_3627246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627250 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3627250 : Nat := 118140960795 + 3627250 * 2 ^ 59
def prefixEnd_3627250 : Nat := 4983230072969 + 3 ^ 40 * 3627250 * 2
def baseEnd_3627250 : Nat := 620840901340346200464529

theorem tailTrace_3627250 : CollatzResearch.WordTrace tailWord_3627250 prefixEnd_3627250 620840901340346200464529 := by
  unfold tailWord_3627250
  simp only [CollatzResearch.WordTrace]
  refine ⟨33074169027275052456347801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88197784072733473216927469 33074169027275052456347801)
  ·
    refine ⟨24805626770456289342260851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33074169027275052456347801 24805626770456289342260851)
    ·
      refine ⟨37208440155684434013391277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24805626770456289342260851 37208440155684434013391277)
      ·
        refine ⟨13953165058381662755021729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37208440155684434013391277 13953165058381662755021729)
        ·
          refine ⟨10464873793786247066266297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13953165058381662755021729 10464873793786247066266297)
          ·
            refine ⟨7848655345339685299699723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10464873793786247066266297 7848655345339685299699723)
            ·
              refine ⟨11772983018009527949549585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848655345339685299699723 11772983018009527949549585)
              ·
                refine ⟨8829737263507145962162189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11772983018009527949549585 8829737263507145962162189)
                ·
                  refine ⟨3311151473815179735810821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8829737263507145962162189 3311151473815179735810821)
                  ·
                    refine ⟨620840901340346200464529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311151473815179735810821 620840901340346200464529)
                    ·
                      rfl

theorem cell23_3627250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3627250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627250 prefixEnd_3627250 := by exact prefixLift 3627250
  have htrace : WordTrace (prefixWord ++ tailWord_3627250) baseStart_3627250 baseEnd_3627250 := by
    simpa [prefixWord, tailWord_3627250, baseEnd_3627250] using wordTrace_append hprefix tailTrace_3627250
  have hstable : (prefixWord ++ tailWord_3627250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627250).length < 2 ^ (prefixWord ++ tailWord_3627250).sum := by decide
  have hdescent : baseEnd_3627250 < baseStart_3627250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627260 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_3627260 : Nat := 118140960795 + 3627260 * 2 ^ 59
def prefixEnd_3627260 : Nat := 4983230072969 + 3 ^ 40 * 3627260 * 2
def baseEnd_3627260 : Nat := 1862527838827583562268541

theorem tailTrace_3627260 : CollatzResearch.WordTrace tailWord_3627260 prefixEnd_3627260 1862527838827583562268541 := by
  unfold tailWord_3627260
  simp only [CollatzResearch.WordTrace]
  refine ⟨66148520419531990766627617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88198027226042654355503489 66148520419531990766627617)
  ·
    refine ⟨49611390314648993074970713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66148520419531990766627617 49611390314648993074970713)
    ·
      refine ⟨37208542735986744806228035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49611390314648993074970713 37208542735986744806228035)
      ·
        refine ⟨55812814103980117209342053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37208542735986744806228035 55812814103980117209342053)
        ·
          refine ⟨10464902644496271976751635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55812814103980117209342053 10464902644496271976751635)
          ·
            refine ⟨15697353966744407965127453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10464902644496271976751635 15697353966744407965127453)
            ·
              refine ⟨5886507737529152986922795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15697353966744407965127453 5886507737529152986922795)
              ·
                refine ⟨8829761606293729480384193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5886507737529152986922795 8829761606293729480384193)
                ·
                  refine ⟨6622321204720297110288145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8829761606293729480384193 6622321204720297110288145)
                  ·
                    refine ⟨4966740903540222832716109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6622321204720297110288145 4966740903540222832716109)
                    ·
                      refine ⟨1862527838827583562268541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966740903540222832716109 1862527838827583562268541)
                      ·
                        rfl

theorem cell23_3627260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_3627260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627260 prefixEnd_3627260 := by exact prefixLift 3627260
  have htrace : WordTrace (prefixWord ++ tailWord_3627260) baseStart_3627260 baseEnd_3627260 := by
    simpa [prefixWord, tailWord_3627260, baseEnd_3627260] using wordTrace_append hprefix tailTrace_3627260
  have hstable : (prefixWord ++ tailWord_3627260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627260).length < 2 ^ (prefixWord ++ tailWord_3627260).sum := by decide
  have hdescent : baseEnd_3627260 < baseStart_3627260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627300 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_3627300 : Nat := 118140960795 + 3627300 * 2 ^ 59
def prefixEnd_3627300 : Nat := 4983230072969 + 3 ^ 40 * 3627300 * 2
def baseEnd_3627300 : Nat := 1862548378053763405768357

theorem tailTrace_3627300 : CollatzResearch.WordTrace tailWord_3627300 prefixEnd_3627300 1862548378053763405768357 := by
  unfold tailWord_3627300
  simp only [CollatzResearch.WordTrace]
  refine ⟨66149249879459534182355677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88198999839279378909807569 66149249879459534182355677)
  ·
    refine ⟨24805968704797325318383379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66149249879459534182355677 24805968704797325318383379)
    ·
      refine ⟨37208953057195987977575069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24805968704797325318383379 37208953057195987977575069)
      ·
        refine ⟨13953357396448495491590651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37208953057195987977575069 13953357396448495491590651)
        ·
          refine ⟨20930036094672743237385977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13953357396448495491590651 20930036094672743237385977)
          ·
            refine ⟨15697527071004557428039483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20930036094672743237385977 15697527071004557428039483)
            ·
              refine ⟨23546290606506836142059225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15697527071004557428039483 23546290606506836142059225)
              ·
                refine ⟨17659717954880127106544419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23546290606506836142059225 17659717954880127106544419)
                ·
                  refine ⟨26489576932320190659816629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17659717954880127106544419 26489576932320190659816629)
                  ·
                    refine ⟨2483397837405017874357809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26489576932320190659816629 2483397837405017874357809)
                    ·
                      refine ⟨1862548378053763405768357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483397837405017874357809 1862548378053763405768357)
                      ·
                        rfl

theorem cell23_3627300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_3627300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627300 prefixEnd_3627300 := by exact prefixLift 3627300
  have htrace : WordTrace (prefixWord ++ tailWord_3627300) baseStart_3627300 baseEnd_3627300 := by
    simpa [prefixWord, tailWord_3627300, baseEnd_3627300] using wordTrace_append hprefix tailTrace_3627300
  have hstable : (prefixWord ++ tailWord_3627300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627300).length < 2 ^ (prefixWord ++ tailWord_3627300).sum := by decide
  have hdescent : baseEnd_3627300 < baseStart_3627300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627333 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_3627333 : Nat := 118140960795 + 3627333 * 2 ^ 59
def prefixEnd_3627333 : Nat := 4983230072969 + 3 ^ 40 * 3627333 * 2
def baseEnd_3627333 : Nat := 1862565322915361776655705

theorem tailTrace_3627333 : CollatzResearch.WordTrace tailWord_3627333 prefixEnd_3627333 1862565322915361776655705 := by
  unfold tailWord_3627333
  simp only [CollatzResearch.WordTrace]
  refine ⟨132299703367799515000662653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88199802245199676667108435 132299703367799515000662653)
  ·
    refine ⟨49612388762924818125248495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132299703367799515000662653 49612388762924818125248495)
    ·
      refine ⟨74418583144387227187872743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49612388762924818125248495 74418583144387227187872743)
      ·
        refine ⟨111627874716580840781809115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74418583144387227187872743 111627874716580840781809115)
        ·
          refine ⟨167441812074871261172713673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111627874716580840781809115 167441812074871261172713673)
          ·
            refine ⟨125581359056153445879535255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167441812074871261172713673 125581359056153445879535255)
            ·
              refine ⟨188372038584230168819302883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125581359056153445879535255 188372038584230168819302883)
              ·
                refine ⟨282558057876345253228954325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188372038584230168819302883 282558057876345253228954325)
                ·
                  refine ⟨6622454481476841872553617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 282558057876345253228954325 6622454481476841872553617)
                  ·
                    refine ⟨4966840861107631404415213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6622454481476841872553617 4966840861107631404415213)
                    ·
                      refine ⟨1862565322915361776655705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966840861107631404415213 1862565322915361776655705)
                      ·
                        rfl

theorem cell23_3627333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_3627333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627333 prefixEnd_3627333 := by exact prefixLift 3627333
  have htrace : WordTrace (prefixWord ++ tailWord_3627333) baseStart_3627333 baseEnd_3627333 := by
    simpa [prefixWord, tailWord_3627333, baseEnd_3627333] using wordTrace_append hprefix tailTrace_3627333
  have hstable : (prefixWord ++ tailWord_3627333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627333).length < 2 ^ (prefixWord ++ tailWord_3627333).sum := by decide
  have hdescent : baseEnd_3627333 < baseStart_3627333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627336 : List Nat := [2, 1, 3, 1, 1, 2, 13]
def baseStart_3627336 : Nat := 118140960795 + 3627336 * 2 ^ 59
def prefixEnd_3627336 : Nat := 4983230072969 + 3 ^ 40 * 3627336 * 2
def baseEnd_3627336 : Nat := 22994652634041052653311

theorem tailTrace_3627336 : CollatzResearch.WordTrace tailWord_3627336 prefixEnd_3627336 22994652634041052653311 := by
  unfold tailWord_3627336
  simp only [CollatzResearch.WordTrace]
  refine ⟨66149906393394323256510931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88199875191192431008681241 66149906393394323256510931)
  ·
    refine ⟨99224859590091484884766397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66149906393394323256510931 99224859590091484884766397)
    ·
      refine ⟨37209322346284306831787399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99224859590091484884766397 37209322346284306831787399)
      ·
        refine ⟨55813983519426460247681099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37209322346284306831787399 55813983519426460247681099)
        ·
          refine ⟨83720975279139690371521649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55813983519426460247681099 83720975279139690371521649)
          ·
            refine ⟨62790731459354767778641237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83720975279139690371521649 62790731459354767778641237)
            ·
              refine ⟨22994652634041052653311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 62790731459354767778641237 22994652634041052653311)
              ·
                rfl

theorem cell23_3627336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 13].length) (baseStart_3627336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627336 prefixEnd_3627336 := by exact prefixLift 3627336
  have htrace : WordTrace (prefixWord ++ tailWord_3627336) baseStart_3627336 baseEnd_3627336 := by
    simpa [prefixWord, tailWord_3627336, baseEnd_3627336] using wordTrace_append hprefix tailTrace_3627336
  have hstable : (prefixWord ++ tailWord_3627336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627336).length < 2 ^ (prefixWord ++ tailWord_3627336).sum := by decide
  have hdescent : baseEnd_3627336 < baseStart_3627336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627340 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_3627340 : Nat := 118140960795 + 3627340 * 2 ^ 59
def prefixEnd_3627340 : Nat := 4983230072969 + 3 ^ 40 * 3627340 * 2
def baseEnd_3627340 : Nat := 620856305759981083089391

theorem tailTrace_3627340 : CollatzResearch.WordTrace tailWord_3627340 prefixEnd_3627340 620856305759981083089391 := by
  unfold tailWord_3627340
  simp only [CollatzResearch.WordTrace]
  refine ⟨66149979339387077598083737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88199972452516103464111649 66149979339387077598083737)
  ·
    refine ⟨49612484504540308198562803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66149979339387077598083737 49612484504540308198562803)
    ·
      refine ⟨74418726756810462297844205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49612484504540308198562803 74418726756810462297844205)
      ·
        refine ⟨27907022533803923361691577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74418726756810462297844205 27907022533803923361691577)
        ·
          refine ⟨20930266900352942521268683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27907022533803923361691577 20930266900352942521268683)
          ·
            refine ⟨31395400350529413781903025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20930266900352942521268683 31395400350529413781903025)
            ·
              refine ⟨23546550262897060336427269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31395400350529413781903025 23546550262897060336427269)
              ·
                refine ⟨4414978174293198813080113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23546550262897060336427269 4414978174293198813080113)
                ·
                  refine ⟨3311233630719899109810085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4414978174293198813080113 3311233630719899109810085)
                  ·
                    refine ⟨620856305759981083089391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311233630719899109810085 620856305759981083089391)
                    ·
                      rfl

theorem cell23_3627340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_3627340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627340 prefixEnd_3627340 := by exact prefixLift 3627340
  have htrace : WordTrace (prefixWord ++ tailWord_3627340) baseStart_3627340 baseEnd_3627340 := by
    simpa [prefixWord, tailWord_3627340, baseEnd_3627340] using wordTrace_append hprefix tailTrace_3627340
  have hstable : (prefixWord ++ tailWord_3627340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627340).length < 2 ^ (prefixWord ++ tailWord_3627340).sum := by decide
  have hdescent : baseEnd_3627340 < baseStart_3627340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627367 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_3627367 : Nat := 118140960795 + 3627367 * 2 ^ 59
def prefixEnd_3627367 : Nat := 4983230072969 + 3 ^ 40 * 3627367 * 2
def baseEnd_3627367 : Nat := 1862582781257614643630549

theorem tailTrace_3627367 : CollatzResearch.WordTrace tailWord_3627367 prefixEnd_3627367 1862582781257614643630549 := by
  unfold tailWord_3627367
  simp only [CollatzResearch.WordTrace]
  refine ⟨132300943449676338807400355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88200628966450892538266903 132300943449676338807400355)
  ·
    refine ⟨198451415174514508211100533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132300943449676338807400355 198451415174514508211100533)
    ·
      refine ⟨18604820172610735144790675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198451415174514508211100533 18604820172610735144790675)
      ·
        refine ⟨27907230258916102717186013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18604820172610735144790675 27907230258916102717186013)
        ·
          refine ⟨10465211347093538518944755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27907230258916102717186013 10465211347093538518944755)
          ·
            refine ⟨15697817020640307778417133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10465211347093538518944755 15697817020640307778417133)
            ·
              refine ⟨5886681382740115416906425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15697817020640307778417133 5886681382740115416906425)
              ·
                refine ⟨4415011037055086562679819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886681382740115416906425 4415011037055086562679819)
                ·
                  refine ⟨6622516555582629844019729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415011037055086562679819 6622516555582629844019729)
                  ·
                    refine ⟨4966887416686972383014797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6622516555582629844019729 4966887416686972383014797)
                    ·
                      refine ⟨1862582781257614643630549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4966887416686972383014797 1862582781257614643630549)
                      ·
                        rfl

theorem cell23_3627367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_3627367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627367 prefixEnd_3627367 := by exact prefixLift 3627367
  have htrace : WordTrace (prefixWord ++ tailWord_3627367) baseStart_3627367 baseEnd_3627367 := by
    simpa [prefixWord, tailWord_3627367, baseEnd_3627367] using wordTrace_append hprefix tailTrace_3627367
  have hstable : (prefixWord ++ tailWord_3627367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627367).length < 2 ^ (prefixWord ++ tailWord_3627367).sum := by decide
  have hdescent : baseEnd_3627367 < baseStart_3627367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627403 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4]
def baseStart_3627403 : Nat := 118140960795 + 3627403 * 2 ^ 59
def prefixEnd_3627403 : Nat := 4983230072969 + 3 ^ 40 * 3627403 * 2
def baseEnd_3627403 : Nat := 1862601266561176502780383

theorem tailTrace_3627403 : CollatzResearch.WordTrace tailWord_3627403 prefixEnd_3627403 1862601266561176502780383 := by
  unfold tailWord_3627403
  simp only [CollatzResearch.WordTrace]
  refine ⟨132302256477545916955710863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88201504318363944637140575 132302256477545916955710863)
  ·
    refine ⟨198453384716318875433566295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132302256477545916955710863 198453384716318875433566295)
    ·
      refine ⟨297680077074478313150349443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198453384716318875433566295 297680077074478313150349443)
      ·
        refine ⟨446520115611717469725524165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297680077074478313150349443 446520115611717469725524165)
        ·
          refine ⟨83722521677197025573535781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446520115611717469725524165 83722521677197025573535781)
          ·
            refine ⟨15697972814474442295037959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83722521677197025573535781 15697972814474442295037959)
            ·
              refine ⟨23546959221711663442556939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15697972814474442295037959 23546959221711663442556939)
              ·
                refine ⟨35320438832567495163835409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23546959221711663442556939 35320438832567495163835409)
                ·
                  refine ⟨26490329124425621372876557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35320438832567495163835409 26490329124425621372876557)
                  ·
                    refine ⟨9933873421659608014828709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26490329124425621372876557 9933873421659608014828709)
                    ·
                      refine ⟨1862601266561176502780383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9933873421659608014828709 1862601266561176502780383)
                      ·
                        rfl

theorem cell23_3627403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_3627403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627403 prefixEnd_3627403 := by exact prefixLift 3627403
  have htrace : WordTrace (prefixWord ++ tailWord_3627403) baseStart_3627403 baseEnd_3627403 := by
    simpa [prefixWord, tailWord_3627403, baseEnd_3627403] using wordTrace_append hprefix tailTrace_3627403
  have hstable : (prefixWord ++ tailWord_3627403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627403).length < 2 ^ (prefixWord ++ tailWord_3627403).sum := by decide
  have hdescent : baseEnd_3627403 < baseStart_3627403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627441 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 1, 3, 2]
def baseStart_3627441 : Nat := 118140960795 + 3627441 * 2 ^ 59
def prefixEnd_3627441 : Nat := 4983230072969 + 3 ^ 40 * 3627441 * 2
def baseEnd_3627441 : Nat := 1862620778826047354105209

theorem tailTrace_3627441 : CollatzResearch.WordTrace tailWord_3627441 prefixEnd_3627441 1862620778826047354105209 := by
  unfold tailWord_3627441
  simp only [CollatzResearch.WordTrace]
  refine ⟨132303642451408249445594177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88202428300938832963729451 132303642451408249445594177)
  ·
    refine ⟨99227731838556187084195633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132303642451408249445594177 99227731838556187084195633)
    ·
      refine ⟨74420798878917140313146725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99227731838556187084195633 74420798878917140313146725)
      ·
        refine ⟨13953899789796963808715011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74420798878917140313146725 13953899789796963808715011)
        ·
          refine ⟨20930849684695445713072517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13953899789796963808715011 20930849684695445713072517)
          ·
            refine ⟨3924534315880396071201097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20930849684695445713072517 3924534315880396071201097)
            ·
              refine ⟨2943400736910297053400823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924534315880396071201097 2943400736910297053400823)
              ·
                refine ⟨4415101105365445580101235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943400736910297053400823 4415101105365445580101235)
                ·
                  refine ⟨6622651658048168370151853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415101105365445580101235 6622651658048168370151853)
                  ·
                    refine ⟨2483494371768063138806945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6622651658048168370151853 2483494371768063138806945)
                    ·
                      refine ⟨1862620778826047354105209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483494371768063138806945 1862620778826047354105209)
                      ·
                        rfl

theorem cell23_3627441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_3627441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627441 prefixEnd_3627441 := by exact prefixLift 3627441
  have htrace : WordTrace (prefixWord ++ tailWord_3627441) baseStart_3627441 baseEnd_3627441 := by
    simpa [prefixWord, tailWord_3627441, baseEnd_3627441] using wordTrace_append hprefix tailTrace_3627441
  have hstable : (prefixWord ++ tailWord_3627441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627441).length < 2 ^ (prefixWord ++ tailWord_3627441).sum := by decide
  have hdescent : baseEnd_3627441 < baseStart_3627441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627522 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3627522 : Nat := 118140960795 + 3627522 * 2 ^ 59
def prefixEnd_3627522 : Nat := 4983230072969 + 3 ^ 40 * 3627522 * 2
def baseEnd_3627522 : Nat := 1862662370759061537192337

theorem tailTrace_3627522 : CollatzResearch.WordTrace tailWord_3627522 prefixEnd_3627522 1862662370759061537192337 := by
  unfold tailWord_3627522
  simp only [CollatzResearch.WordTrace]
  refine ⟨33076649191028700069823205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88204397842743200186195213 33076649191028700069823205)
  ·
    refine ⟨6201871723317881263091851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33076649191028700069823205 6201871723317881263091851)
    ·
      refine ⟨9302807584976821894637777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6201871723317881263091851 9302807584976821894637777)
      ·
        refine ⟨6977105688732616420978333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9302807584976821894637777 6977105688732616420978333)
        ·
          refine ⟨2616414633274731157866875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6977105688732616420978333 2616414633274731157866875)
          ·
            refine ⟨3924621949912096736800313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616414633274731157866875 3924621949912096736800313)
            ·
              refine ⟨2943466462434072552600235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3924621949912096736800313 2943466462434072552600235)
              ·
                refine ⟨4415199693651108828900353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2943466462434072552600235 4415199693651108828900353)
                ·
                  refine ⟨3311399770238331621675265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415199693651108828900353 3311399770238331621675265)
                  ·
                    refine ⟨2483549827678748716256449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3311399770238331621675265 2483549827678748716256449)
                    ·
                      refine ⟨1862662370759061537192337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483549827678748716256449 1862662370759061537192337)
                      ·
                        rfl

theorem cell23_3627522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3627522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627522 prefixEnd_3627522 := by exact prefixLift 3627522
  have htrace : WordTrace (prefixWord ++ tailWord_3627522) baseStart_3627522 baseEnd_3627522 := by
    simpa [prefixWord, tailWord_3627522, baseEnd_3627522] using wordTrace_append hprefix tailTrace_3627522
  have hstable : (prefixWord ++ tailWord_3627522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627522).length < 2 ^ (prefixWord ++ tailWord_3627522).sum := by decide
  have hdescent : baseEnd_3627522 < baseStart_3627522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627554 : List Nat := [3, 3, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3627554 : Nat := 118140960795 + 3627554 * 2 ^ 59
def prefixEnd_3627554 : Nat := 4983230072969 + 3 ^ 40 * 3627554 * 2
def baseEnd_3627554 : Nat := 620892934046668470664063

theorem tailTrace_3627554 : CollatzResearch.WordTrace tailWord_3627554 prefixEnd_3627554 620892934046668470664063 := by
  unfold tailWord_3627554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33076940974999717436114429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88205175933332579829638477 33076940974999717436114429)
  ·
    refine ⟨12403852865624894038542911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33076940974999717436114429 12403852865624894038542911)
    ·
      refine ⟨18605779298437341057814367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12403852865624894038542911 18605779298437341057814367)
      ·
        refine ⟨27908668947656011586721551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18605779298437341057814367 27908668947656011586721551)
        ·
          refine ⟨41863003421484017380082327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27908668947656011586721551 41863003421484017380082327)
          ·
            refine ⟨62794505132226026070123491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41863003421484017380082327 62794505132226026070123491)
            ·
              refine ⟨94191757698339039105185237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62794505132226026070123491 94191757698339039105185237)
              ·
                refine ⟨2207619321054821229027779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94191757698339039105185237 2207619321054821229027779)
                ·
                  refine ⟨3311428981582231843541669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207619321054821229027779 3311428981582231843541669)
                  ·
                    refine ⟨620892934046668470664063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311428981582231843541669 620892934046668470664063)
                    ·
                      rfl

theorem cell23_3627554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3627554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627554 prefixEnd_3627554 := by exact prefixLift 3627554
  have htrace : WordTrace (prefixWord ++ tailWord_3627554) baseStart_3627554 baseEnd_3627554 := by
    simpa [prefixWord, tailWord_3627554, baseEnd_3627554] using wordTrace_append hprefix tailTrace_3627554
  have hstable : (prefixWord ++ tailWord_3627554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627554).length < 2 ^ (prefixWord ++ tailWord_3627554).sum := by decide
  have hdescent : baseEnd_3627554 < baseStart_3627554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627587 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 4, 3, 2]
def baseStart_3627587 : Nat := 118140960795 + 3627587 * 2 ^ 59
def prefixEnd_3627587 : Nat := 4983230072969 + 3 ^ 40 * 3627587 * 2
def baseEnd_3627587 : Nat := 1862695747001603782879537

theorem tailTrace_3627587 : CollatzResearch.WordTrace tailWord_3627587 prefixEnd_3627587 1862695747001603782879537 := by
  unfold tailWord_3627587
  simp only [CollatzResearch.WordTrace]
  refine ⟨132308967508879316380409015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88205978339252877586939343 132308967508879316380409015)
  ·
    refine ⟨198463451263318974570613523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132308967508879316380409015 198463451263318974570613523)
    ·
      refine ⟨297695176894978461855920285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198463451263318974570613523 297695176894978461855920285)
      ·
        refine ⟨111635691335616923195970107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297695176894978461855920285 111635691335616923195970107)
        ·
          refine ⟨167453537003425384793955161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111635691335616923195970107 167453537003425384793955161)
          ·
            refine ⟨125590152752569038595466371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167453537003425384793955161 125590152752569038595466371)
            ·
              refine ⟨188385229128853557893199557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125590152752569038595466371 188385229128853557893199557)
              ·
                refine ⟨35322230461660042104974917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188385229128853557893199557 35322230461660042104974917)
                ·
                  refine ⟨6622918211561257894682797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35322230461660042104974917 6622918211561257894682797)
                  ·
                    refine ⟨2483594329335471710506049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6622918211561257894682797 2483594329335471710506049)
                    ·
                      refine ⟨1862695747001603782879537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483594329335471710506049 1862695747001603782879537)
                      ·
                        rfl

theorem cell23_3627587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_3627587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627587 prefixEnd_3627587 := by exact prefixLift 3627587
  have htrace : WordTrace (prefixWord ++ tailWord_3627587) baseStart_3627587 baseEnd_3627587 := by
    simpa [prefixWord, tailWord_3627587, baseEnd_3627587] using wordTrace_append hprefix tailTrace_3627587
  have hstable : (prefixWord ++ tailWord_3627587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627587).length < 2 ^ (prefixWord ++ tailWord_3627587).sum := by decide
  have hdescent : baseEnd_3627587 < baseStart_3627587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627588 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3627588 : Nat := 118140960795 + 3627588 * 2 ^ 59
def prefixEnd_3627588 : Nat := 4983230072969 + 3 ^ 40 * 3627588 * 2
def baseEnd_3627588 : Nat := 620898753494086092989011

theorem tailTrace_3627588 : CollatzResearch.WordTrace tailWord_3627588 prefixEnd_3627588 620898753494086092989011 := by
  unfold tailWord_3627588
  simp only [CollatzResearch.WordTrace]
  refine ⟨66154501990937846775597709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88206002654583795700796945 66154501990937846775597709)
  ·
    refine ⟨24807938246601692540849141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66154501990937846775597709 24807938246601692540849141)
    ·
      refine ⟨2325744210618908675704607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24807938246601692540849141 2325744210618908675704607)
      ·
        refine ⟨3488616315928363013556911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325744210618908675704607 3488616315928363013556911)
        ·
          refine ⟨5232924473892544520335367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488616315928363013556911 5232924473892544520335367)
          ·
            refine ⟨7849386710838816780503051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5232924473892544520335367 7849386710838816780503051)
            ·
              refine ⟨11774080066258225170754577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849386710838816780503051 11774080066258225170754577)
              ·
                refine ⟨8830560049693668878065933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11774080066258225170754577 8830560049693668878065933)
                ·
                  refine ⟨3311460018635125829274725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830560049693668878065933 3311460018635125829274725)
                  ·
                    refine ⟨620898753494086092989011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311460018635125829274725 620898753494086092989011)
                    ·
                      rfl

theorem cell23_3627588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3627588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627588 prefixEnd_3627588 := by exact prefixLift 3627588
  have htrace : WordTrace (prefixWord ++ tailWord_3627588) baseStart_3627588 baseEnd_3627588 := by
    simpa [prefixWord, tailWord_3627588, baseEnd_3627588] using wordTrace_append hprefix tailTrace_3627588
  have hstable : (prefixWord ++ tailWord_3627588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627588).length < 2 ^ (prefixWord ++ tailWord_3627588).sum := by decide
  have hdescent : baseEnd_3627588 < baseStart_3627588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627594 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_3627594 : Nat := 118140960795 + 3627594 * 2 ^ 59
def prefixEnd_3627594 : Nat := 4983230072969 + 3 ^ 40 * 3627594 * 2
def baseEnd_3627594 : Nat := 1862699341366185255492005

theorem tailTrace_3627594 : CollatzResearch.WordTrace tailWord_3627594 prefixEnd_3627594 1862699341366185255492005 := by
  unfold tailWord_3627594
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077305704963489143978459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88206148546569304383942557 33077305704963489143978459)
  ·
    refine ⟨49615958557445233715967689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33077305704963489143978459 49615958557445233715967689)
    ·
      refine ⟨37211968918083925286975767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49615958557445233715967689 37211968918083925286975767)
      ·
        refine ⟨55817953377125887930463651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37211968918083925286975767 55817953377125887930463651)
        ·
          refine ⟨83726930065688831895695477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55817953377125887930463651 83726930065688831895695477)
          ·
            refine ⟨7849399693658327990221451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83726930065688831895695477 7849399693658327990221451)
            ·
              refine ⟨11774099540487491985332177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849399693658327990221451 11774099540487491985332177)
              ·
                refine ⟨8830574655365618988999133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11774099540487491985332177 8830574655365618988999133)
                ·
                  refine ⟨3311465495762107120874675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8830574655365618988999133 3311465495762107120874675)
                  ·
                    refine ⟨4967198243643160681312013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3311465495762107120874675 4967198243643160681312013)
                    ·
                      refine ⟨1862699341366185255492005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4967198243643160681312013 1862699341366185255492005)
                      ·
                        rfl

theorem cell23_3627594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_3627594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627594 prefixEnd_3627594 := by exact prefixLift 3627594
  have htrace : WordTrace (prefixWord ++ tailWord_3627594) baseStart_3627594 baseEnd_3627594 := by
    simpa [prefixWord, tailWord_3627594, baseEnd_3627594] using wordTrace_append hprefix tailTrace_3627594
  have hstable : (prefixWord ++ tailWord_3627594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627594).length < 2 ^ (prefixWord ++ tailWord_3627594).sum := by decide
  have hdescent : baseEnd_3627594 < baseStart_3627594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627604 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_3627604 : Nat := 118140960795 + 3627604 * 2 ^ 59
def prefixEnd_3627604 : Nat := 4983230072969 + 3 ^ 40 * 3627604 * 2
def baseEnd_3627604 : Nat := 1862704476172730216366959

theorem tailTrace_3627604 : CollatzResearch.WordTrace tailWord_3627604 prefixEnd_3627604 1862704476172730216366959 := by
  unfold tailWord_3627604
  simp only [CollatzResearch.WordTrace]
  refine ⟨66154793774908864141888933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88206391699878485522518577 66154793774908864141888933)
  ·
    refine ⟨12404023832795412026604175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66154793774908864141888933 12404023832795412026604175)
    ·
      refine ⟨18606035749193118039906263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12404023832795412026604175 18606035749193118039906263)
      ·
        refine ⟨27909053623789677059859395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18606035749193118039906263 27909053623789677059859395)
        ·
          refine ⟨41863580435684515589789093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27909053623789677059859395 41863580435684515589789093)
          ·
            refine ⟨7849421331690846673085455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41863580435684515589789093 7849421331690846673085455)
            ·
              refine ⟨11774131997536270009628183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7849421331690846673085455 11774131997536270009628183)
              ·
                refine ⟨17661197996304405014442275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11774131997536270009628183 17661197996304405014442275)
                ·
                  refine ⟨26491796994456607521663413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17661197996304405014442275 26491796994456607521663413)
                  ·
                    refine ⟨2483605968230306955155945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26491796994456607521663413 2483605968230306955155945)
                    ·
                      refine ⟨1862704476172730216366959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483605968230306955155945 1862704476172730216366959)
                      ·
                        rfl

theorem cell23_3627604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_3627604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627604 prefixEnd_3627604 := by exact prefixLift 3627604
  have htrace : WordTrace (prefixWord ++ tailWord_3627604) baseStart_3627604 baseEnd_3627604 := by
    simpa [prefixWord, tailWord_3627604, baseEnd_3627604] using wordTrace_append hprefix tailTrace_3627604
  have hstable : (prefixWord ++ tailWord_3627604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627604).length < 2 ^ (prefixWord ++ tailWord_3627604).sum := by decide
  have hdescent : baseEnd_3627604 < baseStart_3627604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627618 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 6]
def baseStart_3627618 : Nat := 118140960795 + 3627618 * 2 ^ 59
def prefixEnd_3627618 : Nat := 4983230072969 + 3 ^ 40 * 3627618 * 2
def baseEnd_3627618 : Nat := 206967962766877017954655

theorem tailTrace_3627618 : CollatzResearch.WordTrace tailWord_3627618 prefixEnd_3627618 206967962766877017954655 := by
  unfold tailWord_3627618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077524542941752168696877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88206732114511339116525005 33077524542941752168696877)
  ·
    refine ⟨12404071703603157063261329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33077524542941752168696877 12404071703603157063261329)
    ·
      refine ⟨9303053777702367797445997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12404071703603157063261329 9303053777702367797445997)
      ·
        refine ⟨3488645166638387924042249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9303053777702367797445997 3488645166638387924042249)
        ·
          refine ⟨2616483874978790943031687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488645166638387924042249 2616483874978790943031687)
          ·
            refine ⟨3924725812468186414547531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616483874978790943031687 3924725812468186414547531)
            ·
              refine ⟨5887088718702279621821297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924725812468186414547531 5887088718702279621821297)
              ·
                refine ⟨4415316539026709716365973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887088718702279621821297 4415316539026709716365973)
                ·
                  refine ⟨206967962766877017954655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4415316539026709716365973 206967962766877017954655)
                  ·
                    rfl

theorem cell23_3627618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_3627618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627618 prefixEnd_3627618 := by exact prefixLift 3627618
  have htrace : WordTrace (prefixWord ++ tailWord_3627618) baseStart_3627618 baseEnd_3627618 := by
    simpa [prefixWord, tailWord_3627618, baseEnd_3627618] using wordTrace_append hprefix tailTrace_3627618
  have hstable : (prefixWord ++ tailWord_3627618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627618).length < 2 ^ (prefixWord ++ tailWord_3627618).sum := by decide
  have hdescent : baseEnd_3627618 < baseStart_3627618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627627 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 2, 4]
def baseStart_3627627 : Nat := 118140960795 + 3627627 * 2 ^ 59
def prefixEnd_3627627 : Nat := 4983230072969 + 3 ^ 40 * 3627627 * 2
def baseEnd_3627627 : Nat := 620905428742594542126451

theorem tailTrace_3627627 : CollatzResearch.WordTrace tailWord_3627627 prefixEnd_3627627 620905428742594542126451 := by
  unfold tailWord_3627627
  simp only [CollatzResearch.WordTrace]
  refine ⟨132310426428734403211865135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88206950952489602141243423 132310426428734403211865135)
  ·
    refine ⟨198465639643101604817797703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132310426428734403211865135 198465639643101604817797703)
    ·
      refine ⟨297698459464652407226696555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198465639643101604817797703 297698459464652407226696555)
      ·
        refine ⟨446547689196978610840044833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297698459464652407226696555 446547689196978610840044833)
        ·
          refine ⟨334910766897733958130033625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446547689196978610840044833 334910766897733958130033625)
          ·
            refine ⟨251183075173300468597525219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334910766897733958130033625 251183075173300468597525219)
            ·
              refine ⟨376774612759950702896287829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251183075173300468597525219 376774612759950702896287829)
              ·
                refine ⟨4415327493280672299565873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 376774612759950702896287829 4415327493280672299565873)
                ·
                  refine ⟨3311495619960504224674405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415327493280672299565873 3311495619960504224674405)
                  ·
                    refine ⟨620905428742594542126451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311495619960504224674405 620905428742594542126451)
                    ·
                      rfl

theorem cell23_3627627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 4].length) (baseStart_3627627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627627 prefixEnd_3627627 := by exact prefixLift 3627627
  have htrace : WordTrace (prefixWord ++ tailWord_3627627) baseStart_3627627 baseEnd_3627627 := by
    simpa [prefixWord, tailWord_3627627, baseEnd_3627627] using wordTrace_append hprefix tailTrace_3627627
  have hstable : (prefixWord ++ tailWord_3627627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627627).length < 2 ^ (prefixWord ++ tailWord_3627627).sum := by decide
  have hdescent : baseEnd_3627627 < baseStart_3627627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627674 : List Nat := [3, 1, 1, 6, 1, 2, 9]
def baseStart_3627674 : Nat := 118140960795 + 3627674 * 2 ^ 59
def prefixEnd_3627674 : Nat := 4983230072969 + 3 ^ 40 * 3627674 * 2
def baseEnd_3627674 : Nat := 22996795306401789413477

theorem tailTrace_3627674 : CollatzResearch.WordTrace tailWord_3627674 prefixEnd_3627674 22996795306401789413477 := by
  unfold tailWord_3627674
  simp only [CollatzResearch.WordTrace]
  refine ⟨33078035164891032559706519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88208093773042753492550717 33078035164891032559706519)
  ·
    refine ⟨49617052747336548839559779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33078035164891032559706519 49617052747336548839559779)
    ·
      refine ⟨74425579121004823259339669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49617052747336548839559779 74425579121004823259339669)
      ·
        refine ⟨3488699021297101090281547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74425579121004823259339669 3488699021297101090281547)
        ·
          refine ⟨5233048531945651635422321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488699021297101090281547 5233048531945651635422321)
          ·
            refine ⟨3924786398959238726566741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5233048531945651635422321 3924786398959238726566741)
            ·
              refine ⟨22996795306401789413477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3924786398959238726566741 22996795306401789413477)
              ·
                rfl

theorem cell23_3627674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 9].length) (baseStart_3627674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627674 prefixEnd_3627674 := by exact prefixLift 3627674
  have htrace : WordTrace (prefixWord ++ tailWord_3627674) baseStart_3627674 baseEnd_3627674 := by
    simpa [prefixWord, tailWord_3627674, baseEnd_3627674] using wordTrace_append hprefix tailTrace_3627674
  have hstable : (prefixWord ++ tailWord_3627674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627674).length < 2 ^ (prefixWord ++ tailWord_3627674).sum := by decide
  have hdescent : baseEnd_3627674 < baseStart_3627674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627684 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 4, 1, 3]
def baseStart_3627684 : Nat := 118140960795 + 3627684 * 2 ^ 59
def prefixEnd_3627684 : Nat := 4983230072969 + 3 ^ 40 * 3627684 * 2
def baseEnd_3627684 : Nat := 1862745554625089903366591

theorem tailTrace_3627684 : CollatzResearch.WordTrace tailWord_3627684 prefixEnd_3627684 1862745554625089903366591 := by
  unfold tailWord_3627684
  simp only [CollatzResearch.WordTrace]
  refine ⟨66156252694763950973345053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88208336926351934631126737 66156252694763950973345053)
  ·
    refine ⟨24808594760536481615004395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66156252694763950973345053 24808594760536481615004395)
    ·
      refine ⟨37212892140804722422506593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24808594760536481615004395 37212892140804722422506593)
      ·
        refine ⟨27909669105603541816879945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37212892140804722422506593 27909669105603541816879945)
        ·
          refine ⟨20932251829202656362659959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27909669105603541816879945 20932251829202656362659959)
          ·
            refine ⟨31398377743803984543989939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20932251829202656362659959 31398377743803984543989939)
            ·
              refine ⟨47097566615705976815984909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31398377743803984543989939 47097566615705976815984909)
              ·
                refine ⟨17661587480889741305994341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47097566615705976815984909 17661587480889741305994341)
                ·
                  refine ⟨3311547652666826494873939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17661587480889741305994341 3311547652666826494873939)
                  ·
                    refine ⟨4967321479000239742310909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3311547652666826494873939 4967321479000239742310909)
                    ·
                      refine ⟨1862745554625089903366591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4967321479000239742310909 1862745554625089903366591)
                      ·
                        rfl

theorem cell23_3627684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_3627684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627684 prefixEnd_3627684 := by exact prefixLift 3627684
  have htrace : WordTrace (prefixWord ++ tailWord_3627684) baseStart_3627684 baseEnd_3627684 := by
    simpa [prefixWord, tailWord_3627684, baseEnd_3627684] using wordTrace_append hprefix tailTrace_3627684
  have hstable : (prefixWord ++ tailWord_3627684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627684).length < 2 ^ (prefixWord ++ tailWord_3627684).sum := by decide
  have hdescent : baseEnd_3627684 < baseStart_3627684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627711 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 1, 3, 2]
def baseStart_3627711 : Nat := 118140960795 + 3627711 * 2 ^ 59
def prefixEnd_3627711 : Nat := 4983230072969 + 3 ^ 40 * 3627711 * 2
def baseEnd_3627711 : Nat := 1862759418602761297728967

theorem tailTrace_3627711 : CollatzResearch.WordTrace tailWord_3627711 prefixEnd_3627711 1862759418602761297728967 := by
  unfold tailWord_3627711
  simp only [CollatzResearch.WordTrace]
  refine ⟨132313490160430085557922987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88208993440286723705281991 132313490160430085557922987)
  ·
    refine ⟨198470235240645128336884481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132313490160430085557922987 198470235240645128336884481)
    ·
      refine ⟨148852676430483846252663361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198470235240645128336884481 148852676430483846252663361)
      ·
        refine ⟨111639507322862884689497521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148852676430483846252663361 111639507322862884689497521)
        ·
          refine ⟨83729630492147163517123141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111639507322862884689497521 83729630492147163517123141)
          ·
            refine ⟨15699305717277593159460589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83729630492147163517123141 15699305717277593159460589)
            ·
              refine ⟨5887239643979097434797721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15699305717277593159460589 5887239643979097434797721)
              ·
                refine ⟨4415429732984323076098291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887239643979097434797721 4415429732984323076098291)
                ·
                  refine ⟨6623144599476484614147437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4415429732984323076098291 6623144599476484614147437)
                  ·
                    refine ⟨2483679224803681730305289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6623144599476484614147437 2483679224803681730305289)
                    ·
                      refine ⟨1862759418602761297728967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483679224803681730305289 1862759418602761297728967)
                      ·
                        rfl

theorem cell23_3627711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_3627711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627711 prefixEnd_3627711 := by exact prefixLift 3627711
  have htrace : WordTrace (prefixWord ++ tailWord_3627711) baseStart_3627711 baseEnd_3627711 := by
    simpa [prefixWord, tailWord_3627711, baseEnd_3627711] using wordTrace_append hprefix tailTrace_3627711
  have hstable : (prefixWord ++ tailWord_3627711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627711).length < 2 ^ (prefixWord ++ tailWord_3627711).sum := by decide
  have hdescent : baseEnd_3627711 < baseStart_3627711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627737 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3627737 : Nat := 118140960795 + 3627737 * 2 ^ 59
def prefixEnd_3627737 : Nat := 4983230072969 + 3 ^ 40 * 3627737 * 2
def baseEnd_3627737 : Nat := 1862772769099778196003847

theorem tailTrace_3627737 : CollatzResearch.WordTrace tailWord_3627737 prefixEnd_3627737 1862772769099778196003847 := by
  unfold tailWord_3627737
  simp only [CollatzResearch.WordTrace]
  refine ⟨132314438458335891998369465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88209625638890594665579643 132314438458335891998369465)
  ·
    refine ⟨99235828843751918998777099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132314438458335891998369465 99235828843751918998777099)
    ·
      refine ⟨148853743265627878498165649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99235828843751918998777099 148853743265627878498165649)
      ·
        refine ⟨111640307449220908873624237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148853743265627878498165649 111640307449220908873624237)
        ·
          refine ⟨41865115293457840827609089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111640307449220908873624237 41865115293457840827609089)
          ·
            refine ⟨31398836470093380620706817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41865115293457840827609089 31398836470093380620706817)
            ·
              refine ⟨23549127352570035465530113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31398836470093380620706817 23549127352570035465530113)
              ·
                refine ⟨17661845514427526599147585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23549127352570035465530113 17661845514427526599147585)
                ·
                  refine ⟨13246384135820644949360689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17661845514427526599147585 13246384135820644949360689)
                  ·
                    refine ⟨9934788101865483712020517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13246384135820644949360689 9934788101865483712020517)
                    ·
                      refine ⟨1862772769099778196003847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9934788101865483712020517 1862772769099778196003847)
                      ·
                        rfl

theorem cell23_3627737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3627737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627737 prefixEnd_3627737 := by exact prefixLift 3627737
  have htrace : WordTrace (prefixWord ++ tailWord_3627737) baseStart_3627737 baseEnd_3627737 := by
    simpa [prefixWord, tailWord_3627737, baseEnd_3627737] using wordTrace_append hprefix tailTrace_3627737
  have hstable : (prefixWord ++ tailWord_3627737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627737).length < 2 ^ (prefixWord ++ tailWord_3627737).sum := by decide
  have hdescent : baseEnd_3627737 < baseStart_3627737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627758 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_3627758 : Nat := 118140960795 + 3627758 * 2 ^ 59
def prefixEnd_3627758 : Nat := 4983230072969 + 3 ^ 40 * 3627758 * 2
def baseEnd_3627758 : Nat := 1862783552193522613841251

theorem tailTrace_3627758 : CollatzResearch.WordTrace tailWord_3627758 prefixEnd_3627758 1862783552193522613841251 := by
  unfold tailWord_3627758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16539400548907476573110491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88210136260839875056589285 16539400548907476573110491)
  ·
    refine ⟨24809100823361214859665737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16539400548907476573110491 24809100823361214859665737)
    ·
      refine ⟨18606825617520911144749303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24809100823361214859665737 18606825617520911144749303)
      ·
        refine ⟨27910238426281366717123955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18606825617520911144749303 27910238426281366717123955)
        ·
          refine ⟨41865357639422050075685933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27910238426281366717123955 41865357639422050075685933)
          ·
            refine ⟨15699509114783268778382225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41865357639422050075685933 15699509114783268778382225)
            ·
              refine ⟨11774631836087451583786669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15699509114783268778382225 11774631836087451583786669)
              ·
                refine ⟨4415486938532794343920001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11774631836087451583786669 4415486938532794343920001)
                ·
                  refine ⟨3311615203899595757940001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415486938532794343920001 3311615203899595757940001)
                  ·
                    refine ⟨2483711402924696818455001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3311615203899595757940001 2483711402924696818455001)
                    ·
                      refine ⟨1862783552193522613841251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483711402924696818455001 1862783552193522613841251)
                      ·
                        rfl

theorem cell23_3627758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_3627758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627758 prefixEnd_3627758 := by exact prefixLift 3627758
  have htrace : WordTrace (prefixWord ++ tailWord_3627758) baseStart_3627758 baseEnd_3627758 := by
    simpa [prefixWord, tailWord_3627758, baseEnd_3627758] using wordTrace_append hprefix tailTrace_3627758
  have hstable : (prefixWord ++ tailWord_3627758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627758).length < 2 ^ (prefixWord ++ tailWord_3627758).sum := by decide
  have hdescent : baseEnd_3627758 < baseStart_3627758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627884 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_3627884 : Nat := 118140960795 + 3627884 * 2 ^ 59
def prefixEnd_3627884 : Nat := 4983230072969 + 3 ^ 40 * 3627884 * 2
def baseEnd_3627884 : Nat := 620949416918663040288557

theorem tailTrace_3627884 : CollatzResearch.WordTrace tailWord_3627884 prefixEnd_3627884 620949416918663040288557 := by
  unfold tailWord_3627884
  simp only [CollatzResearch.WordTrace]
  refine ⟨66159899994401668051985353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88213199992535557402647137 66159899994401668051985353)
  ·
    refine ⟨49619924995801251038989015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66159899994401668051985353 49619924995801251038989015)
    ·
      refine ⟨74429887493701876558483523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49619924995801251038989015 74429887493701876558483523)
      ·
        refine ⟨111644831240552814837725285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74429887493701876558483523 111644831240552814837725285)
        ·
          refine ⟨20933405857603652782073491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111644831240552814837725285 20933405857603652782073491)
          ·
            refine ⟨31400108786405479173110237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20933405857603652782073491 31400108786405479173110237)
            ·
              refine ⟨11775040794902054689916339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31400108786405479173110237 11775040794902054689916339)
              ·
                refine ⟨17662561192353082034874509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11775040794902054689916339 17662561192353082034874509)
                ·
                  refine ⟨6623460447132405763077941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17662561192353082034874509 6623460447132405763077941)
                  ·
                    refine ⟨620949416918663040288557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6623460447132405763077941 620949416918663040288557)
                    ·
                      rfl

theorem cell23_3627884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_3627884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627884 prefixEnd_3627884 := by exact prefixLift 3627884
  have htrace : WordTrace (prefixWord ++ tailWord_3627884) baseStart_3627884 baseEnd_3627884 := by
    simpa [prefixWord, tailWord_3627884, baseEnd_3627884] using wordTrace_append hprefix tailTrace_3627884
  have hstable : (prefixWord ++ tailWord_3627884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627884).length < 2 ^ (prefixWord ++ tailWord_3627884).sum := by decide
  have hdescent : baseEnd_3627884 < baseStart_3627884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627891 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 2, 3, 2]
def baseStart_3627891 : Nat := 118140960795 + 3627891 * 2 ^ 59
def prefixEnd_3627891 : Nat := 4983230072969 + 3 ^ 40 * 3627891 * 2
def baseEnd_3627891 : Nat := 1862851845120570593478139

theorem tailTrace_3627891 : CollatzResearch.WordTrace tailWord_3627891 prefixEnd_3627891 1862851845120570593478139 := by
  unfold tailWord_3627891
  simp only [CollatzResearch.WordTrace]
  refine ⟨132320055299777976299475527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88213370199851984199650351 132320055299777976299475527)
  ·
    refine ⟨198480082949666964449213291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132320055299777976299475527 198480082949666964449213291)
    ·
      refine ⟨297720124424500446673819937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198480082949666964449213291 297720124424500446673819937)
      ·
        refine ⟨223290093318375335005364953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297720124424500446673819937 223290093318375335005364953)
        ·
          refine ⟨167467569988781501254023715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223290093318375335005364953 167467569988781501254023715)
          ·
            refine ⟨251201354983172251881035573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167467569988781501254023715 251201354983172251881035573)
            ·
              refine ⟨23550127029672398613847085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251201354983172251881035573 23550127029672398613847085)
              ·
                refine ⟨8831297636127149480192657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23550127029672398613847085 8831297636127149480192657)
                ·
                  refine ⟨6623473227095362110144493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8831297636127149480192657 6623473227095362110144493)
                  ·
                    refine ⟨2483802460160760791304185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6623473227095362110144493 2483802460160760791304185)
                    ·
                      refine ⟨1862851845120570593478139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483802460160760791304185 1862851845120570593478139)
                      ·
                        rfl

theorem cell23_3627891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3, 2].length) (baseStart_3627891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627891 prefixEnd_3627891 := by exact prefixLift 3627891
  have htrace : WordTrace (prefixWord ++ tailWord_3627891) baseStart_3627891 baseEnd_3627891 := by
    simpa [prefixWord, tailWord_3627891, baseEnd_3627891] using wordTrace_append hprefix tailTrace_3627891
  have hstable : (prefixWord ++ tailWord_3627891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627891).length < 2 ^ (prefixWord ++ tailWord_3627891).sum := by decide
  have hdescent : baseEnd_3627891 < baseStart_3627891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627898 : List Nat := [3, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3]
def baseStart_3627898 : Nat := 118140960795 + 3627898 * 2 ^ 59
def prefixEnd_3627898 : Nat := 4983230072969 + 3 ^ 40 * 3627898 * 2
def baseEnd_3627898 : Nat := 1862855439485152066090607

theorem tailTrace_3627898 : CollatzResearch.WordTrace tailWord_3627898 prefixEnd_3627898 1862855439485152066090607 := by
  unfold tailWord_3627898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33080077652688154123745087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88213540407168410996653565 33080077652688154123745087)
  ·
    refine ⟨49620116479032231185617631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33080077652688154123745087 49620116479032231185617631)
    ·
      refine ⟨74430174718548346778426447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49620116479032231185617631 74430174718548346778426447)
      ·
        refine ⟨111645262077822520167639671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74430174718548346778426447 111645262077822520167639671)
        ·
          refine ⟨167467893116733780251459507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111645262077822520167639671 167467893116733780251459507)
          ·
            refine ⟨251201839675100670377189261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167467893116733780251459507 251201839675100670377189261)
            ·
              refine ⟨94200689878162751391445973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251201839675100670377189261 94200689878162751391445973)
              ·
                refine ⟨2207828669019439485737015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 94200689878162751391445973 2207828669019439485737015)
                ·
                  refine ⟨3311743003529159228605523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207828669019439485737015 3311743003529159228605523)
                  ·
                    refine ⟨4967614505293738842908285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3311743003529159228605523 4967614505293738842908285)
                    ·
                      refine ⟨1862855439485152066090607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4967614505293738842908285 1862855439485152066090607)
                      ·
                        rfl

theorem cell23_3627898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_3627898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627898 prefixEnd_3627898 := by exact prefixLift 3627898
  have htrace : WordTrace (prefixWord ++ tailWord_3627898) baseStart_3627898 baseEnd_3627898 := by
    simpa [prefixWord, tailWord_3627898, baseEnd_3627898] using wordTrace_append hprefix tailTrace_3627898
  have hstable : (prefixWord ++ tailWord_3627898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627898).length < 2 ^ (prefixWord ++ tailWord_3627898).sum := by decide
  have hdescent : baseEnd_3627898 < baseStart_3627898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627915 : List Nat := [1, 1, 1, 1, 4, 2, 6, 2, 1, 1, 3]
def baseStart_3627915 : Nat := 118140960795 + 3627915 * 2 ^ 59
def prefixEnd_3627915 : Nat := 4983230072969 + 3 ^ 40 * 3627915 * 2
def baseEnd_3627915 : Nat := 1862864168656278499578029

theorem tailTrace_3627915 : CollatzResearch.WordTrace tailWord_3627915 prefixEnd_3627915 1862864168656278499578029 := by
  unfold tailWord_3627915
  simp only [CollatzResearch.WordTrace]
  refine ⟨132320930651691028398349199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88213953767794018932232799 132320930651691028398349199)
  ·
    refine ⟨198481395977536542597523799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132320930651691028398349199 198481395977536542597523799)
    ·
      refine ⟨297722093966304813896285699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198481395977536542597523799 297722093966304813896285699)
      ·
        refine ⟨446583140949457220844428549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297722093966304813896285699 446583140949457220844428549)
        ·
          refine ⟨83734338928023228908330353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446583140949457220844428549 83734338928023228908330353)
          ·
            refine ⟨62800754196017421681247765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83734338928023228908330353 62800754196017421681247765)
            ·
              refine ⟨2943785352938316641308489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62800754196017421681247765 2943785352938316641308489)
              ·
                refine ⟨2207839014703737480981367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943785352938316641308489 2207839014703737480981367)
                ·
                  refine ⟨3311758522055606221472051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207839014703737480981367 3311758522055606221472051)
                  ·
                    refine ⟨4967637783083409332208077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3311758522055606221472051 4967637783083409332208077)
                    ·
                      refine ⟨1862864168656278499578029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4967637783083409332208077 1862864168656278499578029)
                      ·
                        rfl

theorem cell23_3627915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 1, 1, 3].length) (baseStart_3627915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627915 prefixEnd_3627915 := by exact prefixLift 3627915
  have htrace : WordTrace (prefixWord ++ tailWord_3627915) baseStart_3627915 baseEnd_3627915 := by
    simpa [prefixWord, tailWord_3627915, baseEnd_3627915] using wordTrace_append hprefix tailTrace_3627915
  have hstable : (prefixWord ++ tailWord_3627915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627915).length < 2 ^ (prefixWord ++ tailWord_3627915).sum := by decide
  have hdescent : baseEnd_3627915 < baseStart_3627915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627949 : List Nat := [1, 5, 2, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_3627949 : Nat := 118140960795 + 3627949 * 2 ^ 59
def prefixEnd_3627949 : Nat := 4983230072969 + 3 ^ 40 * 3627949 * 2
def baseEnd_3627949 : Nat := 1862881626998531366552873

theorem tailTrace_3627949 : CollatzResearch.WordTrace tailWord_3627949 prefixEnd_3627949 1862881626998531366552873 := by
  unfold tailWord_3627949
  simp only [CollatzResearch.WordTrace]
  refine ⟨132322170733567852205086901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88214780489045234803391267 132322170733567852205086901)
  ·
    refine ⟨12405203506271986144226897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132322170733567852205086901 12405203506271986144226897)
    ·
      refine ⟨9303902629703989608170173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12405203506271986144226897 9303902629703989608170173)
      ·
        refine ⟨3488963486138996103063815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9303902629703989608170173 3488963486138996103063815)
        ·
          refine ⟨5233445229208494154595723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3488963486138996103063815 5233445229208494154595723)
          ·
            refine ⟨7850167843812741231893585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5233445229208494154595723 7850167843812741231893585)
            ·
              refine ⟨5887625882859555923920189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7850167843812741231893585 5887625882859555923920189)
              ·
                refine ⟨2207859706072333471470071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5887625882859555923920189 2207859706072333471470071)
                ·
                  refine ⟨3311789559108500207205107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2207859706072333471470071 3311789559108500207205107)
                  ·
                    refine ⟨4967684338662750310807661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3311789559108500207205107 4967684338662750310807661)
                    ·
                      refine ⟨1862881626998531366552873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4967684338662750310807661 1862881626998531366552873)
                      ·
                        rfl

theorem cell23_3627949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_3627949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627949 prefixEnd_3627949 := by exact prefixLift 3627949
  have htrace : WordTrace (prefixWord ++ tailWord_3627949) baseStart_3627949 baseEnd_3627949 := by
    simpa [prefixWord, tailWord_3627949, baseEnd_3627949] using wordTrace_append hprefix tailTrace_3627949
  have hstable : (prefixWord ++ tailWord_3627949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627949).length < 2 ^ (prefixWord ++ tailWord_3627949).sum := by decide
  have hdescent : baseEnd_3627949 < baseStart_3627949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627965 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_3627965 : Nat := 118140960795 + 3627965 * 2 ^ 59
def prefixEnd_3627965 : Nat := 4983230072969 + 3 ^ 40 * 3627965 * 2
def baseEnd_3627965 : Nat := 620963280896334434650933

theorem tailTrace_3627965 : CollatzResearch.WordTrace tailWord_3627965 prefixEnd_3627965 620963280896334434650933 := by
  unfold tailWord_3627965
  simp only [CollatzResearch.WordTrace]
  refine ⟨132322754301509886937669349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88215169534339924625112899 132322754301509886937669349)
  ·
    refine ⟨24810516431533103800813003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132322754301509886937669349 24810516431533103800813003)
    ·
      refine ⟨37215774647299655701219505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24810516431533103800813003 37215774647299655701219505)
      ·
        refine ⟨27911830985474741775914629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37215774647299655701219505 27911830985474741775914629)
        ·
          refine ⟨5233468309776514082983993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27911830985474741775914629 5233468309776514082983993)
          ·
            refine ⟨3925101232332385562237995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5233468309776514082983993 3925101232332385562237995)
            ·
              refine ⟨5887651848498578343356993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925101232332385562237995 5887651848498578343356993)
              ·
                refine ⟨4415738886373933757517745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5887651848498578343356993 4415738886373933757517745)
                ·
                  refine ⟨3311804164780450318138309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4415738886373933757517745 3311804164780450318138309)
                  ·
                    refine ⟨620963280896334434650933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3311804164780450318138309 620963280896334434650933)
                    ·
                      rfl

theorem cell23_3627965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_3627965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627965 prefixEnd_3627965 := by exact prefixLift 3627965
  have htrace : WordTrace (prefixWord ++ tailWord_3627965) baseStart_3627965 baseEnd_3627965 := by
    simpa [prefixWord, tailWord_3627965, baseEnd_3627965] using wordTrace_append hprefix tailTrace_3627965
  have hstable : (prefixWord ++ tailWord_3627965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627965).length < 2 ^ (prefixWord ++ tailWord_3627965).sum := by decide
  have hdescent : baseEnd_3627965 < baseStart_3627965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627971 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 3]
def baseStart_3627971 : Nat := 118140960795 + 3627971 * 2 ^ 59
def prefixEnd_3627971 : Nat := 4983230072969 + 3 ^ 40 * 3627971 * 2
def baseEnd_3627971 : Nat := 1862892923572930280477771

theorem tailTrace_3627971 : CollatzResearch.WordTrace tailWord_3627971 prefixEnd_3627971 1862892923572930280477771 := by
  unfold tailWord_3627971
  simp only [CollatzResearch.WordTrace]
  refine ⟨132322973139488149962387767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88215315426325433308258511 132322973139488149962387767)
  ·
    refine ⟨198484459709232224943581651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132322973139488149962387767 198484459709232224943581651)
    ·
      refine ⟨297726689563848337415372477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198484459709232224943581651 297726689563848337415372477)
      ·
        refine ⟨111647508586443126530764679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297726689563848337415372477 111647508586443126530764679)
        ·
          refine ⟨167471262879664689796147019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111647508586443126530764679 167471262879664689796147019)
          ·
            refine ⟨251206894319497034694220529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167471262879664689796147019 251206894319497034694220529)
            ·
              refine ⟨188405170739622776020665397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251206894319497034694220529 188405170739622776020665397)
              ·
                refine ⟨17662984756839635251937381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188405170739622776020665397 17662984756839635251937381)
                ·
                  refine ⟨3311809641907431609738259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17662984756839635251937381 3311809641907431609738259)
                  ·
                    refine ⟨4967714462861147414607389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3311809641907431609738259 4967714462861147414607389)
                    ·
                      refine ⟨1862892923572930280477771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4967714462861147414607389 1862892923572930280477771)
                      ·
                        rfl

theorem cell23_3627971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_3627971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627971 prefixEnd_3627971 := by exact prefixLift 3627971
  have htrace : WordTrace (prefixWord ++ tailWord_3627971) baseStart_3627971 baseEnd_3627971 := by
    simpa [prefixWord, tailWord_3627971, baseEnd_3627971] using wordTrace_append hprefix tailTrace_3627971
  have hstable : (prefixWord ++ tailWord_3627971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627971).length < 2 ^ (prefixWord ++ tailWord_3627971).sum := by decide
  have hdescent : baseEnd_3627971 < baseStart_3627971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3627988 : List Nat := [2, 4, 1, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_3627988 : Nat := 118140960795 + 3627988 * 2 ^ 59
def prefixEnd_3627988 : Nat := 4983230072969 + 3 ^ 40 * 3627988 * 2
def baseEnd_3627988 : Nat := 1862901652744056713965193

theorem tailTrace_3627988 : CollatzResearch.WordTrace tailWord_3627988 prefixEnd_3627988 1862901652744056713965193 := by
  unfold tailWord_3627988
  simp only [CollatzResearch.WordTrace]
  refine ⟨66161796590213280932878309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88215728786951041243837745 66161796590213280932878309)
  ·
    refine ⟨12405336860664990174914683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66161796590213280932878309 12405336860664990174914683)
    ·
      refine ⟨18608005290997485262372025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12405336860664990174914683 18608005290997485262372025)
      ·
        refine ⟨13956003968248113946779019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18608005290997485262372025 13956003968248113946779019)
        ·
          refine ⟨20934005952372170920168529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13956003968248113946779019 20934005952372170920168529)
          ·
            refine ⟨15700504464279128190126397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20934005952372170920168529 15700504464279128190126397)
            ·
              refine ⟨5887689174104673071297399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15700504464279128190126397 5887689174104673071297399)
              ·
                refine ⟨8831533761157009606946099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5887689174104673071297399 8831533761157009606946099)
                ·
                  refine ⟨13247300641735514410419149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8831533761157009606946099 13247300641735514410419149)
                  ·
                    refine ⟨4967737740650817903907181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13247300641735514410419149 4967737740650817903907181)
                    ·
                      refine ⟨1862901652744056713965193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4967737740650817903907181 1862901652744056713965193)
                      ·
                        rfl

theorem cell23_3627988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_3627988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3627988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3627988 prefixEnd_3627988 := by exact prefixLift 3627988
  have htrace : WordTrace (prefixWord ++ tailWord_3627988) baseStart_3627988 baseEnd_3627988 := by
    simpa [prefixWord, tailWord_3627988, baseEnd_3627988] using wordTrace_append hprefix tailTrace_3627988
  have hstable : (prefixWord ++ tailWord_3627988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3627988).length < 2 ^ (prefixWord ++ tailWord_3627988).sum := by decide
  have hdescent : baseEnd_3627988 < baseStart_3627988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3627988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628004 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_3628004 : Nat := 118140960795 + 3628004 * 2 ^ 59
def prefixEnd_3628004 : Nat := 4983230072969 + 3 ^ 40 * 3628004 * 2
def baseEnd_3628004 : Nat := 620969956144842883788373

theorem tailTrace_3628004 : CollatzResearch.WordTrace tailWord_3628004 prefixEnd_3628004 620969956144842883788373 := by
  unfold tailWord_3628004
  simp only [CollatzResearch.WordTrace]
  refine ⟨66162088374184298299169533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88216117832245731065559377 66162088374184298299169533)
  ·
    refine ⟨24810783140319111862188575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66162088374184298299169533 24810783140319111862188575)
    ·
      refine ⟨37216174710478667793282863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24810783140319111862188575 37216174710478667793282863)
      ·
        refine ⟨55824262065718001689924295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37216174710478667793282863 55824262065718001689924295)
        ·
          refine ⟨83736393098577002534886443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55824262065718001689924295 83736393098577002534886443)
          ·
            refine ⟨125604589647865503802329665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83736393098577002534886443 125604589647865503802329665)
            ·
              refine ⟨94203442235899127851747249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125604589647865503802329665 94203442235899127851747249)
              ·
                refine ⟨70652581676924345888810437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94203442235899127851747249 70652581676924345888810437)
                ·
                  refine ⟨13247359064423314854151957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70652581676924345888810437 13247359064423314854151957)
                  ·
                    refine ⟨620969956144842883788373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13247359064423314854151957 620969956144842883788373)
                    ·
                      rfl

theorem cell23_3628004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_3628004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628004 prefixEnd_3628004 := by exact prefixLift 3628004
  have htrace : WordTrace (prefixWord ++ tailWord_3628004) baseStart_3628004 baseEnd_3628004 := by
    simpa [prefixWord, tailWord_3628004, baseEnd_3628004] using wordTrace_append hprefix tailTrace_3628004
  have hstable : (prefixWord ++ tailWord_3628004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628004).length < 2 ^ (prefixWord ++ tailWord_3628004).sum := by decide
  have hdescent : baseEnd_3628004 < baseStart_3628004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628078 : List Nat := [4, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3628078 : Nat := 118140960795 + 3628078 * 2 ^ 59
def prefixEnd_3628078 : Nat := 4983230072969 + 3 ^ 40 * 3628078 * 2
def baseEnd_3628078 : Nat := 1862947866002961361839779

theorem tailTrace_3628078 : CollatzResearch.WordTrace tailWord_3628078 prefixEnd_3628078 1862947866002961361839779 := by
  unfold tailWord_3628078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16540859468762563404566611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88217917166733671491021925 16540859468762563404566611)
  ·
    refine ⟨24811289203143845106849917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16540859468762563404566611 24811289203143845106849917)
    ·
      refine ⟨9304233451178941915068719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24811289203143845106849917 9304233451178941915068719)
      ·
        refine ⟨13956350176768412872603079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9304233451178941915068719 13956350176768412872603079)
        ·
          refine ⟨20934525265152619308904619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13956350176768412872603079 20934525265152619308904619)
          ·
            refine ⟨31401787897728928963356929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20934525265152619308904619 31401787897728928963356929)
            ·
              refine ⟨23551340923296696722517697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31401787897728928963356929 23551340923296696722517697)
              ·
                refine ⟨17663505692472522541888273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23551340923296696722517697 17663505692472522541888273)
                ·
                  refine ⟨13247629269354391906416205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17663505692472522541888273 13247629269354391906416205)
                  ·
                    refine ⟨4967860976007896964906077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13247629269354391906416205 4967860976007896964906077)
                    ·
                      refine ⟨1862947866002961361839779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4967860976007896964906077 1862947866002961361839779)
                      ·
                        rfl

theorem cell23_3628078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3628078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628078 prefixEnd_3628078 := by exact prefixLift 3628078
  have htrace : WordTrace (prefixWord ++ tailWord_3628078) baseStart_3628078 baseEnd_3628078 := by
    simpa [prefixWord, tailWord_3628078, baseEnd_3628078] using wordTrace_append hprefix tailTrace_3628078
  have hstable : (prefixWord ++ tailWord_3628078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628078).length < 2 ^ (prefixWord ++ tailWord_3628078).sum := by decide
  have hdescent : baseEnd_3628078 < baseStart_3628078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628081 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 2, 5]
def baseStart_3628081 : Nat := 118140960795 + 3628081 * 2 ^ 59
def prefixEnd_3628081 : Nat := 4983230072969 + 3 ^ 40 * 3628081 * 2
def baseEnd_3628081 : Nat := 620983135481641616700755

theorem tailTrace_3628081 : CollatzResearch.WordTrace tailWord_3628081 prefixEnd_3628081 620983135481641616700755 := by
  unfold tailWord_3628081
  simp only [CollatzResearch.WordTrace]
  refine ⟨132326985169089638748892097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88217990112726425832594731 132326985169089638748892097)
  ·
    refine ⟨99245238876817229061669073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132326985169089638748892097 99245238876817229061669073)
    ·
      refine ⟨74433929157612921796251805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99245238876817229061669073 74433929157612921796251805)
      ·
        refine ⟨27912723434104845673594427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74433929157612921796251805 27912723434104845673594427)
        ·
          refine ⟨41869085151157268510391641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27912723434104845673594427 41869085151157268510391641)
          ·
            refine ⟨31401813863367951382793731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41869085151157268510391641 31401813863367951382793731)
            ·
              refine ⟨47102720795051927074190597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31401813863367951382793731 47102720795051927074190597)
              ·
                refine ⟨8831760149072236326410737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47102720795051927074190597 8831760149072236326410737)
                ·
                  refine ⟨6623820111804177244808053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8831760149072236326410737 6623820111804177244808053)
                  ·
                    refine ⟨620983135481641616700755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6623820111804177244808053 620983135481641616700755)
                    ·
                      rfl

theorem cell23_3628081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_3628081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628081 prefixEnd_3628081 := by exact prefixLift 3628081
  have htrace : WordTrace (prefixWord ++ tailWord_3628081) baseStart_3628081 baseEnd_3628081 := by
    simpa [prefixWord, tailWord_3628081, baseEnd_3628081] using wordTrace_append hprefix tailTrace_3628081
  have hstable : (prefixWord ++ tailWord_3628081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628081).length < 2 ^ (prefixWord ++ tailWord_3628081).sum := by decide
  have hdescent : baseEnd_3628081 < baseStart_3628081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628088 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 2, 5, 2]
def baseStart_3628088 : Nat := 118140960795 + 3628088 * 2 ^ 59
def prefixEnd_3628088 : Nat := 4983230072969 + 3 ^ 40 * 3628088 * 2
def baseEnd_3628088 : Nat := 1862953000809506322714733

theorem tailTrace_3628088 : CollatzResearch.WordTrace tailWord_3628088 prefixEnd_3628088 1862953000809506322714733 := by
  unfold tailWord_3628088
  simp only [CollatzResearch.WordTrace]
  refine ⟨66163620240032139472198459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88218160320042852629597945 66163620240032139472198459)
  ·
    refine ⟨99245430360048209208297689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66163620240032139472198459 99245430360048209208297689)
    ·
      refine ⟨74434072770036156906223267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99245430360048209208297689 74434072770036156906223267)
      ·
        refine ⟨111651109155054235359334901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74434072770036156906223267 111651109155054235359334901)
        ·
          refine ⟨10467291483286334564937647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111651109155054235359334901 10467291483286334564937647)
          ·
            refine ⟨15700937224929501847406471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467291483286334564937647 15700937224929501847406471)
            ·
              refine ⟨23551405837394252771109707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15700937224929501847406471 23551405837394252771109707)
              ·
                refine ⟨35327108756091379156664561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23551405837394252771109707 35327108756091379156664561)
                ·
                  refine ⟨26495331567068534367498421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35327108756091379156664561 26495331567068534367498421)
                  ·
                    refine ⟨2483937334412675096952977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26495331567068534367498421 2483937334412675096952977)
                    ·
                      refine ⟨1862953000809506322714733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2483937334412675096952977 1862953000809506322714733)
                      ·
                        rfl

theorem cell23_3628088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_3628088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628088 prefixEnd_3628088 := by exact prefixLift 3628088
  have htrace : WordTrace (prefixWord ++ tailWord_3628088) baseStart_3628088 baseEnd_3628088 := by
    simpa [prefixWord, tailWord_3628088, baseEnd_3628088] using wordTrace_append hprefix tailTrace_3628088
  have hstable : (prefixWord ++ tailWord_3628088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628088).length < 2 ^ (prefixWord ++ tailWord_3628088).sum := by decide
  have hdescent : baseEnd_3628088 < baseStart_3628088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628101 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_3628101 : Nat := 118140960795 + 3628101 * 2 ^ 59
def prefixEnd_3628101 : Nat := 4983230072969 + 3 ^ 40 * 3628101 * 2
def baseEnd_3628101 : Nat := 1862959676058014771852173

theorem tailTrace_3628101 : CollatzResearch.WordTrace tailWord_3628101 prefixEnd_3628101 1862959676058014771852173 := by
  unfold tailWord_3628101
  simp only [CollatzResearch.WordTrace]
  refine ⟨132327714629017182164620157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88218476419344788109746771 132327714629017182164620157)
  ·
    refine ⟨49622892985881443311732559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132327714629017182164620157 49622892985881443311732559)
    ·
      refine ⟨74434339478822164967598839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49622892985881443311732559 74434339478822164967598839)
      ·
        refine ⟨111651509218233247451398259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74434339478822164967598839 111651509218233247451398259)
        ·
          refine ⟨167477263827349871177097389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111651509218233247451398259 167477263827349871177097389)
          ·
            refine ⟨62803973935256201691411521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167477263827349871177097389 62803973935256201691411521)
            ·
              refine ⟨47102980451442151268558641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62803973935256201691411521 47102980451442151268558641)
              ·
                refine ⟨35327235338581613451418981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47102980451442151268558641 35327235338581613451418981)
                ·
                  refine ⟨6623856625984052522141059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35327235338581613451418981 6623856625984052522141059)
                  ·
                    refine ⟨9935784938976078783211589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6623856625984052522141059 9935784938976078783211589)
                    ·
                      refine ⟨1862959676058014771852173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9935784938976078783211589 1862959676058014771852173)
                      ·
                        rfl

theorem cell23_3628101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_3628101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628101 prefixEnd_3628101 := by exact prefixLift 3628101
  have htrace : WordTrace (prefixWord ++ tailWord_3628101) baseStart_3628101 baseEnd_3628101 := by
    simpa [prefixWord, tailWord_3628101, baseEnd_3628101] using wordTrace_append hprefix tailTrace_3628101
  have hstable : (prefixWord ++ tailWord_3628101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628101).length < 2 ^ (prefixWord ++ tailWord_3628101).sum := by decide
  have hdescent : baseEnd_3628101 < baseStart_3628101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628171 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 3, 5]
def baseStart_3628171 : Nat := 118140960795 + 3628171 * 2 ^ 59
def prefixEnd_3628171 : Nat := 4983230072969 + 3 ^ 40 * 3628171 * 2
def baseEnd_3628171 : Nat := 620998539901276499325617

theorem tailTrace_3628171 : CollatzResearch.WordTrace tailWord_3628171 prefixEnd_3628171 620998539901276499325617 := by
  unfold tailWord_3628171
  simp only [CollatzResearch.WordTrace]
  refine ⟨132330267738763584119668367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88220178492509056079778911 132330267738763584119668367)
  ·
    refine ⟨198495401608145376179502551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132330267738763584119668367 198495401608145376179502551)
    ·
      refine ⟨297743102412218064269253827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198495401608145376179502551 297743102412218064269253827)
      ·
        refine ⟨446614653618327096403880741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297743102412218064269253827 446614653618327096403880741)
        ·
          refine ⟨83740247553436330575727639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446614653618327096403880741 83740247553436330575727639)
          ·
            refine ⟨125610371330154495863591459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83740247553436330575727639 125610371330154495863591459)
            ·
              refine ⟨188415556995231743795387189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125610371330154495863591459 188415556995231743795387189)
              ·
                refine ⟨17663958468302975980817549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188415556995231743795387189 17663958468302975980817549)
                ·
                  refine ⟨6623984425613615992806581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17663958468302975980817549 6623984425613615992806581)
                  ·
                    refine ⟨620998539901276499325617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6623984425613615992806581 620998539901276499325617)
                    ·
                      rfl

theorem cell23_3628171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 5].length) (baseStart_3628171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628171 prefixEnd_3628171 := by exact prefixLift 3628171
  have htrace : WordTrace (prefixWord ++ tailWord_3628171) baseStart_3628171 baseEnd_3628171 := by
    simpa [prefixWord, tailWord_3628171, baseEnd_3628171] using wordTrace_append hprefix tailTrace_3628171
  have hstable : (prefixWord ++ tailWord_3628171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628171).length < 2 ^ (prefixWord ++ tailWord_3628171).sum := by decide
  have hdescent : baseEnd_3628171 < baseStart_3628171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628222 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_3628222 : Nat := 118140960795 + 3628222 * 2 ^ 59
def prefixEnd_3628222 : Nat := 4983230072969 + 3 ^ 40 * 3628222 * 2
def baseEnd_3628222 : Nat := 621007269072402932813039

theorem tailTrace_3628222 : CollatzResearch.WordTrace tailWord_3628222 prefixEnd_3628222 621007269072402932813039 := by
  unfold tailWord_3628222
  simp only [CollatzResearch.WordTrace]
  refine ⟨16541515982697352478721865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88221418574385879886516613 16541515982697352478721865)
  ·
    refine ⟨12406136987023014359041399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16541515982697352478721865 12406136987023014359041399)
    ·
      refine ⟨18609205480534521538562099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12406136987023014359041399 18609205480534521538562099)
      ·
        refine ⟨27913808220801782307843149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18609205480534521538562099 27913808220801782307843149)
        ·
          refine ⟨10467678082800668365441181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27913808220801782307843149 10467678082800668365441181)
          ·
            refine ⟨3925379281050250637040443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10467678082800668365441181 3925379281050250637040443)
            ·
              refine ⟨5888068921575375955560665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925379281050250637040443 5888068921575375955560665)
              ·
                refine ⟨4416051691181531966670499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5888068921575375955560665 4416051691181531966670499)
                ·
                  refine ⟨6624077536772297950005749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416051691181531966670499 6624077536772297950005749)
                  ·
                    refine ⟨621007269072402932813039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6624077536772297950005749 621007269072402932813039)
                    ·
                      rfl

theorem cell23_3628222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_3628222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628222 prefixEnd_3628222 := by exact prefixLift 3628222
  have htrace : WordTrace (prefixWord ++ tailWord_3628222) baseStart_3628222 baseEnd_3628222 := by
    simpa [prefixWord, tailWord_3628222, baseEnd_3628222] using wordTrace_append hprefix tailTrace_3628222
  have hstable : (prefixWord ++ tailWord_3628222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628222).length < 2 ^ (prefixWord ++ tailWord_3628222).sum := by decide
  have hdescent : baseEnd_3628222 < baseStart_3628222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628242 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_3628242 : Nat := 118140960795 + 3628242 * 2 ^ 59
def prefixEnd_3628242 : Nat := 4983230072969 + 3 ^ 40 * 3628242 * 2
def baseEnd_3628242 : Nat := 1863032076830298720189025

theorem tailTrace_3628242 : CollatzResearch.WordTrace tailWord_3628242 prefixEnd_3628242 1863032076830298720189025 := by
  unfold tailWord_3628242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33083214330376590811375745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88221904881004242163668653 33083214330376590811375745)
  ·
    refine ⟨24812410747782443108531809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33083214330376590811375745 24812410747782443108531809)
    ·
      refine ⟨18609308060836832331398857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24812410747782443108531809 18609308060836832331398857)
      ·
        refine ⟨13956981045627624248549143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18609308060836832331398857 13956981045627624248549143)
        ·
          refine ⟨20935471568441436372823715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13956981045627624248549143 20935471568441436372823715)
          ·
            refine ⟨31403207352662154559235573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20935471568441436372823715 31403207352662154559235573)
            ·
              refine ⟨2944050689312076989928335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31403207352662154559235573 2944050689312076989928335)
              ·
                refine ⟨4416076033968115484892503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944050689312076989928335 4416076033968115484892503)
                ·
                  refine ⟨6624114050952173227338755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416076033968115484892503 6624114050952173227338755)
                  ·
                    refine ⟨9936171076428259841008133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6624114050952173227338755 9936171076428259841008133)
                    ·
                      refine ⟨1863032076830298720189025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9936171076428259841008133 1863032076830298720189025)
                      ·
                        rfl

theorem cell23_3628242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_3628242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628242 prefixEnd_3628242 := by exact prefixLift 3628242
  have htrace : WordTrace (prefixWord ++ tailWord_3628242) baseStart_3628242 baseEnd_3628242 := by
    simpa [prefixWord, tailWord_3628242, baseEnd_3628242] using wordTrace_append hprefix tailTrace_3628242
  have hstable : (prefixWord ++ tailWord_3628242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628242).length < 2 ^ (prefixWord ++ tailWord_3628242).sum := by decide
  have hdescent : baseEnd_3628242 < baseStart_3628242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628245 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3628245 : Nat := 118140960795 + 3628245 * 2 ^ 59
def prefixEnd_3628245 : Nat := 4983230072969 + 3 ^ 40 * 3628245 * 2
def baseEnd_3628245 : Nat := 1863033617272262208451511

theorem tailTrace_3628245 : CollatzResearch.WordTrace tailWord_3628245 prefixEnd_3628245 1863033617272262208451511 := by
  unfold tailWord_3628245
  simp only [CollatzResearch.WordTrace]
  refine ⟨132332966740495494757862189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88221977826996996505241459 132332966740495494757862189)
  ·
    refine ⟨49624862527685810534198321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132332966740495494757862189 49624862527685810534198321)
    ·
      refine ⟨37218646895764357900648741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49624862527685810534198321 37218646895764357900648741)
      ·
        refine ⟨6978496292955817106371639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37218646895764357900648741 6978496292955817106371639)
        ·
          refine ⟨10467744439433725659557459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6978496292955817106371639 10467744439433725659557459)
          ·
            refine ⟨15701616659150588489336189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10467744439433725659557459 15701616659150588489336189)
            ·
              refine ⟨5888106247181470683501071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15701616659150588489336189 5888106247181470683501071)
              ·
                refine ⟨8832159370772206025251607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888106247181470683501071 8832159370772206025251607)
                ·
                  refine ⟨13248239056158309037877411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832159370772206025251607 13248239056158309037877411)
                  ·
                    refine ⟨19872358584237463556816117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13248239056158309037877411 19872358584237463556816117)
                    ·
                      refine ⟨1863033617272262208451511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19872358584237463556816117 1863033617272262208451511)
                      ·
                        rfl

theorem cell23_3628245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3628245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628245 prefixEnd_3628245 := by exact prefixLift 3628245
  have htrace : WordTrace (prefixWord ++ tailWord_3628245) baseStart_3628245 baseEnd_3628245 := by
    simpa [prefixWord, tailWord_3628245, baseEnd_3628245] using wordTrace_append hprefix tailTrace_3628245
  have hstable : (prefixWord ++ tailWord_3628245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628245).length < 2 ^ (prefixWord ++ tailWord_3628245).sum := by decide
  have hdescent : baseEnd_3628245 < baseStart_3628245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628248 : List Nat := [2, 1, 2, 2, 6, 10]
def baseStart_3628248 : Nat := 118140960795 + 3628248 * 2 ^ 59
def prefixEnd_3628248 : Nat := 4983230072969 + 3 ^ 40 * 3628248 * 2
def baseEnd_3628248 : Nat := 7666811348618212743679

theorem tailTrace_3628248 : CollatzResearch.WordTrace tailWord_3628248 prefixEnd_3628248 7666811348618212743679 := by
  unfold tailWord_3628248
  simp only [CollatzResearch.WordTrace]
  refine ⟨66166538079742313135110699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88222050772989750846814265 66166538079742313135110699)
  ·
    refine ⟨99249807119613469702666049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66166538079742313135110699 99249807119613469702666049)
    ·
      refine ⟨74437355339710102276999537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99249807119613469702666049 74437355339710102276999537)
      ·
        refine ⟨55828016504782576707749653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74437355339710102276999537 55828016504782576707749653)
        ·
          refine ⟨2616938273661683283175765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55828016504782576707749653 2616938273661683283175765)
          ·
            refine ⟨7666811348618212743679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2616938273661683283175765 7666811348618212743679)
            ·
              rfl

theorem cell23_3628248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 10].length) (baseStart_3628248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628248 prefixEnd_3628248 := by exact prefixLift 3628248
  have htrace : WordTrace (prefixWord ++ tailWord_3628248) baseStart_3628248 baseEnd_3628248 := by
    simpa [prefixWord, tailWord_3628248, baseEnd_3628248] using wordTrace_append hprefix tailTrace_3628248
  have hstable : (prefixWord ++ tailWord_3628248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628248).length < 2 ^ (prefixWord ++ tailWord_3628248).sum := by decide
  have hdescent : baseEnd_3628248 < baseStart_3628248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628253 : List Nat := [1, 4, 3, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_3628253 : Nat := 118140960795 + 3628253 * 2 ^ 59
def prefixEnd_3628253 : Nat := 4983230072969 + 3 ^ 40 * 3628253 * 2
def baseEnd_3628253 : Nat := 1863037725117498177151475

theorem tailTrace_3628253 : CollatzResearch.WordTrace tailWord_3628253 prefixEnd_3628253 1863037725117498177151475 := by
  unfold tailWord_3628253
  simp only [CollatzResearch.WordTrace]
  refine ⟨132333258524466512124153413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88222172349644341416102275 132333258524466512124153413)
  ·
    refine ⟨24812485973337471023278765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132333258524466512124153413 24812485973337471023278765)
    ·
      refine ⟨9304682240001551633729537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24812485973337471023278765 9304682240001551633729537)
      ·
        refine ⟨6978511680001163725297153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9304682240001551633729537 6978511680001163725297153)
        ·
          refine ⟨5233883760000872793972865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978511680001163725297153 5233883760000872793972865)
          ·
            refine ⟨3925412820000654595479649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5233883760000872793972865 3925412820000654595479649)
            ·
              refine ⟨2944059615000490946609737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925412820000654595479649 2944059615000490946609737)
              ·
                refine ⟨2208044711250368209957303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944059615000490946609737 2208044711250368209957303)
                ·
                  refine ⟨3312067066875552314935955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208044711250368209957303 3312067066875552314935955)
                  ·
                    refine ⟨4968100600313328472403933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3312067066875552314935955 4968100600313328472403933)
                    ·
                      refine ⟨1863037725117498177151475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968100600313328472403933 1863037725117498177151475)
                      ·
                        rfl

theorem cell23_3628253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_3628253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628253 prefixEnd_3628253 := by exact prefixLift 3628253
  have htrace : WordTrace (prefixWord ++ tailWord_3628253) baseStart_3628253 baseEnd_3628253 := by
    simpa [prefixWord, tailWord_3628253, baseEnd_3628253] using wordTrace_append hprefix tailTrace_3628253
  have hstable : (prefixWord ++ tailWord_3628253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628253).length < 2 ^ (prefixWord ++ tailWord_3628253).sum := by decide
  have hdescent : baseEnd_3628253 < baseStart_3628253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628275 : List Nat := [1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 3]
def baseStart_3628275 : Nat := 118140960795 + 3628275 * 2 ^ 59
def prefixEnd_3628275 : Nat := 4983230072969 + 3 ^ 40 * 3628275 * 2
def baseEnd_3628275 : Nat := 1863049021691897091076373

theorem tailTrace_3628275 : CollatzResearch.WordTrace tailWord_3628275 prefixEnd_3628275 1863049021691897091076373 := by
  unfold tailWord_3628275
  simp only [CollatzResearch.WordTrace]
  refine ⟨132334060930386809881454279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88222707286924539920969519 132334060930386809881454279)
  ·
    refine ⟨198501091395580214822181419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132334060930386809881454279 198501091395580214822181419)
    ·
      refine ⟨297751637093370322233272129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198501091395580214822181419 297751637093370322233272129)
      ·
        refine ⟨223313727820027741674954097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297751637093370322233272129 223313727820027741674954097)
        ·
          refine ⟨167485295865020806256215573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223313727820027741674954097 167485295865020806256215573)
          ·
            refine ⟨7850873243672850293260105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167485295865020806256215573 7850873243672850293260105)
            ·
              refine ⟨5888154932754637719945079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7850873243672850293260105 5888154932754637719945079)
              ·
                refine ⟨8832232399131956579917619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888154932754637719945079 8832232399131956579917619)
                ·
                  refine ⟨13248348598697934869876429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832232399131956579917619 13248348598697934869876429)
                  ·
                    refine ⟨4968130724511725576203661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13248348598697934869876429 4968130724511725576203661)
                    ·
                      refine ⟨1863049021691897091076373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968130724511725576203661 1863049021691897091076373)
                      ·
                        rfl

theorem cell23_3628275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_3628275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628275 prefixEnd_3628275 := by exact prefixLift 3628275
  have htrace : WordTrace (prefixWord ++ tailWord_3628275) baseStart_3628275 baseEnd_3628275 := by
    simpa [prefixWord, tailWord_3628275, baseEnd_3628275] using wordTrace_append hprefix tailTrace_3628275
  have hstable : (prefixWord ++ tailWord_3628275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628275).length < 2 ^ (prefixWord ++ tailWord_3628275).sum := by decide
  have hdescent : baseEnd_3628275 < baseStart_3628275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628278 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 4, 7]
def baseStart_3628278 : Nat := 118140960795 + 3628278 * 2 ^ 59
def prefixEnd_3628278 : Nat := 4983230072969 + 3 ^ 40 * 3628278 * 2
def baseEnd_3628278 : Nat := 621016854044620193112953

theorem tailTrace_3628278 : CollatzResearch.WordTrace tailWord_3628278 prefixEnd_3628278 621016854044620193112953 := by
  unfold tailWord_3628278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8270885646835996337113343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88222780232917294262542325 8270885646835996337113343)
  ·
    refine ⟨12406328470253994505670015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8270885646835996337113343 12406328470253994505670015)
    ·
      refine ⟨18609492705380991758505023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12406328470253994505670015 18609492705380991758505023)
      ·
        refine ⟨27914239058071487637757535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18609492705380991758505023 27914239058071487637757535)
        ·
          refine ⟨41871358587107231456636303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27914239058071487637757535 41871358587107231456636303)
          ·
            refine ⟨62807037880660847184954455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41871358587107231456636303 62807037880660847184954455)
            ·
              refine ⟨94210556820991270777431683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62807037880660847184954455 94210556820991270777431683)
              ·
                refine ⟨141315835231486906166147525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94210556820991270777431683 141315835231486906166147525)
                ·
                  refine ⟨26496719105903794906152661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141315835231486906166147525 26496719105903794906152661)
                  ·
                    refine ⟨621016854044620193112953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26496719105903794906152661 621016854044620193112953)
                    ·
                      rfl

theorem cell23_3628278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_3628278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628278 prefixEnd_3628278 := by exact prefixLift 3628278
  have htrace : WordTrace (prefixWord ++ tailWord_3628278) baseStart_3628278 baseEnd_3628278 := by
    simpa [prefixWord, tailWord_3628278, baseEnd_3628278] using wordTrace_append hprefix tailTrace_3628278
  have hstable : (prefixWord ++ tailWord_3628278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628278).length < 2 ^ (prefixWord ++ tailWord_3628278).sum := by decide
  have hdescent : baseEnd_3628278 < baseStart_3628278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628296 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 1, 2, 3]
def baseStart_3628296 : Nat := 118140960795 + 3628296 * 2 ^ 59
def prefixEnd_3628296 : Nat := 4983230072969 + 3 ^ 40 * 3628296 * 2
def baseEnd_3628296 : Nat := 1863059804785641508913777

theorem tailTrace_3628296 : CollatzResearch.WordTrace tailWord_3628296 prefixEnd_3628296 1863059804785641508913777 := by
  unfold tailWord_3628296
  simp only [CollatzResearch.WordTrace]
  refine ⟨66167413431655365233984371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88223217908873820311979161 66167413431655365233984371)
  ·
    refine ⟨99251120147483047850976557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66167413431655365233984371 99251120147483047850976557)
    ·
      refine ⟨37219170055306142944116209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99251120147483047850976557 37219170055306142944116209)
      ·
        refine ⟨27914377541479607208087157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37219170055306142944116209 27914377541479607208087157)
        ·
          refine ⟨2616972894513713175758171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27914377541479607208087157 2616972894513713175758171)
          ·
            refine ⟨3925459341770569763637257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616972894513713175758171 3925459341770569763637257)
            ·
              refine ⟨2944094506327927322727943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3925459341770569763637257 2944094506327927322727943)
              ·
                refine ⟨4416141759491890984091915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944094506327927322727943 4416141759491890984091915)
                ·
                  refine ⟨6624212639237836476137873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416141759491890984091915 6624212639237836476137873)
                  ·
                    refine ⟨4968159479428377357103405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6624212639237836476137873 4968159479428377357103405)
                    ·
                      refine ⟨1863059804785641508913777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968159479428377357103405 1863059804785641508913777)
                      ·
                        rfl

theorem cell23_3628296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_3628296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628296 prefixEnd_3628296 := by exact prefixLift 3628296
  have htrace : WordTrace (prefixWord ++ tailWord_3628296) baseStart_3628296 baseEnd_3628296 := by
    simpa [prefixWord, tailWord_3628296, baseEnd_3628296] using wordTrace_append hprefix tailTrace_3628296
  have hstable : (prefixWord ++ tailWord_3628296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628296).length < 2 ^ (prefixWord ++ tailWord_3628296).sum := by decide
  have hdescent : baseEnd_3628296 < baseStart_3628296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628378 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3628378 : Nat := 118140960795 + 3628378 * 2 ^ 59
def prefixEnd_3628378 : Nat := 4983230072969 + 3 ^ 40 * 3628378 * 2
def baseEnd_3628378 : Nat := 1863101910199310188088399

theorem tailTrace_3628378 : CollatzResearch.WordTrace tailWord_3628378 prefixEnd_3628378 1863101910199310188088399 := by
  unfold tailWord_3628378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33084454412253414618113447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88225211766009105648302525 33084454412253414618113447)
  ·
    refine ⟨49626681618380121927170171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33084454412253414618113447 49626681618380121927170171)
    ·
      refine ⟨74440022427570182890755257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49626681618380121927170171 74440022427570182890755257)
      ·
        refine ⟨55830016820677637168066443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74440022427570182890755257 55830016820677637168066443)
        ·
          refine ⟨83745025231016455752099665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55830016820677637168066443 83745025231016455752099665)
          ·
            refine ⟨62808768923262341814074749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83745025231016455752099665 62808768923262341814074749)
            ·
              refine ⟨23553288346223378180278031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62808768923262341814074749 23553288346223378180278031)
              ·
                refine ⟨35329932519335067270417047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23553288346223378180278031 35329932519335067270417047)
                ·
                  refine ⟨52994898779002600905625571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35329932519335067270417047 52994898779002600905625571)
                  ·
                    refine ⟨79492348168503901358438357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52994898779002600905625571 79492348168503901358438357)
                    ·
                      refine ⟨1863101910199310188088399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79492348168503901358438357 1863101910199310188088399)
                      ·
                        rfl

theorem cell23_3628378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3628378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628378 prefixEnd_3628378 := by exact prefixLift 3628378
  have htrace : WordTrace (prefixWord ++ tailWord_3628378) baseStart_3628378 baseEnd_3628378 := by
    simpa [prefixWord, tailWord_3628378, baseEnd_3628378] using wordTrace_append hprefix tailTrace_3628378
  have hstable : (prefixWord ++ tailWord_3628378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628378).length < 2 ^ (prefixWord ++ tailWord_3628378).sum := by decide
  have hdescent : baseEnd_3628378 < baseStart_3628378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628456 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3628456 : Nat := 118140960795 + 3628456 * 2 ^ 59
def prefixEnd_3628456 : Nat := 4983230072969 + 3 ^ 40 * 3628456 * 2
def baseEnd_3628456 : Nat := 1863141961690360882913041

theorem tailTrace_3628456 : CollatzResearch.WordTrace tailWord_3628456 prefixEnd_3628456 1863141961690360882913041 := by
  unfold tailWord_3628456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66170331271365538896896611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88227108361820718529195481 66170331271365538896896611)
  ·
    refine ⟨99255496907048308345344917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66170331271365538896896611 99255496907048308345344917)
    ·
      refine ⟨4652601417517889453688043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99255496907048308345344917 4652601417517889453688043)
      ·
        refine ⟨6978902126276834180532065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4652601417517889453688043 6978902126276834180532065)
        ·
          refine ⟨5234176594707625635399049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978902126276834180532065 5234176594707625635399049)
          ·
            refine ⟨3925632446030719226549287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5234176594707625635399049 3925632446030719226549287)
            ·
              refine ⟨5888448669046078839823931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3925632446030719226549287 5888448669046078839823931)
              ·
                refine ⟨8832673003569118259735897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5888448669046078839823931 8832673003569118259735897)
                ·
                  refine ⟨6624504752676838694801923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8832673003569118259735897 6624504752676838694801923)
                  ·
                    refine ⟨9936757129015258042202885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6624504752676838694801923 9936757129015258042202885)
                    ·
                      refine ⟨1863141961690360882913041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9936757129015258042202885 1863141961690360882913041)
                      ·
                        rfl

theorem cell23_3628456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3628456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628456 prefixEnd_3628456 := by exact prefixLift 3628456
  have htrace : WordTrace (prefixWord ++ tailWord_3628456) baseStart_3628456 baseEnd_3628456 := by
    simpa [prefixWord, tailWord_3628456, baseEnd_3628456] using wordTrace_append hprefix tailTrace_3628456
  have hstable : (prefixWord ++ tailWord_3628456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628456).length < 2 ^ (prefixWord ++ tailWord_3628456).sum := by decide
  have hdescent : baseEnd_3628456 < baseStart_3628456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628495 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_3628495 : Nat := 118140960795 + 3628495 * 2 ^ 59
def prefixEnd_3628495 : Nat := 4983230072969 + 3 ^ 40 * 3628495 * 2
def baseEnd_3628495 : Nat := 1863161987435886230325361

theorem tailTrace_3628495 : CollatzResearch.WordTrace tailWord_3628495 prefixEnd_3628495 1863161987435886230325361 := by
  unfold tailWord_3628495
  simp only [CollatzResearch.WordTrace]
  refine ⟨132342084989589787454462939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88228056659726524969641959 132342084989589787454462939)
  ·
    refine ⟨198513127484384681181694409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132342084989589787454462939 198513127484384681181694409)
    ·
      refine ⟨148884845613288510886270807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198513127484384681181694409 148884845613288510886270807)
      ·
        refine ⟨223327268419932766329406211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148884845613288510886270807 223327268419932766329406211)
        ·
          refine ⟨334990902629899149494109317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223327268419932766329406211 334990902629899149494109317)
          ·
            refine ⟨62810794243106090530145497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334990902629899149494109317 62810794243106090530145497)
            ·
              refine ⟨47108095682329567897609123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62810794243106090530145497 47108095682329567897609123)
              ·
                refine ⟨70662143523494351846413685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47108095682329567897609123 70662143523494351846413685)
                ·
                  refine ⟨6624575955327595485601283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70662143523494351846413685 6624575955327595485601283)
                  ·
                    refine ⟨9936863932991393228401925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6624575955327595485601283 9936863932991393228401925)
                    ·
                      refine ⟨1863161987435886230325361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9936863932991393228401925 1863161987435886230325361)
                      ·
                        rfl

theorem cell23_3628495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_3628495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628495 prefixEnd_3628495 := by exact prefixLift 3628495
  have htrace : WordTrace (prefixWord ++ tailWord_3628495) baseStart_3628495 baseEnd_3628495 := by
    simpa [prefixWord, tailWord_3628495, baseEnd_3628495] using wordTrace_append hprefix tailTrace_3628495
  have hstable : (prefixWord ++ tailWord_3628495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628495).length < 2 ^ (prefixWord ++ tailWord_3628495).sum := by decide
  have hdescent : baseEnd_3628495 < baseStart_3628495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628509 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3628509 : Nat := 118140960795 + 3628509 * 2 ^ 59
def prefixEnd_3628509 : Nat := 4983230072969 + 3 ^ 40 * 3628509 * 2
def baseEnd_3628509 : Nat := 621056392055016391850099

theorem tailTrace_3628509 : CollatzResearch.WordTrace tailWord_3628509 prefixEnd_3628509 621056392055016391850099 := by
  unfold tailWord_3628509
  simp only [CollatzResearch.WordTrace]
  refine ⟨132342595611539067845472581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88228397074359378563648387 132342595611539067845472581)
  ·
    refine ⟨24814236677163575221026109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132342595611539067845472581 24814236677163575221026109)
    ·
      refine ⟨9305338753936340707884791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24814236677163575221026109 9305338753936340707884791)
      ·
        refine ⟨13958008130904511061827187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9305338753936340707884791 13958008130904511061827187)
        ·
          refine ⟨20937012196356766592740781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13958008130904511061827187 20937012196356766592740781)
          ·
            refine ⟨7851379573633787472277793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20937012196356766592740781 7851379573633787472277793)
            ·
              refine ⟨5888534680225340604208345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7851379573633787472277793 5888534680225340604208345)
              ·
                refine ⟨4416401010169005453156259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5888534680225340604208345 4416401010169005453156259)
                ·
                  refine ⟨6624601515253508179734389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4416401010169005453156259 6624601515253508179734389)
                  ·
                    refine ⟨621056392055016391850099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6624601515253508179734389 621056392055016391850099)
                    ·
                      rfl

theorem cell23_3628509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3628509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628509 prefixEnd_3628509 := by exact prefixLift 3628509
  have htrace : WordTrace (prefixWord ++ tailWord_3628509) baseStart_3628509 baseEnd_3628509 := by
    simpa [prefixWord, tailWord_3628509, baseEnd_3628509] using wordTrace_append hprefix tailTrace_3628509
  have hstable : (prefixWord ++ tailWord_3628509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628509).length < 2 ^ (prefixWord ++ tailWord_3628509).sum := by decide
  have hdescent : baseEnd_3628509 < baseStart_3628509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628575 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3628575 : Nat := 118140960795 + 3628575 * 2 ^ 59
def prefixEnd_3628575 : Nat := 4983230072969 + 3 ^ 40 * 3628575 * 2
def baseEnd_3628575 : Nat := 1863203065888245917324993

theorem tailTrace_3628575 : CollatzResearch.WordTrace tailWord_3628575 prefixEnd_3628575 1863203065888245917324993 := by
  unfold tailWord_3628575
  simp only [CollatzResearch.WordTrace]
  refine ⟨132345002829299961117375179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88230001886199974078250119 132345002829299961117375179)
  ·
    refine ⟨198517504243949941676062769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132345002829299961117375179 198517504243949941676062769)
    ·
      refine ⟨148888128182962456257047077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198517504243949941676062769 148888128182962456257047077)
      ·
        refine ⟨27916524034305460548196327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148888128182962456257047077 27916524034305460548196327)
        ·
          refine ⟨41874786051458190822294491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27916524034305460548196327 41874786051458190822294491)
          ·
            refine ⟨62812179077187286233441737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41874786051458190822294491 62812179077187286233441737)
            ·
              refine ⟨47109134307890464675081303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62812179077187286233441737 47109134307890464675081303)
              ·
                refine ⟨70663701461835697012621955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47109134307890464675081303 70663701461835697012621955)
                ·
                  refine ⟨105995552192753545518932933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70663701461835697012621955 105995552192753545518932933)
                  ·
                    refine ⟨19874166036141289784799925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105995552192753545518932933 19874166036141289784799925)
                    ·
                      refine ⟨1863203065888245917324993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19874166036141289784799925 1863203065888245917324993)
                      ·
                        rfl

theorem cell23_3628575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3628575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628575 prefixEnd_3628575 := by exact prefixLift 3628575
  have htrace : WordTrace (prefixWord ++ tailWord_3628575) baseStart_3628575 baseEnd_3628575 := by
    simpa [prefixWord, tailWord_3628575, baseEnd_3628575] using wordTrace_append hprefix tailTrace_3628575
  have hstable : (prefixWord ++ tailWord_3628575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628575).length < 2 ^ (prefixWord ++ tailWord_3628575).sum := by decide
  have hdescent : baseEnd_3628575 < baseStart_3628575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628579 : List Nat := [1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 3]
def baseStart_3628579 : Nat := 118140960795 + 3628579 * 2 ^ 59
def prefixEnd_3628579 : Nat := 4983230072969 + 3 ^ 40 * 3628579 * 2
def baseEnd_3628579 : Nat := 1863205119810863901674975

theorem tailTrace_3628579 : CollatzResearch.WordTrace tailWord_3628579 prefixEnd_3628579 1863205119810863901674975 := by
  unfold tailWord_3628579
  simp only [CollatzResearch.WordTrace]
  refine ⟨132345148721285469800520791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88230099147523646533680527 132345148721285469800520791)
  ·
    refine ⟨198517723081928204700781187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132345148721285469800520791 198517723081928204700781187)
    ·
      refine ⟨297776584622892307051171781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198517723081928204700781187 297776584622892307051171781)
      ·
        refine ⟨55833109616792307572094709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297776584622892307051171781 55833109616792307572094709)
        ·
          refine ⟨5234354026574278834883879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55833109616792307572094709 5234354026574278834883879)
          ·
            refine ⟨7851531039861418252325819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234354026574278834883879 7851531039861418252325819)
            ·
              refine ⟨11777296559792127378488729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851531039861418252325819 11777296559792127378488729)
              ·
                refine ⟨8832972419844095533866547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11777296559792127378488729 8832972419844095533866547)
                ·
                  refine ⟨13249458629766143300799821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8832972419844095533866547 13249458629766143300799821)
                  ·
                    refine ⟨4968546986162303737799933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13249458629766143300799821 4968546986162303737799933)
                    ·
                      refine ⟨1863205119810863901674975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968546986162303737799933 1863205119810863901674975)
                      ·
                        rfl

theorem cell23_3628579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_3628579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628579 prefixEnd_3628579 := by exact prefixLift 3628579
  have htrace : WordTrace (prefixWord ++ tailWord_3628579) baseStart_3628579 baseEnd_3628579 := by
    simpa [prefixWord, tailWord_3628579, baseEnd_3628579] using wordTrace_append hprefix tailTrace_3628579
  have hstable : (prefixWord ++ tailWord_3628579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628579).length < 2 ^ (prefixWord ++ tailWord_3628579).sum := by decide
  have hdescent : baseEnd_3628579 < baseStart_3628579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628619 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 6, 2, 2]
def baseStart_3628619 : Nat := 118140960795 + 3628619 * 2 ^ 59
def prefixEnd_3628619 : Nat := 4983230072969 + 3 ^ 40 * 3628619 * 2
def baseEnd_3628619 : Nat := 1863225659037043745174791

theorem tailTrace_3628619 : CollatzResearch.WordTrace tailWord_3628619 prefixEnd_3628619 1863225659037043745174791 := by
  unfold tailWord_3628619
  simp only [CollatzResearch.WordTrace]
  refine ⟨132346607641140556631976911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88231071760760371087984607 132346607641140556631976911)
  ·
    refine ⟨198519911461710834947965367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132346607641140556631976911 198519911461710834947965367)
    ·
      refine ⟨297779867192566252421948051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198519911461710834947965367 297779867192566252421948051)
      ·
        refine ⟨446669800788849378632922077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297779867192566252421948051 446669800788849378632922077)
        ·
          refine ⟨167501175295818516987345779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446669800788849378632922077 167501175295818516987345779)
          ·
            refine ⟨251251762943727775481018669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167501175295818516987345779 251251762943727775481018669)
            ·
              refine ⟨94219411103897915805382001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251251762943727775481018669 94219411103897915805382001)
              ·
                refine ⟨70664558327923436854036501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94219411103897915805382001 70664558327923436854036501)
                ·
                  refine ⟨3312401171621411102532961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70664558327923436854036501 3312401171621411102532961)
                  ·
                    refine ⟨2484300878716058326899721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3312401171621411102532961 2484300878716058326899721)
                    ·
                      refine ⟨1863225659037043745174791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484300878716058326899721 1863225659037043745174791)
                      ·
                        rfl

theorem cell23_3628619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 2, 2].length) (baseStart_3628619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628619 prefixEnd_3628619 := by exact prefixLift 3628619
  have htrace : WordTrace (prefixWord ++ tailWord_3628619) baseStart_3628619 baseEnd_3628619 := by
    simpa [prefixWord, tailWord_3628619, baseEnd_3628619] using wordTrace_append hprefix tailTrace_3628619
  have hstable : (prefixWord ++ tailWord_3628619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628619).length < 2 ^ (prefixWord ++ tailWord_3628619).sum := by decide
  have hdescent : baseEnd_3628619 < baseStart_3628619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628622 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3628622 : Nat := 118140960795 + 3628622 * 2 ^ 59
def prefixEnd_3628622 : Nat := 4983230072969 + 3 ^ 40 * 3628622 * 2
def baseEnd_3628622 : Nat := 1863227199479007233437277

theorem tailTrace_3628622 : CollatzResearch.WordTrace tailWord_3628622 prefixEnd_3628622 1863227199479007233437277 := by
  unfold tailWord_3628622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16543339632516211018042015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88231144706753125429557413 16543339632516211018042015)
  ·
    refine ⟨24815009448774316527063023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16543339632516211018042015 24815009448774316527063023)
    ·
      refine ⟨37222514173161474790594535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24815009448774316527063023 37222514173161474790594535)
      ·
        refine ⟨55833771259742212185891803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37222514173161474790594535 55833771259742212185891803)
        ·
          refine ⟨83750656889613318278837705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55833771259742212185891803 83750656889613318278837705)
          ·
            refine ⟨62812992667209988709128279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83750656889613318278837705 62812992667209988709128279)
            ·
              refine ⟨94219489000814983063692419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62812992667209988709128279 94219489000814983063692419)
              ·
                refine ⟨141329233501222474595538629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94219489000814983063692419 141329233501222474595538629)
                ·
                  refine ⟨26499231281479213986663493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141329233501222474595538629 26499231281479213986663493)
                  ·
                    refine ⟨4968605865277352622499405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26499231281479213986663493 4968605865277352622499405)
                    ·
                      refine ⟨1863227199479007233437277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968605865277352622499405 1863227199479007233437277)
                      ·
                        rfl

theorem cell23_3628622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3628622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628622 prefixEnd_3628622 := by exact prefixLift 3628622
  have htrace : WordTrace (prefixWord ++ tailWord_3628622) baseStart_3628622 baseEnd_3628622 := by
    simpa [prefixWord, tailWord_3628622, baseEnd_3628622] using wordTrace_append hprefix tailTrace_3628622
  have hstable : (prefixWord ++ tailWord_3628622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628622).length < 2 ^ (prefixWord ++ tailWord_3628622).sum := by decide
  have hdescent : baseEnd_3628622 < baseStart_3628622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628636 : List Nat := [2, 2, 4, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_3628636 : Nat := 118140960795 + 3628636 * 2 ^ 59
def prefixEnd_3628636 : Nat := 4983230072969 + 3 ^ 40 * 3628636 * 2
def baseEnd_3628636 : Nat := 1863234388208170178662213

theorem tailTrace_3628636 : CollatzResearch.WordTrace tailWord_3628636 prefixEnd_3628636 1863234388208170178662213 := by
  unfold tailWord_3628636
  simp only [CollatzResearch.WordTrace]
  refine ⟨66173613841039484267672881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88231485121385979023563841 66173613841039484267672881)
  ·
    refine ⟨49630210380779613200754661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66173613841039484267672881 49630210380779613200754661)
    ·
      refine ⟨9305664446396177475141499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49630210380779613200754661 9305664446396177475141499)
      ·
        refine ⟨13958496669594266212712249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9305664446396177475141499 13958496669594266212712249)
        ·
          refine ⟨10468872502195699659534187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13958496669594266212712249 10468872502195699659534187)
          ·
            refine ⟨15703308753293549489301281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468872502195699659534187 15703308753293549489301281)
            ·
              refine ⟨11777481564970162116975961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15703308753293549489301281 11777481564970162116975961)
              ·
                refine ⟨8833111173727621587731971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11777481564970162116975961 8833111173727621587731971)
                ·
                  refine ⟨13249666760591432381597957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833111173727621587731971 13249666760591432381597957)
                  ·
                    refine ⟨2484312517610893571549617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13249666760591432381597957 2484312517610893571549617)
                    ·
                      refine ⟨1863234388208170178662213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484312517610893571549617 1863234388208170178662213)
                      ·
                        rfl

theorem cell23_3628636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_3628636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628636 prefixEnd_3628636 := by exact prefixLift 3628636
  have htrace : WordTrace (prefixWord ++ tailWord_3628636) baseStart_3628636 baseEnd_3628636 := by
    simpa [prefixWord, tailWord_3628636, baseEnd_3628636] using wordTrace_append hprefix tailTrace_3628636
  have hstable : (prefixWord ++ tailWord_3628636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628636).length < 2 ^ (prefixWord ++ tailWord_3628636).sum := by decide
  have hdescent : baseEnd_3628636 < baseStart_3628636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628653 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_3628653 : Nat := 118140960795 + 3628653 * 2 ^ 59
def prefixEnd_3628653 : Nat := 4983230072969 + 3 ^ 40 * 3628653 * 2
def baseEnd_3628653 : Nat := 1863243117379296612149635

theorem tailTrace_3628653 : CollatzResearch.WordTrace tailWord_3628653 prefixEnd_3628653 1863243117379296612149635 := by
  unfold tailWord_3628653
  simp only [CollatzResearch.WordTrace]
  refine ⟨132347847723017380438714613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88231898482011586959143075 132347847723017380438714613)
  ·
    refine ⟨12407610724032879416129495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132347847723017380438714613 12407610724032879416129495)
    ·
      refine ⟨18611416086049319124194243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12407610724032879416129495 18611416086049319124194243)
      ·
        refine ⟨27917124129073978686291365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18611416086049319124194243 27917124129073978686291365)
        ·
          refine ⟨5234460774201371003679631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27917124129073978686291365 5234460774201371003679631)
          ·
            refine ⟨7851691161302056505519447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234460774201371003679631 7851691161302056505519447)
            ·
              refine ⟨11777536741953084758279171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7851691161302056505519447 11777536741953084758279171)
              ·
                refine ⟨17666305112929627137418757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777536741953084758279171 17666305112929627137418757)
                ·
                  refine ⟨3312432208674305088266017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17666305112929627137418757 3312432208674305088266017)
                  ·
                    refine ⟨2484324156505728816199513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3312432208674305088266017 2484324156505728816199513)
                    ·
                      refine ⟨1863243117379296612149635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484324156505728816199513 1863243117379296612149635)
                      ·
                        rfl

theorem cell23_3628653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_3628653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628653 prefixEnd_3628653 := by exact prefixLift 3628653
  have htrace : WordTrace (prefixWord ++ tailWord_3628653) baseStart_3628653 baseEnd_3628653 := by
    simpa [prefixWord, tailWord_3628653, baseEnd_3628653] using wordTrace_append hprefix tailTrace_3628653
  have hstable : (prefixWord ++ tailWord_3628653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628653).length < 2 ^ (prefixWord ++ tailWord_3628653).sum := by decide
  have hdescent : baseEnd_3628653 < baseStart_3628653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628669 : List Nat := [1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 3]
def baseStart_3628669 : Nat := 118140960795 + 3628669 * 2 ^ 59
def prefixEnd_3628669 : Nat := 4983230072969 + 3 ^ 40 * 3628669 * 2
def baseEnd_3628669 : Nat := 1863251333069768549549561

theorem tailTrace_3628669 : CollatzResearch.WordTrace tailWord_3628669 prefixEnd_3628669 1863251333069768549549561 := by
  unfold tailWord_3628669
  simp only [CollatzResearch.WordTrace]
  refine ⟨132348431290959415171297061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88232287527306276780864707 132348431290959415171297061)
  ·
    refine ⟨24815330867054890344618199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132348431290959415171297061 24815330867054890344618199)
    ·
      refine ⟨37222996300582335516927299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24815330867054890344618199 37222996300582335516927299)
      ·
        refine ⟨55834494450873503275390949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37222996300582335516927299 55834494450873503275390949)
        ·
          refine ⟨10468967709538781864135803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55834494450873503275390949 10468967709538781864135803)
          ·
            refine ⟨15703451564308172796203705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468967709538781864135803 15703451564308172796203705)
            ·
              refine ⟨11777588673231129597152779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15703451564308172796203705 11777588673231129597152779)
              ·
                refine ⟨17666383009846694395729169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11777588673231129597152779 17666383009846694395729169)
                ·
                  refine ⟨13249787257385020796796877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17666383009846694395729169 13249787257385020796796877)
                  ·
                    refine ⟨4968670221519382798798829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13249787257385020796796877 4968670221519382798798829)
                    ·
                      refine ⟨1863251333069768549549561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968670221519382798798829 1863251333069768549549561)
                      ·
                        rfl

theorem cell23_3628669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_3628669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628669 prefixEnd_3628669 := by exact prefixLift 3628669
  have htrace : WordTrace (prefixWord ++ tailWord_3628669) baseStart_3628669 baseEnd_3628669 := by
    simpa [prefixWord, tailWord_3628669, baseEnd_3628669] using wordTrace_append hprefix tailTrace_3628669
  have hstable : (prefixWord ++ tailWord_3628669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628669).length < 2 ^ (prefixWord ++ tailWord_3628669).sum := by decide
  have hdescent : baseEnd_3628669 < baseStart_3628669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628709 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 4, 4, 2]
def baseStart_3628709 : Nat := 118140960795 + 3628709 * 2 ^ 59
def prefixEnd_3628709 : Nat := 4983230072969 + 3 ^ 40 * 3628709 * 2
def baseEnd_3628709 : Nat := 1863271872295948393049377

theorem tailTrace_3628709 : CollatzResearch.WordTrace tailWord_3628709 prefixEnd_3628709 1863271872295948393049377 := by
  unfold tailWord_3628709
  simp only [CollatzResearch.WordTrace]
  refine ⟨132349890210814502002753181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88233260140543001335168787 132349890210814502002753181)
  ·
    refine ⟨49631208829055438251032443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132349890210814502002753181 49631208829055438251032443)
    ·
      refine ⟨74446813243583157376548665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49631208829055438251032443 74446813243583157376548665)
      ·
        refine ⟨55835109932687368032411499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74446813243583157376548665 55835109932687368032411499)
        ·
          refine ⟨83752664899031052048617249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55835109932687368032411499 83752664899031052048617249)
          ·
            refine ⟨62814498674273289036462937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83752664899031052048617249 62814498674273289036462937)
            ·
              refine ⟨47110874005704966777347203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62814498674273289036462937 47110874005704966777347203)
              ·
                refine ⟨70666311008557450166020805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47110874005704966777347203 70666311008557450166020805)
                ·
                  refine ⟨13249933314104521906128901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70666311008557450166020805 13249933314104521906128901)
                  ·
                    refine ⟨2484362496394597857399169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13249933314104521906128901 2484362496394597857399169)
                    ·
                      refine ⟨1863271872295948393049377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484362496394597857399169 1863271872295948393049377)
                      ·
                        rfl

theorem cell23_3628709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_3628709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628709 prefixEnd_3628709 := by exact prefixLift 3628709
  have htrace : WordTrace (prefixWord ++ tailWord_3628709) baseStart_3628709 baseEnd_3628709 := by
    simpa [prefixWord, tailWord_3628709, baseEnd_3628709] using wordTrace_append hprefix tailTrace_3628709
  have hstable : (prefixWord ++ tailWord_3628709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628709).length < 2 ^ (prefixWord ++ tailWord_3628709).sum := by decide
  have hdescent : baseEnd_3628709 < baseStart_3628709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628722 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_3628722 : Nat := 118140960795 + 3628722 * 2 ^ 59
def prefixEnd_3628722 : Nat := 4983230072969 + 3 ^ 40 * 3628722 * 2
def baseEnd_3628722 : Nat := 1863278547544456842186817

theorem tailTrace_3628722 : CollatzResearch.WordTrace tailWord_3628722 prefixEnd_3628722 1863278547544456842186817 := by
  unfold tailWord_3628722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33087591089941851305744105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88233576239844936815317613 33087591089941851305744105)
  ·
    refine ⟨24815693317456388479308079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33087591089941851305744105 24815693317456388479308079)
    ·
      refine ⟨37223539976184582718962119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24815693317456388479308079 37223539976184582718962119)
      ·
        refine ⟨55835309964276874078443179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37223539976184582718962119 55835309964276874078443179)
        ·
          refine ⟨83752964946415311117664769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55835309964276874078443179 83752964946415311117664769)
          ·
            refine ⟨62814723709811483338248577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83752964946415311117664769 62814723709811483338248577)
            ·
              refine ⟨47111042782358612503686433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62814723709811483338248577 47111042782358612503686433)
              ·
                refine ⟨35333282086768959377764825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47111042782358612503686433 35333282086768959377764825)
                ·
                  refine ⟨26499961565076719533323619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35333282086768959377764825 26499961565076719533323619)
                  ·
                    refine ⟨39749942347615079299985429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26499961565076719533323619 39749942347615079299985429)
                    ·
                      refine ⟨1863278547544456842186817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39749942347615079299985429 1863278547544456842186817)
                      ·
                        rfl

theorem cell23_3628722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_3628722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628722 prefixEnd_3628722 := by exact prefixLift 3628722
  have htrace : WordTrace (prefixWord ++ tailWord_3628722) baseStart_3628722 baseEnd_3628722 := by
    simpa [prefixWord, tailWord_3628722, baseEnd_3628722] using wordTrace_append hprefix tailTrace_3628722
  have hstable : (prefixWord ++ tailWord_3628722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628722).length < 2 ^ (prefixWord ++ tailWord_3628722).sum := by decide
  have hdescent : baseEnd_3628722 < baseStart_3628722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628786 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_3628786 : Nat := 118140960795 + 3628786 * 2 ^ 59
def prefixEnd_3628786 : Nat := 4983230072969 + 3 ^ 40 * 3628786 * 2
def baseEnd_3628786 : Nat := 1863311410306344591786523

theorem tailTrace_3628786 : CollatzResearch.WordTrace tailWord_3628786 prefixEnd_3628786 1863311410306344591786523 := by
  unfold tailWord_3628786
  simp only [CollatzResearch.WordTrace]
  refine ⟨33088174657883886038326553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88235132421023696102204141 33088174657883886038326553)
  ·
    refine ⟨24816130993412914528744915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33088174657883886038326553 24816130993412914528744915)
    ·
      refine ⟨37224196490119371793117373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24816130993412914528744915 37224196490119371793117373)
      ·
        refine ⟨13959073683794764422419015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37224196490119371793117373 13959073683794764422419015)
        ·
          refine ⟨20938610525692146633628523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13959073683794764422419015 20938610525692146633628523)
          ·
            refine ⟨31407915788538219950442785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20938610525692146633628523 31407915788538219950442785)
            ·
              refine ⟨23555936841403664962832089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31407915788538219950442785 23555936841403664962832089)
              ·
                refine ⟨17666952631052748722124067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23555936841403664962832089 17666952631052748722124067)
                ·
                  refine ⟨26500428946579123083186101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17666952631052748722124067 26500428946579123083186101)
                  ·
                    refine ⟨2484415213741792789048697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26500428946579123083186101 2484415213741792789048697)
                    ·
                      refine ⟨1863311410306344591786523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484415213741792789048697 1863311410306344591786523)
                      ·
                        rfl

theorem cell23_3628786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_3628786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628786 prefixEnd_3628786 := by exact prefixLift 3628786
  have htrace : WordTrace (prefixWord ++ tailWord_3628786) baseStart_3628786 baseEnd_3628786 := by
    simpa [prefixWord, tailWord_3628786, baseEnd_3628786] using wordTrace_append hprefix tailTrace_3628786
  have hstable : (prefixWord ++ tailWord_3628786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628786).length < 2 ^ (prefixWord ++ tailWord_3628786).sum := by decide
  have hdescent : baseEnd_3628786 < baseStart_3628786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628799 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_3628799 : Nat := 118140960795 + 3628799 * 2 ^ 59
def prefixEnd_3628799 : Nat := 4983230072969 + 3 ^ 40 * 3628799 * 2
def baseEnd_3628799 : Nat := 1863318085554853040923963

theorem tailTrace_3628799 : CollatzResearch.WordTrace tailWord_3628799 prefixEnd_3628799 1863318085554853040923963 := by
  unfold tailWord_3628799
  simp only [CollatzResearch.WordTrace]
  refine ⟨132353172780488447373529451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88235448520325631582352967 132353172780488447373529451)
  ·
    refine ⟨198529759170732671060294177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132353172780488447373529451 198529759170732671060294177)
    ·
      refine ⟨148897319378049503295220633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198529759170732671060294177 148897319378049503295220633)
      ·
        refine ⟨111672989533537127471415475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148897319378049503295220633 111672989533537127471415475)
        ·
          refine ⟨167509484300305691207123213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111672989533537127471415475 167509484300305691207123213)
          ·
            refine ⟨62816056612614634202671205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167509484300305691207123213 62816056612614634202671205)
            ·
              refine ⟨11778010614865243913000851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62816056612614634202671205 11778010614865243913000851)
              ·
                refine ⟨17667015922297865869501277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11778010614865243913000851 17667015922297865869501277)
                ·
                  refine ⟨6625130970861699701062979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17667015922297865869501277 6625130970861699701062979)
                  ·
                    refine ⟨9937696456292549551594469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6625130970861699701062979 9937696456292549551594469)
                    ·
                      refine ⟨1863318085554853040923963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9937696456292549551594469 1863318085554853040923963)
                      ·
                        rfl

theorem cell23_3628799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_3628799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628799 prefixEnd_3628799 := by exact prefixLift 3628799
  have htrace : WordTrace (prefixWord ++ tailWord_3628799) baseStart_3628799 baseEnd_3628799 := by
    simpa [prefixWord, tailWord_3628799, baseEnd_3628799] using wordTrace_append hprefix tailTrace_3628799
  have hstable : (prefixWord ++ tailWord_3628799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628799).length < 2 ^ (prefixWord ++ tailWord_3628799).sum := by decide
  have hdescent : baseEnd_3628799 < baseStart_3628799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628809 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 4, 4]
def baseStart_3628809 : Nat := 118140960795 + 3628809 * 2 ^ 59
def prefixEnd_3628809 : Nat := 4983230072969 + 3 ^ 40 * 3628809 * 2
def baseEnd_3628809 : Nat := 621107740120466000599639

theorem tailTrace_3628809 : CollatzResearch.WordTrace tailWord_3628809 prefixEnd_3628809 621107740120466000599639 := by
  unfold tailWord_3628809
  simp only [CollatzResearch.WordTrace]
  refine ⟨132353537510452219081393481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88235691673634812720928987 132353537510452219081393481)
  ·
    refine ⟨99265153132839164311045111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132353537510452219081393481 99265153132839164311045111)
    ·
      refine ⟨148897729699258746466567667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99265153132839164311045111 148897729699258746466567667)
      ·
        refine ⟨223346594548888119699851501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148897729699258746466567667 223346594548888119699851501)
        ·
          refine ⟨83754972955833044887444313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223346594548888119699851501 83754972955833044887444313)
          ·
            refine ⟨62816229716874783665583235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83754972955833044887444313 62816229716874783665583235)
            ·
              refine ⟨94224344575312175498374853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62816229716874783665583235 94224344575312175498374853)
              ·
                refine ⟨17667064607871032905945285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94224344575312175498374853 17667064607871032905945285)
                ·
                  refine ⟨3312574613975818669864741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17667064607871032905945285 3312574613975818669864741)
                  ·
                    refine ⟨621107740120466000599639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312574613975818669864741 621107740120466000599639)
                    ·
                      rfl

theorem cell23_3628809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 4].length) (baseStart_3628809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628809 prefixEnd_3628809 := by exact prefixLift 3628809
  have htrace : WordTrace (prefixWord ++ tailWord_3628809) baseStart_3628809 baseEnd_3628809 := by
    simpa [prefixWord, tailWord_3628809, baseEnd_3628809] using wordTrace_append hprefix tailTrace_3628809
  have hstable : (prefixWord ++ tailWord_3628809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628809).length < 2 ^ (prefixWord ++ tailWord_3628809).sum := by decide
  have hdescent : baseEnd_3628809 < baseStart_3628809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628810 : List Nat := [3, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_3628810 : Nat := 118140960795 + 3628810 * 2 ^ 59
def prefixEnd_3628810 : Nat := 4983230072969 + 3 ^ 40 * 3628810 * 2
def baseEnd_3628810 : Nat := 1863323733842052497886413

theorem tailTrace_3628810 : CollatzResearch.WordTrace tailWord_3628810 prefixEnd_3628810 1863323733842052497886413 := by
  unfold tailWord_3628810
  simp only [CollatzResearch.WordTrace]
  refine ⟨33088393495862149063044971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88235715988965730834786589 33088393495862149063044971)
  ·
    refine ⟨49632590243793223594567457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33088393495862149063044971 49632590243793223594567457)
    ·
      refine ⟨37224442682844917695925593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49632590243793223594567457 37224442682844917695925593)
      ·
        refine ⟨27918332012133688271944195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37224442682844917695925593 27918332012133688271944195)
        ·
          refine ⟨41877498018200532407916293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27918332012133688271944195 41877498018200532407916293)
          ·
            refine ⟨7852030878412599826484305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41877498018200532407916293 7852030878412599826484305)
            ·
              refine ⟨5889023158809449869863229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852030878412599826484305 5889023158809449869863229)
              ·
                refine ⟨2208383684553543701198711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889023158809449869863229 2208383684553543701198711)
                ·
                  refine ⟨3312575526830315551798067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208383684553543701198711 3312575526830315551798067)
                  ·
                    refine ⟨4968863290245473327697101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3312575526830315551798067 4968863290245473327697101)
                    ·
                      refine ⟨1863323733842052497886413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968863290245473327697101 1863323733842052497886413)
                      ·
                        rfl

theorem cell23_3628810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_3628810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628810 prefixEnd_3628810 := by exact prefixLift 3628810
  have htrace : WordTrace (prefixWord ++ tailWord_3628810) baseStart_3628810 baseEnd_3628810 := by
    simpa [prefixWord, tailWord_3628810, baseEnd_3628810] using wordTrace_append hprefix tailTrace_3628810
  have hstable : (prefixWord ++ tailWord_3628810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628810).length < 2 ^ (prefixWord ++ tailWord_3628810).sum := by decide
  have hdescent : baseEnd_3628810 < baseStart_3628810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628819 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 3]
def baseStart_3628819 : Nat := 118140960795 + 3628819 * 2 ^ 59
def prefixEnd_3628819 : Nat := 4983230072969 + 3 ^ 40 * 3628819 * 2
def baseEnd_3628819 : Nat := 1863328355167942962673871

theorem tailTrace_3628819 : CollatzResearch.WordTrace tailWord_3628819 prefixEnd_3628819 1863328355167942962673871 := by
  unfold tailWord_3628819
  simp only [CollatzResearch.WordTrace]
  refine ⟨132353902240415990789257511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88235934826943993859505007 132353902240415990789257511)
  ·
    refine ⟨198530853360623986183886267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132353902240415990789257511 198530853360623986183886267)
    ·
      refine ⟨297796280040935979275829401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198530853360623986183886267 297796280040935979275829401)
      ·
        refine ⟨223347210030701984456872051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297796280040935979275829401 223347210030701984456872051)
        ·
          refine ⟨335020815046052976685308077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223347210030701984456872051 335020815046052976685308077)
          ·
            refine ⟨125632805642269866256990529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335020815046052976685308077 125632805642269866256990529)
            ·
              refine ⟨94224604231702399692742897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125632805642269866256990529 94224604231702399692742897)
              ·
                refine ⟨70668453173776799769557173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94224604231702399692742897 70668453173776799769557173)
                ·
                  refine ⟨6625167485041574978395985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70668453173776799769557173 6625167485041574978395985)
                  ·
                    refine ⟨4968875613781181233796989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6625167485041574978395985 4968875613781181233796989)
                    ·
                      refine ⟨1863328355167942962673871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968875613781181233796989 1863328355167942962673871)
                      ·
                        rfl

theorem cell23_3628819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_3628819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628819 prefixEnd_3628819 := by exact prefixLift 3628819
  have htrace : WordTrace (prefixWord ++ tailWord_3628819) baseStart_3628819 baseEnd_3628819 := by
    simpa [prefixWord, tailWord_3628819, baseEnd_3628819] using wordTrace_append hprefix tailTrace_3628819
  have hstable : (prefixWord ++ tailWord_3628819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628819).length < 2 ^ (prefixWord ++ tailWord_3628819).sum := by decide
  have hdescent : baseEnd_3628819 < baseStart_3628819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628826 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_3628826 : Nat := 118140960795 + 3628826 * 2 ^ 59
def prefixEnd_3628826 : Nat := 4983230072969 + 3 ^ 40 * 3628826 * 2
def baseEnd_3628826 : Nat := 621110649844174811762113

theorem tailTrace_3628826 : CollatzResearch.WordTrace tailWord_3628826 prefixEnd_3628826 621110649844174811762113 := by
  unfold tailWord_3628826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33088539387847657746190583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88236105034260420656508221 33088539387847657746190583)
  ·
    refine ⟨49632809081771486619285875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33088539387847657746190583 49632809081771486619285875)
    ·
      refine ⟨74449213622657229928928813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49632809081771486619285875 74449213622657229928928813)
      ·
        refine ⟨27918455108496461223348305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74449213622657229928928813 27918455108496461223348305)
        ·
          refine ⟨20938841331372345917511229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27918455108496461223348305 20938841331372345917511229)
          ·
            refine ⟨7852065499264629719066711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20938841331372345917511229 7852065499264629719066711)
            ·
              refine ⟨11778098248896944578600067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852065499264629719066711 11778098248896944578600067)
              ·
                refine ⟨17667147373345416867900101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11778098248896944578600067 17667147373345416867900101)
                ·
                  refine ⟨3312590132502265662731269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17667147373345416867900101 3312590132502265662731269)
                  ·
                    refine ⟨621110649844174811762113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312590132502265662731269 621110649844174811762113)
                    ·
                      rfl

theorem cell23_3628826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_3628826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628826 prefixEnd_3628826 := by exact prefixLift 3628826
  have htrace : WordTrace (prefixWord ++ tailWord_3628826) baseStart_3628826 baseEnd_3628826 := by
    simpa [prefixWord, tailWord_3628826, baseEnd_3628826] using wordTrace_append hprefix tailTrace_3628826
  have hstable : (prefixWord ++ tailWord_3628826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628826).length < 2 ^ (prefixWord ++ tailWord_3628826).sum := by decide
  have hdescent : baseEnd_3628826 < baseStart_3628826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628833 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_3628833 : Nat := 118140960795 + 3628833 * 2 ^ 59
def prefixEnd_3628833 : Nat := 4983230072969 + 3 ^ 40 * 3628833 * 2
def baseEnd_3628833 : Nat := 1863335543897105907898807

theorem tailTrace_3628833 : CollatzResearch.WordTrace tailWord_3628833 prefixEnd_3628833 1863335543897105907898807 := by
  unfold tailWord_3628833
  simp only [CollatzResearch.WordTrace]
  refine ⟨132354412862365271180267153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88236275241576847453511435 132354412862365271180267153)
  ·
    refine ⟨99265809646773953385200365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132354412862365271180267153 99265809646773953385200365)
    ·
      refine ⟨37224678617540232519450137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99265809646773953385200365 37224678617540232519450137)
      ·
        refine ⟨27918508963155174389587603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37224678617540232519450137 27918508963155174389587603)
        ·
          refine ⟨41877763444732761584381405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27918508963155174389587603 41877763444732761584381405)
          ·
            refine ⟨15704161291774785594143027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41877763444732761584381405 15704161291774785594143027)
            ·
              refine ⟨23556241937662178391214541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15704161291774785594143027 23556241937662178391214541)
              ·
                refine ⟨8833590726623316896705453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23556241937662178391214541 8833590726623316896705453)
                ·
                  refine ⟨3312596522483743836264545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8833590726623316896705453 3312596522483743836264545)
                  ·
                    refine ⟨2484447391862807877198409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3312596522483743836264545 2484447391862807877198409)
                    ·
                      refine ⟨1863335543897105907898807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484447391862807877198409 1863335543897105907898807)
                      ·
                        rfl

theorem cell23_3628833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_3628833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628833 prefixEnd_3628833 := by exact prefixLift 3628833
  have htrace : WordTrace (prefixWord ++ tailWord_3628833) baseStart_3628833 baseEnd_3628833 := by
    simpa [prefixWord, tailWord_3628833, baseEnd_3628833] using wordTrace_append hprefix tailTrace_3628833
  have hstable : (prefixWord ++ tailWord_3628833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628833).length < 2 ^ (prefixWord ++ tailWord_3628833).sum := by decide
  have hdescent : baseEnd_3628833 < baseStart_3628833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628836 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3628836 : Nat := 118140960795 + 3628836 * 2 ^ 59
def prefixEnd_3628836 : Nat := 4983230072969 + 3 ^ 40 * 3628836 * 2
def baseEnd_3628836 : Nat := 1863337084339069396161293

theorem tailTrace_3628836 : CollatzResearch.WordTrace tailWord_3628836 prefixEnd_3628836 1863337084339069396161293 := by
  unfold tailWord_3628836
  simp only [CollatzResearch.WordTrace]
  refine ⟨66177261140677201346313181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88236348187569601795084241 66177261140677201346313181)
  ·
    refine ⟨24816472927753950504867443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66177261140677201346313181 24816472927753950504867443)
    ·
      refine ⟨37224709391630925757301165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24816472927753950504867443 37224709391630925757301165)
      ·
        refine ⟨13959266021861597158987937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37224709391630925757301165 13959266021861597158987937)
        ·
          refine ⟨10469449516396197869240953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13959266021861597158987937 10469449516396197869240953)
          ·
            refine ⟨7852087137297148401930715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10469449516396197869240953 7852087137297148401930715)
            ·
              refine ⟨11778130705945722602896073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852087137297148401930715 11778130705945722602896073)
              ·
                refine ⟨8833598029459291952172055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11778130705945722602896073 8833598029459291952172055)
                ·
                  refine ⟨13250397044188937928258083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833598029459291952172055 13250397044188937928258083)
                  ·
                    refine ⟨19875595566283406892387125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13250397044188937928258083 19875595566283406892387125)
                    ·
                      refine ⟨1863337084339069396161293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19875595566283406892387125 1863337084339069396161293)
                      ·
                        rfl

theorem cell23_3628836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3628836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628836 prefixEnd_3628836 := by exact prefixLift 3628836
  have htrace : WordTrace (prefixWord ++ tailWord_3628836) baseStart_3628836 baseEnd_3628836 := by
    simpa [prefixWord, tailWord_3628836, baseEnd_3628836] using wordTrace_append hprefix tailTrace_3628836
  have hstable : (prefixWord ++ tailWord_3628836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628836).length < 2 ^ (prefixWord ++ tailWord_3628836).sum := by decide
  have hdescent : baseEnd_3628836 < baseStart_3628836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628856 : List Nat := [2, 1, 2, 1, 3, 5, 2, 7]
def baseStart_3628856 : Nat := 118140960795 + 3628856 * 2 ^ 59
def prefixEnd_3628856 : Nat := 4983230072969 + 3 ^ 40 * 3628856 * 2
def baseEnd_3628856 : Nat := 69012864961191085848563

theorem tailTrace_3628856 : CollatzResearch.WordTrace tailWord_3628856 prefixEnd_3628856 69012864961191085848563 := by
  unfold tailWord_3628856
  simp only [CollatzResearch.WordTrace]
  refine ⟨66177625870640973054177211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88236834494187964072236281 66177625870640973054177211)
  ·
    refine ⟨99266438805961459581265817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66177625870640973054177211 99266438805961459581265817)
    ·
      refine ⟨74449829104471094685949363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99266438805961459581265817 74449829104471094685949363)
      ·
        refine ⟨111674743656706642028924045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74449829104471094685949363 111674743656706642028924045)
        ·
          refine ⟨41878028871264990760846517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111674743656706642028924045 41878028871264990760846517)
          ·
            refine ⟨3926065206681092883829361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41878028871264990760846517 3926065206681092883829361)
            ·
              refine ⟨2944548905010819662872021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926065206681092883829361 2944548905010819662872021)
              ·
                refine ⟨69012864961191085848563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2944548905010819662872021 69012864961191085848563)
                ·
                  rfl

theorem cell23_3628856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 7].length) (baseStart_3628856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628856 prefixEnd_3628856 := by exact prefixLift 3628856
  have htrace : WordTrace (prefixWord ++ tailWord_3628856) baseStart_3628856 baseEnd_3628856 := by
    simpa [prefixWord, tailWord_3628856, baseEnd_3628856] using wordTrace_append hprefix tailTrace_3628856
  have hstable : (prefixWord ++ tailWord_3628856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628856).length < 2 ^ (prefixWord ++ tailWord_3628856).sum := by decide
  have hdescent : baseEnd_3628856 < baseStart_3628856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628867 : List Nat := [1, 1, 1, 3, 1, 7, 1, 3, 1, 2, 2]
def baseStart_3628867 : Nat := 118140960795 + 3628867 * 2 ^ 59
def prefixEnd_3628867 : Nat := 4983230072969 + 3 ^ 40 * 3628867 * 2
def baseEnd_3628867 : Nat := 1863353002239358774873651

theorem tailTrace_3628867 : CollatzResearch.WordTrace tailWord_3628867 prefixEnd_3628867 1863353002239358774873651 := by
  unfold tailWord_3628867
  simp only [CollatzResearch.WordTrace]
  refine ⟨132355652944242094987004855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88237101962828063324669903 132355652944242094987004855)
  ·
    refine ⟨198533479416363142480507283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132355652944242094987004855 198533479416363142480507283)
    ·
      refine ⟨297800219124544713720760925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198533479416363142480507283 297800219124544713720760925)
      ·
        refine ⟨111675082171704267645285347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297800219124544713720760925 111675082171704267645285347)
        ·
          refine ⟨167512623257556401467928021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111675082171704267645285347 167512623257556401467928021)
          ·
            refine ⟨3926077107598978159404563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 167512623257556401467928021 3926077107598978159404563)
            ·
              refine ⟨5889115661398467239106845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926077107598978159404563 5889115661398467239106845)
              ·
                refine ⟨2208418373024425214665067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889115661398467239106845 2208418373024425214665067)
                ·
                  refine ⟨3312627559536637821997601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208418373024425214665067 3312627559536637821997601)
                  ·
                    refine ⟨2484470669652478366498201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3312627559536637821997601 2484470669652478366498201)
                    ·
                      refine ⟨1863353002239358774873651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484470669652478366498201 1863353002239358774873651)
                      ·
                        rfl

theorem cell23_3628867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_3628867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628867 prefixEnd_3628867 := by exact prefixLift 3628867
  have htrace : WordTrace (prefixWord ++ tailWord_3628867) baseStart_3628867 baseEnd_3628867 := by
    simpa [prefixWord, tailWord_3628867, baseEnd_3628867] using wordTrace_append hprefix tailTrace_3628867
  have hstable : (prefixWord ++ tailWord_3628867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628867).length < 2 ^ (prefixWord ++ tailWord_3628867).sum := by decide
  have hdescent : baseEnd_3628867 < baseStart_3628867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628870 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3628870 : Nat := 118140960795 + 3628870 * 2 ^ 59
def prefixEnd_3628870 : Nat := 4983230072969 + 3 ^ 40 * 3628870 * 2
def baseEnd_3628870 : Nat := 1863354542681322263136137

theorem tailTrace_3628870 : CollatzResearch.WordTrace tailWord_3628870 prefixEnd_3628870 1863354542681322263136137 := by
  unfold tailWord_3628870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136117573850975828105127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88237174908820817666242709 4136117573850975828105127)
  ·
    refine ⟨6204176360776463742157691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4136117573850975828105127 6204176360776463742157691)
    ·
      refine ⟨9306264541164695613236537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6204176360776463742157691 9306264541164695613236537)
      ·
        refine ⟨6979698405873521709927403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9306264541164695613236537 6979698405873521709927403)
        ·
          refine ⟨10469547608810282564891105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979698405873521709927403 10469547608810282564891105)
          ·
            refine ⟨7852160706607711923668329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10469547608810282564891105 7852160706607711923668329)
            ·
              refine ⟨5889120529955783942751247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852160706607711923668329 5889120529955783942751247)
              ·
                refine ⟨8833680794933675914126871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889120529955783942751247 8833680794933675914126871)
                ·
                  refine ⟨13250521192400513871190307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8833680794933675914126871 13250521192400513871190307)
                  ·
                    refine ⟨19875781788600770806785461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13250521192400513871190307 19875781788600770806785461)
                    ·
                      refine ⟨1863354542681322263136137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19875781788600770806785461 1863354542681322263136137)
                      ·
                        rfl

theorem cell23_3628870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3628870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628870 prefixEnd_3628870 := by exact prefixLift 3628870
  have htrace : WordTrace (prefixWord ++ tailWord_3628870) baseStart_3628870 baseEnd_3628870 := by
    simpa [prefixWord, tailWord_3628870, baseEnd_3628870] using wordTrace_append hprefix tailTrace_3628870
  have hstable : (prefixWord ++ tailWord_3628870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628870).length < 2 ^ (prefixWord ++ tailWord_3628870).sum := by decide
  have hdescent : baseEnd_3628870 < baseStart_3628870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628884 : List Nat := [2, 4, 1, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_3628884 : Nat := 118140960795 + 3628884 * 2 ^ 59
def prefixEnd_3628884 : Nat := 4983230072969 + 3 ^ 40 * 3628884 * 2
def baseEnd_3628884 : Nat := 1863361731410485208361073

theorem tailTrace_3628884 : CollatzResearch.WordTrace tailWord_3628884 prefixEnd_3628884 1863361731410485208361073 := by
  unfold tailWord_3628884
  simp only [CollatzResearch.WordTrace]
  refine ⟨66178136492590253445186853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88237515323453671260249137 66178136492590253445186853)
  ·
    refine ⟨12408400592360672520972535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66178136492590253445186853 12408400592360672520972535)
    ·
      refine ⟨18612600888541008781458803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12408400592360672520972535 18612600888541008781458803)
      ·
        refine ⟨27918901332811513172188205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18612600888541008781458803 27918901332811513172188205)
        ·
          refine ⟨10469587999804317439570577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27918901332811513172188205 10469587999804317439570577)
          ·
            refine ⟨7852190999853238079677933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10469587999804317439570577 7852190999853238079677933)
            ·
              refine ⟨2944571624944964279879225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7852190999853238079677933 2944571624944964279879225)
              ·
                refine ⟨2208428718708723209909419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944571624944964279879225 2208428718708723209909419)
                ·
                  refine ⟨3312643078063084814864129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208428718708723209909419 3312643078063084814864129)
                  ·
                    refine ⟨2484482308547313611148097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3312643078063084814864129 2484482308547313611148097)
                    ·
                      refine ⟨1863361731410485208361073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484482308547313611148097 1863361731410485208361073)
                      ·
                        rfl

theorem cell23_3628884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_3628884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628884 prefixEnd_3628884 := by exact prefixLift 3628884
  have htrace : WordTrace (prefixWord ++ tailWord_3628884) baseStart_3628884 baseEnd_3628884 := by
    simpa [prefixWord, tailWord_3628884, baseEnd_3628884] using wordTrace_append hprefix tailTrace_3628884
  have hstable : (prefixWord ++ tailWord_3628884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628884).length < 2 ^ (prefixWord ++ tailWord_3628884).sum := by decide
  have hdescent : baseEnd_3628884 < baseStart_3628884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628889 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3628889 : Nat := 118140960795 + 3628889 * 2 ^ 59
def prefixEnd_3628889 : Nat := 4983230072969 + 3 ^ 40 * 3628889 * 2
def baseEnd_3628889 : Nat := 1863364298813757688798549

theorem tailTrace_3628889 : CollatzResearch.WordTrace tailWord_3628889 prefixEnd_3628889 1863364298813757688798549 := by
  unfold tailWord_3628889
  simp only [CollatzResearch.WordTrace]
  refine ⟨132356455350162392744305721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88237636900108261829537147 132356455350162392744305721)
  ·
    refine ⟨99267341512621794558229291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132356455350162392744305721 99267341512621794558229291)
    ·
      refine ⟨148901012268932691837343937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99267341512621794558229291 148901012268932691837343937)
      ·
        refine ⟨111675759201699518878007953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148901012268932691837343937 111675759201699518878007953)
        ·
          refine ⟨83756819401274639158505965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111675759201699518878007953 83756819401274639158505965)
          ·
            refine ⟨31408807275477989684439737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83756819401274639158505965 31408807275477989684439737)
            ·
              refine ⟨23556605456608492263329803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31408807275477989684439737 23556605456608492263329803)
              ·
                refine ⟨35334908184912738394994705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23556605456608492263329803 35334908184912738394994705)
                ·
                  refine ⟨26501181138684553796246029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35334908184912738394994705 26501181138684553796246029)
                  ·
                    refine ⟨9937942927006707673592261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26501181138684553796246029 9937942927006707673592261)
                    ·
                      refine ⟨1863364298813757688798549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9937942927006707673592261 1863364298813757688798549)
                      ·
                        rfl

theorem cell23_3628889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3628889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628889 prefixEnd_3628889 := by exact prefixLift 3628889
  have htrace : WordTrace (prefixWord ++ tailWord_3628889) baseStart_3628889 baseEnd_3628889 := by
    simpa [prefixWord, tailWord_3628889, baseEnd_3628889] using wordTrace_append hprefix tailTrace_3628889
  have hstable : (prefixWord ++ tailWord_3628889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628889).length < 2 ^ (prefixWord ++ tailWord_3628889).sum := by decide
  have hdescent : baseEnd_3628889 < baseStart_3628889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628900 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_3628900 : Nat := 118140960795 + 3628900 * 2 ^ 59
def prefixEnd_3628900 : Nat := 4983230072969 + 3 ^ 40 * 3628900 * 2
def baseEnd_3628900 : Nat := 1863369947100957145760999

theorem tailTrace_3628900 : CollatzResearch.WordTrace tailWord_3628900 prefixEnd_3628900 1863369947100957145760999 := by
  unfold tailWord_3628900
  simp only [CollatzResearch.WordTrace]
  refine ⟨66178428276561270811478077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88237904368748361081970769 66178428276561270811478077)
  ·
    refine ⟨24816910603710476554304279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66178428276561270811478077 24816910603710476554304279)
    ·
      refine ⟨37225365905565714831456419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24816910603710476554304279 37225365905565714831456419)
      ·
        refine ⟨55838048858348572247184629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37225365905565714831456419 55838048858348572247184629)
        ·
          refine ⟨5234817080470178648173559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55838048858348572247184629 5234817080470178648173559)
          ·
            refine ⟨7852225620705267972260339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5234817080470178648173559 7852225620705267972260339)
            ·
              refine ⟨11778338431057901958390509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852225620705267972260339 11778338431057901958390509)
              ·
                refine ⟨4416876911646713234396441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11778338431057901958390509 4416876911646713234396441)
                ·
                  refine ⟨3312657683735034925797331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4416876911646713234396441 3312657683735034925797331)
                  ·
                    refine ⟨4968986525602552388695997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3312657683735034925797331 4968986525602552388695997)
                    ·
                      refine ⟨1863369947100957145760999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4968986525602552388695997 1863369947100957145760999)
                      ·
                        rfl

theorem cell23_3628900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_3628900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628900 prefixEnd_3628900 := by exact prefixLift 3628900
  have htrace : WordTrace (prefixWord ++ tailWord_3628900) baseStart_3628900 baseEnd_3628900 := by
    simpa [prefixWord, tailWord_3628900, baseEnd_3628900] using wordTrace_append hprefix tailTrace_3628900
  have hstable : (prefixWord ++ tailWord_3628900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628900).length < 2 ^ (prefixWord ++ tailWord_3628900).sum := by decide
  have hdescent : baseEnd_3628900 < baseStart_3628900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628910 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_3628910 : Nat := 118140960795 + 3628910 * 2 ^ 59
def prefixEnd_3628910 : Nat := 4983230072969 + 3 ^ 40 * 3628910 * 2
def baseEnd_3628910 : Nat := 1863375081907502106635953

theorem tailTrace_3628910 : CollatzResearch.WordTrace tailWord_3628910 prefixEnd_3628910 1863375081907502106635953 := by
  unfold tailWord_3628910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16544652660385789166352523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88238147522057542220546789 16544652660385789166352523)
  ·
    refine ⟨24816978990578683749528785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16544652660385789166352523 24816978990578683749528785)
    ·
      refine ⟨18612734242934012812146589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24816978990578683749528785 18612734242934012812146589)
      ·
        refine ⟨6979775341100254804554971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18612734242934012812146589 6979775341100254804554971)
        ·
          refine ⟨10469663011650382206832457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6979775341100254804554971 10469663011650382206832457)
          ·
            refine ⟨7852247258737786655124343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10469663011650382206832457 7852247258737786655124343)
            ·
              refine ⟨11778370888106679982686515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852247258737786655124343 11778370888106679982686515)
              ·
                refine ⟨17667556332160019974029773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11778370888106679982686515 17667556332160019974029773)
                ·
                  refine ⟨6625333624560007490261165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17667556332160019974029773 6625333624560007490261165)
                  ·
                    refine ⟨2484500109210002808847937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6625333624560007490261165 2484500109210002808847937)
                    ·
                      refine ⟨1863375081907502106635953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484500109210002808847937 1863375081907502106635953)
                      ·
                        rfl

theorem cell23_3628910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_3628910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628910 prefixEnd_3628910 := by exact prefixLift 3628910
  have htrace : WordTrace (prefixWord ++ tailWord_3628910) baseStart_3628910 baseEnd_3628910 := by
    simpa [prefixWord, tailWord_3628910, baseEnd_3628910] using wordTrace_append hprefix tailTrace_3628910
  have hstable : (prefixWord ++ tailWord_3628910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628910).length < 2 ^ (prefixWord ++ tailWord_3628910).sum := by decide
  have hdescent : baseEnd_3628910 < baseStart_3628910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628919 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_3628919 : Nat := 118140960795 + 3628919 * 2 ^ 59
def prefixEnd_3628919 : Nat := 4983230072969 + 3 ^ 40 * 3628919 * 2
def baseEnd_3628919 : Nat := 1863379703233392571423411

theorem tailTrace_3628919 : CollatzResearch.WordTrace tailWord_3628919 prefixEnd_3628919 1863379703233392571423411 := by
  unfold tailWord_3628919
  simp only [CollatzResearch.WordTrace]
  refine ⟨132357549540053707867897811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88238366360035805245265207 132357549540053707867897811)
  ·
    refine ⟨198536324310080561801846717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132357549540053707867897811 198536324310080561801846717)
    ·
      refine ⟨74451121616280210675692519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198536324310080561801846717 74451121616280210675692519)
      ·
        refine ⟨111676682424420316013538779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74451121616280210675692519 111676682424420316013538779)
        ·
          refine ⟨167515023636630474020308169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111676682424420316013538779 167515023636630474020308169)
          ·
            refine ⟨125636267727472855515231127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167515023636630474020308169 125636267727472855515231127)
            ·
              refine ⟨188454401591209283272846691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125636267727472855515231127 188454401591209283272846691)
              ·
                refine ⟨282681602386813924909270037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188454401591209283272846691 282681602386813924909270037)
                ·
                  refine ⟨13250700111881902730122033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282681602386813924909270037 13250700111881902730122033)
                  ·
                    refine ⟨9938025083911427047591525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13250700111881902730122033 9938025083911427047591525)
                    ·
                      refine ⟨1863379703233392571423411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9938025083911427047591525 1863379703233392571423411)
                      ·
                        rfl

theorem cell23_3628919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_3628919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628919 prefixEnd_3628919 := by exact prefixLift 3628919
  have htrace : WordTrace (prefixWord ++ tailWord_3628919) baseStart_3628919 baseEnd_3628919 := by
    simpa [prefixWord, tailWord_3628919, baseEnd_3628919] using wordTrace_append hprefix tailTrace_3628919
  have hstable : (prefixWord ++ tailWord_3628919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628919).length < 2 ^ (prefixWord ++ tailWord_3628919).sum := by decide
  have hdescent : baseEnd_3628919 < baseStart_3628919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3628969 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_3628969 : Nat := 118140960795 + 3628969 * 2 ^ 59
def prefixEnd_3628969 : Nat := 4983230072969 + 3 ^ 40 * 3628969 * 2
def baseEnd_3628969 : Nat := 1863405377266117375798181

theorem tailTrace_3628969 : CollatzResearch.WordTrace tailWord_3628969 prefixEnd_3628969 1863405377266117375798181 := by
  unfold tailWord_3628969
  simp only [CollatzResearch.WordTrace]
  refine ⟨132359373189872566407217961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88239582126581710938145307 132359373189872566407217961)
  ·
    refine ⟨99269529892404424805413471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132359373189872566407217961 99269529892404424805413471)
    ·
      refine ⟨148904294838606637208120207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99269529892404424805413471 148904294838606637208120207)
      ·
        refine ⟨223356442257909955812180311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148904294838606637208120207 223356442257909955812180311)
        ·
          refine ⟨335034663386864933718270467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223356442257909955812180311 335034663386864933718270467)
          ·
            refine ⟨502551995080297400577405701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335034663386864933718270467 502551995080297400577405701)
            ·
              refine ⟨94228499077555762608263569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502551995080297400577405701 94228499077555762608263569)
              ·
                refine ⟨70671374308166821956197677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94228499077555762608263569 70671374308166821956197677)
                ·
                  refine ⟨26501765365562558233574129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70671374308166821956197677 26501765365562558233574129)
                  ·
                    refine ⟨19876324024171918675180597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26501765365562558233574129 19876324024171918675180597)
                    ·
                      refine ⟨1863405377266117375798181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19876324024171918675180597 1863405377266117375798181)
                      ·
                        rfl

theorem cell23_3628969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_3628969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3628969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3628969 prefixEnd_3628969 := by exact prefixLift 3628969
  have htrace : WordTrace (prefixWord ++ tailWord_3628969) baseStart_3628969 baseEnd_3628969 := by
    simpa [prefixWord, tailWord_3628969, baseEnd_3628969] using wordTrace_append hprefix tailTrace_3628969
  have hstable : (prefixWord ++ tailWord_3628969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3628969).length < 2 ^ (prefixWord ++ tailWord_3628969).sum := by decide
  have hdescent : baseEnd_3628969 < baseStart_3628969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3628969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629016 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 3, 4, 3]
def baseStart_3629016 : Nat := 118140960795 + 3629016 * 2 ^ 59
def prefixEnd_3629016 : Nat := 4983230072969 + 3 ^ 40 * 3629016 * 2
def baseEnd_3629016 : Nat := 1863429510856878691910465

theorem tailTrace_3629016 : CollatzResearch.WordTrace tailWord_3629016 prefixEnd_3629016 1863429510856878691910465 := by
  unfold tailWord_3629016
  simp only [CollatzResearch.WordTrace]
  refine ⟨66180543710351146717089451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88240724947134862289452601 66180543710351146717089451)
  ·
    refine ⟨99270815565526720075634177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66180543710351146717089451 99270815565526720075634177)
    ·
      refine ⟨74453111674145040056725633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99270815565526720075634177 74453111674145040056725633)
      ·
        refine ⟨55839833755608780042544225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74453111674145040056725633 55839833755608780042544225)
        ·
          refine ⟨41879875316706585031908169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55839833755608780042544225 41879875316706585031908169)
          ·
            refine ⟨31409906487529938773931127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41879875316706585031908169 31409906487529938773931127)
            ·
              refine ⟨47114859731294908160896691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31409906487529938773931127 47114859731294908160896691)
              ·
                refine ⟨70672289596942362241345037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47114859731294908160896691 70672289596942362241345037)
                ·
                  refine ⟨26502108598853385840504389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70672289596942362241345037 26502108598853385840504389)
                  ·
                    refine ⟨4969145362285009845094573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26502108598853385840504389 4969145362285009845094573)
                    ·
                      refine ⟨1863429510856878691910465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4969145362285009845094573 1863429510856878691910465)
                      ·
                        rfl

theorem cell23_3629016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_3629016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629016 prefixEnd_3629016 := by exact prefixLift 3629016
  have htrace : WordTrace (prefixWord ++ tailWord_3629016) baseStart_3629016 baseEnd_3629016 := by
    simpa [prefixWord, tailWord_3629016, baseEnd_3629016] using wordTrace_append hprefix tailTrace_3629016
  have hstable : (prefixWord ++ tailWord_3629016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629016).length < 2 ^ (prefixWord ++ tailWord_3629016).sum := by decide
  have hdescent : baseEnd_3629016 < baseStart_3629016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629023 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 3, 4]
def baseStart_3629023 : Nat := 118140960795 + 3629023 * 2 ^ 59
def prefixEnd_3629023 : Nat := 4983230072969 + 3 ^ 40 * 3629023 * 2
def baseEnd_3629023 : Nat := 621144368407153388174311

theorem tailTrace_3629023 : CollatzResearch.WordTrace tailWord_3629023 prefixEnd_3629023 621144368407153388174311 := by
  unfold tailWord_3629023
  simp only [CollatzResearch.WordTrace]
  refine ⟨132361342731676933629683723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88240895154451289086455815 132361342731676933629683723)
  ·
    refine ⟨198542014097515400444525585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132361342731676933629683723 198542014097515400444525585)
    ·
      refine ⟨148906510573136550333394189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198542014097515400444525585 148906510573136550333394189)
      ·
        refine ⟨55839941464926206375022821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148906510573136550333394189 55839941464926206375022821)
        ·
          refine ⟨10469989024673663695316779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55839941464926206375022821 10469989024673663695316779)
          ·
            refine ⟨15704983537010495542975169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10469989024673663695316779 15704983537010495542975169)
            ·
              refine ⟨11778737652757871657231377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15704983537010495542975169 11778737652757871657231377)
              ·
                refine ⟨8834053239568403742923533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11778737652757871657231377 8834053239568403742923533)
                ·
                  refine ⟨3312769964838151403596325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8834053239568403742923533 3312769964838151403596325)
                  ·
                    refine ⟨621144368407153388174311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312769964838151403596325 621144368407153388174311)
                    ·
                      rfl

theorem cell23_3629023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_3629023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629023 prefixEnd_3629023 := by exact prefixLift 3629023
  have htrace : WordTrace (prefixWord ++ tailWord_3629023) baseStart_3629023 baseEnd_3629023 := by
    simpa [prefixWord, tailWord_3629023, baseEnd_3629023] using wordTrace_append hprefix tailTrace_3629023
  have hstable : (prefixWord ++ tailWord_3629023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629023).length < 2 ^ (prefixWord ++ tailWord_3629023).sum := by decide
  have hdescent : baseEnd_3629023 < baseStart_3629023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629040 : List Nat := [2, 1, 1, 1, 3, 2, 5, 3, 1, 4]
def baseStart_3629040 : Nat := 118140960795 + 3629040 * 2 ^ 59
def prefixEnd_3629040 : Nat := 4983230072969 + 3 ^ 40 * 3629040 * 2
def baseEnd_3629040 : Nat := 621147278130862199336785

theorem tailTrace_3629040 : CollatzResearch.WordTrace tailWord_3629040 prefixEnd_3629040 621147278130862199336785 := by
  unfold tailWord_3629040
  simp only [CollatzResearch.WordTrace]
  refine ⟨66180981386307672766526287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88241308515076897022035049 66180981386307672766526287)
  ·
    refine ⟨99271472079461509149789431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66180981386307672766526287 99271472079461509149789431)
    ·
      refine ⟨148907208119192263724684147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99271472079461509149789431 148907208119192263724684147)
      ·
        refine ⟨223360812178788395587026221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148907208119192263724684147 223360812178788395587026221)
        ·
          refine ⟨83760304567045648345134833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223360812178788395587026221 83760304567045648345134833)
          ·
            refine ⟨62820228425284236258851125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83760304567045648345134833 62820228425284236258851125)
            ·
              refine ⟨5889396414870397149267293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62820228425284236258851125 5889396414870397149267293)
              ·
                refine ⟨2208523655576398930975235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5889396414870397149267293 2208523655576398930975235)
                ·
                  refine ⟨3312785483364598396462853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208523655576398930975235 3312785483364598396462853)
                  ·
                    refine ⟨621147278130862199336785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312785483364598396462853 621147278130862199336785)
                    ·
                      rfl

theorem cell23_3629040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 4].length) (baseStart_3629040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629040 prefixEnd_3629040 := by exact prefixLift 3629040
  have htrace : WordTrace (prefixWord ++ tailWord_3629040) baseStart_3629040 baseEnd_3629040 := by
    simpa [prefixWord, tailWord_3629040, baseEnd_3629040] using wordTrace_append hprefix tailTrace_3629040
  have hstable : (prefixWord ++ tailWord_3629040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629040).length < 2 ^ (prefixWord ++ tailWord_3629040).sum := by decide
  have hdescent : baseEnd_3629040 < baseStart_3629040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629057 : List Nat := [1, 2, 4, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3629057 : Nat := 118140960795 + 3629057 * 2 ^ 59
def prefixEnd_3629057 : Nat := 4983230072969 + 3 ^ 40 * 3629057 * 2
def baseEnd_3629057 : Nat := 621150187854571010499259

theorem tailTrace_3629057 : CollatzResearch.WordTrace tailWord_3629057 prefixEnd_3629057 621150187854571010499259 := by
  unfold tailWord_3629057
  simp only [CollatzResearch.WordTrace]
  refine ⟨132362582813553757436421425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88241721875702504957614283 132362582813553757436421425)
  ·
    refine ⟨99271937110165318077316069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132362582813553757436421425 99271937110165318077316069)
    ·
      refine ⟨18613488208155997139496763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99271937110165318077316069 18613488208155997139496763)
      ·
        refine ⟨27920232312233995709245145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18613488208155997139496763 27920232312233995709245145)
        ·
          refine ⟨20940174234175496781933859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27920232312233995709245145 20940174234175496781933859)
          ·
            refine ⟨31410261351263245172900789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20940174234175496781933859 31410261351263245172900789)
            ·
              refine ⟨2944712001680929234959449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31410261351263245172900789 2944712001680929234959449)
              ·
                refine ⟨2208534001260696926219587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944712001680929234959449 2208534001260696926219587)
                ·
                  refine ⟨3312801001891045389329381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208534001260696926219587 3312801001891045389329381)
                  ·
                    refine ⟨621150187854571010499259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312801001891045389329381 621150187854571010499259)
                    ·
                      rfl

theorem cell23_3629057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3629057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629057 prefixEnd_3629057 := by exact prefixLift 3629057
  have htrace : WordTrace (prefixWord ++ tailWord_3629057) baseStart_3629057 baseEnd_3629057 := by
    simpa [prefixWord, tailWord_3629057, baseEnd_3629057] using wordTrace_append hprefix tailTrace_3629057
  have hstable : (prefixWord ++ tailWord_3629057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629057).length < 2 ^ (prefixWord ++ tailWord_3629057).sum := by decide
  have hdescent : baseEnd_3629057 < baseStart_3629057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629108 : List Nat := [2, 5, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_3629108 : Nat := 118140960795 + 3629108 * 2 ^ 59
def prefixEnd_3629108 : Nat := 4983230072969 + 3 ^ 40 * 3629108 * 2
def baseEnd_3629108 : Nat := 621158917025697443986681

theorem tailTrace_3629108 : CollatzResearch.WordTrace tailWord_3629108 prefixEnd_3629108 621158917025697443986681 := by
  unfold tailWord_3629108
  simp only [CollatzResearch.WordTrace]
  refine ⟨66182221468184496573263989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88242961957579328764351985 66182221468184496573263989)
  ·
    refine ⟨6204583262642296553743499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66182221468184496573263989 6204583262642296553743499)
    ·
      refine ⟨9306874893963444830615249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6204583262642296553743499 9306874893963444830615249)
      ·
        refine ⟨6980156170472583622961437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9306874893963444830615249 6980156170472583622961437)
        ·
          refine ⟨2617558563927218858610539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6980156170472583622961437 2617558563927218858610539)
          ·
            refine ⟨3926337845890828287915809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617558563927218858610539 3926337845890828287915809)
            ·
              refine ⟨2944753384418121215936857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926337845890828287915809 2944753384418121215936857)
              ·
                refine ⟨2208565038313590911952643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944753384418121215936857 2208565038313590911952643)
                ·
                  refine ⟨3312847557470386367928965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208565038313590911952643 3312847557470386367928965)
                  ·
                    refine ⟨621158917025697443986681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3312847557470386367928965 621158917025697443986681)
                    ·
                      rfl

theorem cell23_3629108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_3629108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629108 prefixEnd_3629108 := by exact prefixLift 3629108
  have htrace : WordTrace (prefixWord ++ tailWord_3629108) baseStart_3629108 baseEnd_3629108 := by
    simpa [prefixWord, tailWord_3629108, baseEnd_3629108] using wordTrace_append hprefix tailTrace_3629108
  have hstable : (prefixWord ++ tailWord_3629108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629108).length < 2 ^ (prefixWord ++ tailWord_3629108).sum := by decide
  have hdescent : baseEnd_3629108 < baseStart_3629108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629140 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_3629140 : Nat := 118140960795 + 3629140 * 2 ^ 59
def prefixEnd_3629140 : Nat := 4983230072969 + 3 ^ 40 * 3629140 * 2
def baseEnd_3629140 : Nat := 1863493182458036206759895

theorem tailTrace_3629140 : CollatzResearch.WordTrace tailWord_3629140 prefixEnd_3629140 1863493182458036206759895 := by
  unfold tailWord_3629140
  simp only [CollatzResearch.WordTrace]
  refine ⟨66182805036126531305846437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88243740048168708407795249 66182805036126531305846437)
  ·
    refine ⟨12409275944273724619846207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66182805036126531305846437 12409275944273724619846207)
    ·
      refine ⟨18613913916410586929769311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409275944273724619846207 18613913916410586929769311)
      ·
        refine ⟨27920870874615880394653967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18613913916410586929769311 27920870874615880394653967)
        ·
          refine ⟨41881306311923820591980951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27920870874615880394653967 41881306311923820591980951)
          ·
            refine ⟨62821959467885730887971427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41881306311923820591980951 62821959467885730887971427)
            ·
              refine ⟨94232939201828596331957141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62821959467885730887971427 94232939201828596331957141)
              ·
                refine ⟨4417169025085715453060491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94232939201828596331957141 4417169025085715453060491)
                ·
                  refine ⟨6625753537628573179590737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417169025085715453060491 6625753537628573179590737)
                  ·
                    refine ⟨4969315153221429884693053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6625753537628573179590737 4969315153221429884693053)
                    ·
                      refine ⟨1863493182458036206759895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4969315153221429884693053 1863493182458036206759895)
                      ·
                        rfl

theorem cell23_3629140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_3629140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629140 prefixEnd_3629140 := by exact prefixLift 3629140
  have htrace : WordTrace (prefixWord ++ tailWord_3629140) baseStart_3629140 baseEnd_3629140 := by
    simpa [prefixWord, tailWord_3629140, baseEnd_3629140] using wordTrace_append hprefix tailTrace_3629140
  have hstable : (prefixWord ++ tailWord_3629140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629140).length < 2 ^ (prefixWord ++ tailWord_3629140).sum := by decide
  have hdescent : baseEnd_3629140 < baseStart_3629140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629157 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 1, 2, 3]
def baseStart_3629157 : Nat := 118140960795 + 3629157 * 2 ^ 59
def prefixEnd_3629157 : Nat := 4983230072969 + 3 ^ 40 * 3629157 * 2
def baseEnd_3629157 : Nat := 1863501911629162640247317

theorem tailTrace_3629157 : CollatzResearch.WordTrace tailWord_3629157 prefixEnd_3629157 1863501911629162640247317 := by
  unfold tailWord_3629157
  simp only [CollatzResearch.WordTrace]
  refine ⟨132366230113191474515061725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88244153408794316343374483 132366230113191474515061725)
  ·
    refine ⟨49637336292446802943148147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132366230113191474515061725 49637336292446802943148147)
    ·
      refine ⟨74456004438670204414722221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49637336292446802943148147 74456004438670204414722221)
      ·
        refine ⟨27921001664501326655520833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74456004438670204414722221 27921001664501326655520833)
        ·
          refine ⟨20940751248375994991640625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27921001664501326655520833 20940751248375994991640625)
          ·
            refine ⟨15705563436281996243730469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20940751248375994991640625 15705563436281996243730469)
            ·
              refine ⟨2944793144302874295699463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15705563436281996243730469 2944793144302874295699463)
              ·
                refine ⟨4417189716454311443549195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2944793144302874295699463 4417189716454311443549195)
                ·
                  refine ⟨6625784574681467165323793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417189716454311443549195 6625784574681467165323793)
                  ·
                    refine ⟨4969338431011100373992845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6625784574681467165323793 4969338431011100373992845)
                    ·
                      refine ⟨1863501911629162640247317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4969338431011100373992845 1863501911629162640247317)
                      ·
                        rfl

theorem cell23_3629157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_3629157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629157 prefixEnd_3629157 := by exact prefixLift 3629157
  have htrace : WordTrace (prefixWord ++ tailWord_3629157) baseStart_3629157 baseEnd_3629157 := by
    simpa [prefixWord, tailWord_3629157, baseEnd_3629157] using wordTrace_append hprefix tailTrace_3629157
  have hstable : (prefixWord ++ tailWord_3629157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629157).length < 2 ^ (prefixWord ++ tailWord_3629157).sum := by decide
  have hdescent : baseEnd_3629157 < baseStart_3629157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629213 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3629213 : Nat := 118140960795 + 3629213 * 2 ^ 59
def prefixEnd_3629213 : Nat := 4983230072969 + 3 ^ 40 * 3629213 * 2
def baseEnd_3629213 : Nat := 1863530666545814421147059

theorem tailTrace_3629213 : CollatzResearch.WordTrace tailWord_3629213 prefixEnd_3629213 1863530666545814421147059 := by
  unfold tailWord_3629213
  simp only [CollatzResearch.WordTrace]
  refine ⟨132368272600988596079100293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88245515067325730719400195 132368272600988596079100293)
  ·
    refine ⟨24819051112685361764831305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132368272600988596079100293 24819051112685361764831305)
    ·
      refine ⟨18614288334514021323623479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24819051112685361764831305 18614288334514021323623479)
      ·
        refine ⟨27921432501771031985435219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18614288334514021323623479 27921432501771031985435219)
        ·
          refine ⟨41882148752656547978152829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27921432501771031985435219 41882148752656547978152829)
          ·
            refine ⟨15705805782246205491807311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41882148752656547978152829 15705805782246205491807311)
            ·
              refine ⟨23558708673369308237710967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15705805782246205491807311 23558708673369308237710967)
              ·
                refine ⟨35338063010053962356566451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23558708673369308237710967 35338063010053962356566451)
                ·
                  refine ⟨53007094515080943534849677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35338063010053962356566451 53007094515080943534849677)
                  ·
                    refine ⟨19877660443155353825568629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53007094515080943534849677 19877660443155353825568629)
                    ·
                      refine ⟨1863530666545814421147059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19877660443155353825568629 1863530666545814421147059)
                      ·
                        rfl

theorem cell23_3629213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3629213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629213 prefixEnd_3629213 := by exact prefixLift 3629213
  have htrace : WordTrace (prefixWord ++ tailWord_3629213) baseStart_3629213 baseEnd_3629213 := by
    simpa [prefixWord, tailWord_3629213, baseEnd_3629213] using wordTrace_append hprefix tailTrace_3629213
  have hstable : (prefixWord ++ tailWord_3629213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629213).length < 2 ^ (prefixWord ++ tailWord_3629213).sum := by decide
  have hdescent : baseEnd_3629213 < baseStart_3629213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629243 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 3]
def baseStart_3629243 : Nat := 118140960795 + 3629243 * 2 ^ 59
def prefixEnd_3629243 : Nat := 4983230072969 + 3 ^ 40 * 3629243 * 2
def baseEnd_3629243 : Nat := 1863546070965449303771921

theorem tailTrace_3629243 : CollatzResearch.WordTrace tailWord_3629243 prefixEnd_3629243 1863546070965449303771921 := by
  unfold tailWord_3629243
  simp only [CollatzResearch.WordTrace]
  refine ⟨132369366790879911202692383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88246244527253274135128255 132369366790879911202692383)
  ·
    refine ⟨198554050186319866804038575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132369366790879911202692383 198554050186319866804038575)
    ·
      refine ⟨297831075279479800206057863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198554050186319866804038575 297831075279479800206057863)
      ·
        refine ⟨446746612919219700309086795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297831075279479800206057863 446746612919219700309086795)
        ·
          refine ⟨670119919378829550463630193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446746612919219700309086795 670119919378829550463630193)
          ·
            refine ⟨502589939534122162847722645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670119919378829550463630193 502589939534122162847722645)
            ·
              refine ⟨23558903415661976383486999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 502589939534122162847722645 23558903415661976383486999)
              ·
                refine ⟨35338355123492964575230499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23558903415661976383486999 35338355123492964575230499)
                ·
                  refine ⟨53007532685239446862845749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35338355123492964575230499 53007532685239446862845749)
                  ·
                    refine ⟨4969456189241198143391789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53007532685239446862845749 4969456189241198143391789)
                    ·
                      refine ⟨1863546070965449303771921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4969456189241198143391789 1863546070965449303771921)
                      ·
                        rfl

theorem cell23_3629243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 3].length) (baseStart_3629243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629243 prefixEnd_3629243 := by exact prefixLift 3629243
  have htrace : WordTrace (prefixWord ++ tailWord_3629243) baseStart_3629243 baseEnd_3629243 := by
    simpa [prefixWord, tailWord_3629243, baseEnd_3629243] using wordTrace_append hprefix tailTrace_3629243
  have hstable : (prefixWord ++ tailWord_3629243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629243).length < 2 ^ (prefixWord ++ tailWord_3629243).sum := by decide
  have hdescent : baseEnd_3629243 < baseStart_3629243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629273 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3629273 : Nat := 118140960795 + 3629273 * 2 ^ 59
def prefixEnd_3629273 : Nat := 4983230072969 + 3 ^ 40 * 3629273 * 2
def baseEnd_3629273 : Nat := 1863561475385084186396783

theorem tailTrace_3629273 : CollatzResearch.WordTrace tailWord_3629273 prefixEnd_3629273 1863561475385084186396783 := by
  unfold tailWord_3629273
  simp only [CollatzResearch.WordTrace]
  refine ⟨132370460980771226326284473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88246973987180817550856315 132370460980771226326284473)
  ·
    refine ⟨99277845735578419744713355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132370460980771226326284473 99277845735578419744713355)
    ·
      refine ⟨148916768603367629617070033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99277845735578419744713355 148916768603367629617070033)
      ·
        refine ⟨111687576452525722212802525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148916768603367629617070033 111687576452525722212802525)
        ·
          refine ⟨41882841169697145829800947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111687576452525722212802525 41882841169697145829800947)
          ·
            refine ⟨62824261754545718744701421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41882841169697145829800947 62824261754545718744701421)
            ·
              refine ⟨23559098157954644529263033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62824261754545718744701421 23559098157954644529263033)
              ·
                refine ⟨17669323618465983396947275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23559098157954644529263033 17669323618465983396947275)
                ·
                  refine ⟨26503985427698975095420913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17669323618465983396947275 26503985427698975095420913)
                  ·
                    refine ⟨19877989070774231321565685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26503985427698975095420913 19877989070774231321565685)
                    ·
                      refine ⟨1863561475385084186396783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19877989070774231321565685 1863561475385084186396783)
                      ·
                        rfl

theorem cell23_3629273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3629273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629273 prefixEnd_3629273 := by exact prefixLift 3629273
  have htrace : WordTrace (prefixWord ++ tailWord_3629273) baseStart_3629273 baseEnd_3629273 := by
    simpa [prefixWord, tailWord_3629273, baseEnd_3629273] using wordTrace_append hprefix tailTrace_3629273
  have hstable : (prefixWord ++ tailWord_3629273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629273).length < 2 ^ (prefixWord ++ tailWord_3629273).sum := by decide
  have hdescent : baseEnd_3629273 < baseStart_3629273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629287 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3629287 : Nat := 118140960795 + 3629287 * 2 ^ 59
def prefixEnd_3629287 : Nat := 4983230072969 + 3 ^ 40 * 3629287 * 2
def baseEnd_3629287 : Nat := 1863568664114247131621719

theorem tailTrace_3629287 : CollatzResearch.WordTrace tailWord_3629287 prefixEnd_3629287 1863568664114247131621719 := by
  unfold tailWord_3629287
  simp only [CollatzResearch.WordTrace]
  refine ⟨132370971602720506717294115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88247314401813671144862743 132370971602720506717294115)
  ·
    refine ⟨198556457404080760075941173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132370971602720506717294115 198556457404080760075941173)
    ·
      refine ⟨18614667881632571257119485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198556457404080760075941173 18614667881632571257119485)
      ·
        refine ⟨6980500455612214221419807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18614667881632571257119485 6980500455612214221419807)
        ·
          refine ⟨10470750683418321332129711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6980500455612214221419807 10470750683418321332129711)
          ·
            refine ⟨15706126025127481998194567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10470750683418321332129711 15706126025127481998194567)
            ·
              refine ⟨23559189037691222997291851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15706126025127481998194567 23559189037691222997291851)
              ·
                refine ⟨35338783556536834495937777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23559189037691222997291851 35338783556536834495937777)
                ·
                  refine ⟨26504087667402625871953333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35338783556536834495937777 26504087667402625871953333)
                  ·
                    refine ⟨2484758218818996175495625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26504087667402625871953333 2484758218818996175495625)
                    ·
                      refine ⟨1863568664114247131621719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484758218818996175495625 1863568664114247131621719)
                      ·
                        rfl

theorem cell23_3629287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3629287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629287 prefixEnd_3629287 := by exact prefixLift 3629287
  have htrace : WordTrace (prefixWord ++ tailWord_3629287) baseStart_3629287 baseEnd_3629287 := by
    simpa [prefixWord, tailWord_3629287, baseEnd_3629287] using wordTrace_append hprefix tailTrace_3629287
  have hstable : (prefixWord ++ tailWord_3629287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629287).length < 2 ^ (prefixWord ++ tailWord_3629287).sum := by decide
  have hdescent : baseEnd_3629287 < baseStart_3629287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629314 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3629314 : Nat := 118140960795 + 3629314 * 2 ^ 59
def prefixEnd_3629314 : Nat := 4983230072969 + 3 ^ 40 * 3629314 * 2
def baseEnd_3629314 : Nat := 621194176030639508661365

theorem tailTrace_3629314 : CollatzResearch.WordTrace tailWord_3629314 prefixEnd_3629314 621194176030639508661365 := by
  unfold tailWord_3629314
  simp only [CollatzResearch.WordTrace]
  refine ⟨33092989093405672582131749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88247970915748460219017997 33092989093405672582131749)
  ·
    refine ⟨6204935455013563609149703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33092989093405672582131749 6204935455013563609149703)
    ·
      refine ⟨9307403182520345413724555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6204935455013563609149703 9307403182520345413724555)
      ·
        refine ⟨13961104773780518120586833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9307403182520345413724555 13961104773780518120586833)
        ·
          refine ⟨10470828580335388590440125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13961104773780518120586833 10470828580335388590440125)
          ·
            refine ⟨3926560717625770721415047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10470828580335388590440125 3926560717625770721415047)
            ·
              refine ⟨5889841076438656082122571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926560717625770721415047 5889841076438656082122571)
              ·
                refine ⟨8834761614657984123183857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5889841076438656082122571 8834761614657984123183857)
                ·
                  refine ⟨6626071210993488092387893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8834761614657984123183857 6626071210993488092387893)
                  ·
                    refine ⟨621194176030639508661365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6626071210993488092387893 621194176030639508661365)
                    ·
                      rfl

theorem cell23_3629314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3629314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629314 prefixEnd_3629314 := by exact prefixLift 3629314
  have htrace : WordTrace (prefixWord ++ tailWord_3629314) baseStart_3629314 baseEnd_3629314 := by
    simpa [prefixWord, tailWord_3629314, baseEnd_3629314] using wordTrace_append hprefix tailTrace_3629314
  have hstable : (prefixWord ++ tailWord_3629314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629314).length < 2 ^ (prefixWord ++ tailWord_3629314).sum := by decide
  have hdescent : baseEnd_3629314 < baseStart_3629314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629323 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 8]
def baseStart_3629323 : Nat := 118140960795 + 3629323 * 2 ^ 59
def prefixEnd_3629323 : Nat := 4983230072969 + 3 ^ 40 * 3629323 * 2
def baseEnd_3629323 : Nat := 207065238824200998974617

theorem tailTrace_3629323 : CollatzResearch.WordTrace tailWord_3629323 prefixEnd_3629323 207065238824200998974617 := by
  unfold tailWord_3629323
  simp only [CollatzResearch.WordTrace]
  refine ⟨132372284630590084865604623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88248189753726723243736415 132372284630590084865604623)
  ·
    refine ⟨198558426945885127298406935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132372284630590084865604623 198558426945885127298406935)
    ·
      refine ⟨297837640418827690947610403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198558426945885127298406935 297837640418827690947610403)
      ·
        refine ⟨446756460628241536421415605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297837640418827690947610403 446756460628241536421415605)
        ·
          refine ⟨41883418183897644039507713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446756460628241536421415605 41883418183897644039507713)
          ·
            refine ⟨31412563637923233029630785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41883418183897644039507713 31412563637923233029630785)
            ·
              refine ⟨23559422728442424772223089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31412563637923233029630785 23559422728442424772223089)
              ·
                refine ⟨17669567046331818579167317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23559422728442424772223089 17669567046331818579167317)
                ·
                  refine ⟨207065238824200998974617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17669567046331818579167317 207065238824200998974617)
                  ·
                    rfl

theorem cell23_3629323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 8].length) (baseStart_3629323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629323 prefixEnd_3629323 := by exact prefixLift 3629323
  have htrace : WordTrace (prefixWord ++ tailWord_3629323) baseStart_3629323 baseEnd_3629323 := by
    simpa [prefixWord, tailWord_3629323, baseEnd_3629323] using wordTrace_append hprefix tailTrace_3629323
  have hstable : (prefixWord ++ tailWord_3629323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629323).length < 2 ^ (prefixWord ++ tailWord_3629323).sum := by decide
  have hdescent : baseEnd_3629323 < baseStart_3629323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629344 : List Nat := [2, 1, 1, 5, 2, 1, 2, 4, 1, 4]
def baseStart_3629344 : Nat := 118140960795 + 3629344 * 2 ^ 59
def prefixEnd_3629344 : Nat := 4983230072969 + 3 ^ 40 * 3629344 * 2
def baseEnd_3629344 : Nat := 621199310837184469536319

theorem tailTrace_3629344 : CollatzResearch.WordTrace tailWord_3629344 prefixEnd_3629344 621199310837184469536319 := by
  unfold tailWord_3629344
  simp only [CollatzResearch.WordTrace]
  refine ⟨66186525281757002726059543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88248700375676003634746057 66186525281757002726059543)
  ·
    refine ⟨99279787922635504089089315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66186525281757002726059543 99279787922635504089089315)
    ·
      refine ⟨148919681883953256133633973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99279787922635504089089315 148919681883953256133633973)
      ·
        refine ⟨13961220176620617762528185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148919681883953256133633973 13961220176620617762528185)
        ·
          refine ⟨10470915132465463321896139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13961220176620617762528185 10470915132465463321896139)
          ·
            refine ⟨15706372698698194982844209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10470915132465463321896139 15706372698698194982844209)
            ·
              refine ⟨11779779524023646237133157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15706372698698194982844209 11779779524023646237133157)
              ·
                refine ⟨2208708660754433669462467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11779779524023646237133157 2208708660754433669462467)
                ·
                  refine ⟨3313062991131650504193701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208708660754433669462467 3313062991131650504193701)
                  ·
                    refine ⟨621199310837184469536319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313062991131650504193701 621199310837184469536319)
                    ·
                      rfl

theorem cell23_3629344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 4].length) (baseStart_3629344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629344 prefixEnd_3629344 := by exact prefixLift 3629344
  have htrace : WordTrace (prefixWord ++ tailWord_3629344) baseStart_3629344 baseEnd_3629344 := by
    simpa [prefixWord, tailWord_3629344, baseEnd_3629344] using wordTrace_append hprefix tailTrace_3629344
  have hstable : (prefixWord ++ tailWord_3629344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629344).length < 2 ^ (prefixWord ++ tailWord_3629344).sum := by decide
  have hdescent : baseEnd_3629344 < baseStart_3629344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629417 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 2, 4]
def baseStart_3629417 : Nat := 118140960795 + 3629417 * 2 ^ 59
def prefixEnd_3629417 : Nat := 4983230072969 + 3 ^ 40 * 3629417 * 2
def baseEnd_3629417 : Nat := 621211805533110540998707

theorem tailTrace_3629417 : CollatzResearch.WordTrace tailWord_3629417 prefixEnd_3629417 621211805533110540998707 := by
  unfold tailWord_3629417
  simp only [CollatzResearch.WordTrace]
  refine ⟨132375713092249538919526505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88250475394833025946351003 132375713092249538919526505)
  ·
    refine ⟨99281784819187154189644879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132375713092249538919526505 99281784819187154189644879)
    ·
      refine ⟨148922677228780731284467319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99281784819187154189644879 148922677228780731284467319)
      ·
        refine ⟨223384015843171096926700979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148922677228780731284467319 223384015843171096926700979)
        ·
          refine ⟨335076023764756645390051469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223384015843171096926700979 335076023764756645390051469)
          ·
            refine ⟨125653508911783742021269301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335076023764756645390051469 125653508911783742021269301)
            ·
              refine ⟨11780016460479725814493997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125653508911783742021269301 11780016460479725814493997)
              ·
                refine ⟨4417506172679897180435249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11780016460479725814493997 4417506172679897180435249)
                ·
                  refine ⟨3313129629509922885326437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4417506172679897180435249 3313129629509922885326437)
                  ·
                    refine ⟨621211805533110540998707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313129629509922885326437 621211805533110540998707)
                    ·
                      rfl

theorem cell23_3629417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_3629417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629417 prefixEnd_3629417 := by exact prefixLift 3629417
  have htrace : WordTrace (prefixWord ++ tailWord_3629417) baseStart_3629417 baseEnd_3629417 := by
    simpa [prefixWord, tailWord_3629417, baseEnd_3629417] using wordTrace_append hprefix tailTrace_3629417
  have hstable : (prefixWord ++ tailWord_3629417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629417).length < 2 ^ (prefixWord ++ tailWord_3629417).sum := by decide
  have hdescent : baseEnd_3629417 < baseStart_3629417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629424 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4]
def baseStart_3629424 : Nat := 118140960795 + 3629424 * 2 ^ 59
def prefixEnd_3629424 : Nat := 4983230072969 + 3 ^ 40 * 3629424 * 2
def baseEnd_3629424 : Nat := 1863639010963913095608589

theorem tailTrace_3629424 : CollatzResearch.WordTrace tailWord_3629424 prefixEnd_3629424 1863639010963913095608589 := by
  unfold tailWord_3629424
  simp only [CollatzResearch.WordTrace]
  refine ⟨66187984201612089557515663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88250645602149452743354217 66187984201612089557515663)
  ·
    refine ⟨99281976302418134336273495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66187984201612089557515663 99281976302418134336273495)
    ·
      refine ⟨148922964453627201504410243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99281976302418134336273495 148922964453627201504410243)
      ·
        refine ⟨223384446680440802256615365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148922964453627201504410243 223384446680440802256615365)
        ·
          refine ⟨41884583752582650423115381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223384446680440802256615365 41884583752582650423115381)
          ·
            refine ⟨3926679726804623477167067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41884583752582650423115381 3926679726804623477167067)
            ·
              refine ⟨5890019590206935215750601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926679726804623477167067 5890019590206935215750601)
              ·
                refine ⟨4417514692655201411812951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890019590206935215750601 4417514692655201411812951)
                ·
                  refine ⟨6626272038982802117719427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417514692655201411812951 6626272038982802117719427)
                  ·
                    refine ⟨9939408058474203176579141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626272038982802117719427 9939408058474203176579141)
                    ·
                      refine ⟨1863639010963913095608589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9939408058474203176579141 1863639010963913095608589)
                      ·
                        rfl

theorem cell23_3629424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 4].length) (baseStart_3629424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629424 prefixEnd_3629424 := by exact prefixLift 3629424
  have htrace : WordTrace (prefixWord ++ tailWord_3629424) baseStart_3629424 baseEnd_3629424 := by
    simpa [prefixWord, tailWord_3629424, baseEnd_3629424] using wordTrace_append hprefix tailTrace_3629424
  have hstable : (prefixWord ++ tailWord_3629424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629424).length < 2 ^ (prefixWord ++ tailWord_3629424).sum := by decide
  have hdescent : baseEnd_3629424 < baseStart_3629424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629437 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_3629437 : Nat := 118140960795 + 3629437 * 2 ^ 59
def prefixEnd_3629437 : Nat := 4983230072969 + 3 ^ 40 * 3629437 * 2
def baseEnd_3629437 : Nat := 1863645686212421544746029

theorem tailTrace_3629437 : CollatzResearch.WordTrace tailWord_3629437 prefixEnd_3629437 1863645686212421544746029 := by
  unfold tailWord_3629437
  simp only [CollatzResearch.WordTrace]
  refine ⟨132376442552177082335254565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88250961701451388223503043 132376442552177082335254565)
  ·
    refine ⟨24820582978533202937860231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132376442552177082335254565 24820582978533202937860231)
    ·
      refine ⟨37230874467799804406790347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24820582978533202937860231 37230874467799804406790347)
      ·
        refine ⟨55846311701699706610185521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37230874467799804406790347 55846311701699706610185521)
        ·
          refine ⟨41884733776274779957639141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55846311701699706610185521 41884733776274779957639141)
          ·
            refine ⟨7853387583051521242057339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41884733776274779957639141 7853387583051521242057339)
            ·
              refine ⟨11780081374577281863086009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7853387583051521242057339 11780081374577281863086009)
              ·
                refine ⟨8835061030932961397314507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11780081374577281863086009 8835061030932961397314507)
                ·
                  refine ⟨13252591546399442095971761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835061030932961397314507 13252591546399442095971761)
                  ·
                    refine ⟨9939443659799581571978821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13252591546399442095971761 9939443659799581571978821)
                    ·
                      refine ⟨1863645686212421544746029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9939443659799581571978821 1863645686212421544746029)
                      ·
                        rfl

theorem cell23_3629437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_3629437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629437 prefixEnd_3629437 := by exact prefixLift 3629437
  have htrace : WordTrace (prefixWord ++ tailWord_3629437) baseStart_3629437 baseEnd_3629437 := by
    simpa [prefixWord, tailWord_3629437, baseEnd_3629437] using wordTrace_append hprefix tailTrace_3629437
  have hstable : (prefixWord ++ tailWord_3629437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629437).length < 2 ^ (prefixWord ++ tailWord_3629437).sum := by decide
  have hdescent : baseEnd_3629437 < baseStart_3629437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629441 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_3629441 : Nat := 118140960795 + 3629441 * 2 ^ 59
def prefixEnd_3629441 : Nat := 4983230072969 + 3 ^ 40 * 3629441 * 2
def baseEnd_3629441 : Nat := 1863647740135039529096011

theorem tailTrace_3629441 : CollatzResearch.WordTrace tailWord_3629441 prefixEnd_3629441 1863647740135039529096011 := by
  unfold tailWord_3629441
  simp only [CollatzResearch.WordTrace]
  refine ⟨132376588444162591018400177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88251058962775060678933451 132376588444162591018400177)
  ·
    refine ⟨99282441333121943263800133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132376588444162591018400177 99282441333121943263800133)
    ·
      refine ⟨18615457749960364361962525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99282441333121943263800133 18615457749960364361962525)
      ·
        refine ⟨6980796656235136635735947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18615457749960364361962525 6980796656235136635735947)
        ·
          refine ⟨10471194984352704953603921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6980796656235136635735947 10471194984352704953603921)
          ·
            refine ⟨7853396238264528715202941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10471194984352704953603921 7853396238264528715202941)
            ·
              refine ⟨2945023589349198268201103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7853396238264528715202941 2945023589349198268201103)
              ·
                refine ⟨4417535384023797402301655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945023589349198268201103 4417535384023797402301655)
                ·
                  refine ⟨6626303076035696103452483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417535384023797402301655 6626303076035696103452483)
                  ·
                    refine ⟨9939454614053544155178725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626303076035696103452483 9939454614053544155178725)
                    ·
                      refine ⟨1863647740135039529096011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9939454614053544155178725 1863647740135039529096011)
                      ·
                        rfl

theorem cell23_3629441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_3629441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629441 prefixEnd_3629441 := by exact prefixLift 3629441
  have htrace : WordTrace (prefixWord ++ tailWord_3629441) baseStart_3629441 baseEnd_3629441 := by
    simpa [prefixWord, tailWord_3629441, baseEnd_3629441] using wordTrace_append hprefix tailTrace_3629441
  have hstable : (prefixWord ++ tailWord_3629441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629441).length < 2 ^ (prefixWord ++ tailWord_3629441).sum := by decide
  have hdescent : baseEnd_3629441 < baseStart_3629441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629474 : List Nat := [3, 3, 1, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3629474 : Nat := 118140960795 + 3629474 * 2 ^ 59
def prefixEnd_3629474 : Nat := 4983230072969 + 3 ^ 40 * 3629474 * 2
def baseEnd_3629474 : Nat := 1863664684996637899983359

theorem tailTrace_3629474 : CollatzResearch.WordTrace tailWord_3629474 prefixEnd_3629474 1863664684996637899983359 := by
  unfold tailWord_3629474
  simp only [CollatzResearch.WordTrace]
  refine ⟨33094448013260759413587869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88251861368695358436234317 33094448013260759413587869)
  ·
    refine ⟨12410418004972784780095451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33094448013260759413587869 12410418004972784780095451)
    ·
      refine ⟨18615627007459177170143177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12410418004972784780095451 18615627007459177170143177)
      ·
        refine ⟨13961720255594382877607383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18615627007459177170143177 13961720255594382877607383)
        ·
          refine ⟨20942580383391574316411075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13961720255594382877607383 20942580383391574316411075)
          ·
            refine ⟨31413870575087361474616613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20942580383391574316411075 31413870575087361474616613)
            ·
              refine ⟨5890100732828880276490615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31413870575087361474616613 5890100732828880276490615)
              ·
                refine ⟨8835151099243320414735923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890100732828880276490615 8835151099243320414735923)
                ·
                  refine ⟨13252726648864980622103885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835151099243320414735923 13252726648864980622103885)
                  ·
                    refine ⟨4969772493324367733288957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13252726648864980622103885 4969772493324367733288957)
                    ·
                      refine ⟨1863664684996637899983359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4969772493324367733288957 1863664684996637899983359)
                      ·
                        rfl

theorem cell23_3629474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3629474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629474 prefixEnd_3629474 := by exact prefixLift 3629474
  have htrace : WordTrace (prefixWord ++ tailWord_3629474) baseStart_3629474 baseEnd_3629474 := by
    simpa [prefixWord, tailWord_3629474, baseEnd_3629474] using wordTrace_append hprefix tailTrace_3629474
  have hstable : (prefixWord ++ tailWord_3629474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629474).length < 2 ^ (prefixWord ++ tailWord_3629474).sum := by decide
  have hdescent : baseEnd_3629474 < baseStart_3629474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629484 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 1, 3, 2]
def baseStart_3629484 : Nat := 118140960795 + 3629484 * 2 ^ 59
def prefixEnd_3629484 : Nat := 4983230072969 + 3 ^ 40 * 3629484 * 2
def baseEnd_3629484 : Nat := 1863669819803182860858313

theorem tailTrace_3629484 : CollatzResearch.WordTrace tailWord_3629484 prefixEnd_3629484 1863669819803182860858313 := by
  unfold tailWord_3629484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66189078391503404681107753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88252104522004539574810337 66189078391503404681107753)
  ·
    refine ⟨49641808793627553510830815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66189078391503404681107753 49641808793627553510830815)
    ·
      refine ⟨74462713190441330266246223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49641808793627553510830815 74462713190441330266246223)
      ·
        refine ⟨111694069785661995399369335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74462713190441330266246223 111694069785661995399369335)
        ·
          refine ⟨167541104678492993099054003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111694069785661995399369335 167541104678492993099054003)
          ·
            refine ⟨251311657017739489648581005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167541104678492993099054003 251311657017739489648581005)
            ·
              refine ⟨94241871381652308618217877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251311657017739489648581005 94241871381652308618217877)
              ·
                refine ⟨4417587721014951966478963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94241871381652308618217877 4417587721014951966478963)
                ·
                  refine ⟨6626381581522427949718445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417587721014951966478963 6626381581522427949718445)
                  ·
                    refine ⟨2484893093070910481144417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6626381581522427949718445 2484893093070910481144417)
                    ·
                      refine ⟨1863669819803182860858313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484893093070910481144417 1863669819803182860858313)
                      ·
                        rfl

theorem cell23_3629484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_3629484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629484 prefixEnd_3629484 := by exact prefixLift 3629484
  have htrace : WordTrace (prefixWord ++ tailWord_3629484) baseStart_3629484 baseEnd_3629484 := by
    simpa [prefixWord, tailWord_3629484, baseEnd_3629484] using wordTrace_append hprefix tailTrace_3629484
  have hstable : (prefixWord ++ tailWord_3629484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629484).length < 2 ^ (prefixWord ++ tailWord_3629484).sum := by decide
  have hdescent : baseEnd_3629484 < baseStart_3629484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629490 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3629490 : Nat := 118140960795 + 3629490 * 2 ^ 59
def prefixEnd_3629490 : Nat := 4983230072969 + 3 ^ 40 * 3629490 * 2
def baseEnd_3629490 : Nat := 621224300229036612461095

theorem tailTrace_3629490 : CollatzResearch.WordTrace tailWord_3629490 prefixEnd_3629490 621224300229036612461095 := by
  unfold tailWord_3629490
  simp only [CollatzResearch.WordTrace]
  refine ⟨33094593905246268096733481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88252250413990048257955949 33094593905246268096733481)
  ·
    refine ⟨24820945428934701072550111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33094593905246268096733481 24820945428934701072550111)
    ·
      refine ⟨37231418143402051608825167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24820945428934701072550111 37231418143402051608825167)
      ·
        refine ⟨55847127215103077413237751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37231418143402051608825167 55847127215103077413237751)
        ·
          refine ⟨83770690822654616119856627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55847127215103077413237751 83770690822654616119856627)
          ·
            refine ⟨125656036233981924179784941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83770690822654616119856627 125656036233981924179784941)
            ·
              refine ⟨47121013587743221567419353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125656036233981924179784941 47121013587743221567419353)
              ·
                refine ⟨35340760190807416175564515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47121013587743221567419353 35340760190807416175564515)
                ·
                  refine ⟨53011140286211124263346773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35340760190807416175564515 53011140286211124263346773)
                  ·
                    refine ⟨621224300229036612461095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53011140286211124263346773 621224300229036612461095)
                    ·
                      rfl

theorem cell23_3629490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3629490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629490 prefixEnd_3629490 := by exact prefixLift 3629490
  have htrace : WordTrace (prefixWord ++ tailWord_3629490) baseStart_3629490 baseEnd_3629490 := by
    simpa [prefixWord, tailWord_3629490, baseEnd_3629490] using wordTrace_append hprefix tailTrace_3629490
  have hstable : (prefixWord ++ tailWord_3629490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629490).length < 2 ^ (prefixWord ++ tailWord_3629490).sum := by decide
  have hdescent : baseEnd_3629490 < baseStart_3629490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629492 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3629492 : Nat := 118140960795 + 3629492 * 2 ^ 59
def prefixEnd_3629492 : Nat := 4983230072969 + 3 ^ 40 * 3629492 * 2
def baseEnd_3629492 : Nat := 1863673927648418829558277

theorem tailTrace_3629492 : CollatzResearch.WordTrace tailWord_3629492 prefixEnd_3629492 1863673927648418829558277 := by
  unfold tailWord_3629492
  simp only [CollatzResearch.WordTrace]
  refine ⟨66189224283488913364253365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88252299044651884485671153 66189224283488913364253365)
  ·
    refine ⟨6205239776577085627898753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66189224283488913364253365 6205239776577085627898753)
    ·
      refine ⟨4653929832432814220924065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6205239776577085627898753 4653929832432814220924065)
      ·
        refine ⟨3490447374324610665693049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4653929832432814220924065 3490447374324610665693049)
        ·
          refine ⟨2617835530743457999269787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3490447374324610665693049 2617835530743457999269787)
          ·
            refine ⟨3926753296115186998904681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2617835530743457999269787 3926753296115186998904681)
            ·
              refine ⟨2945064972086390249178511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3926753296115186998904681 2945064972086390249178511)
              ·
                refine ⟨4417597458129585373767767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945064972086390249178511 4417597458129585373767767)
                ·
                  refine ⟨6626396187194378060651651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417597458129585373767767 6626396187194378060651651)
                  ·
                    refine ⟨9939594280791567090977477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626396187194378060651651 9939594280791567090977477)
                    ·
                      refine ⟨1863673927648418829558277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9939594280791567090977477 1863673927648418829558277)
                      ·
                        rfl

theorem cell23_3629492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3629492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629492 prefixEnd_3629492 := by exact prefixLift 3629492
  have htrace : WordTrace (prefixWord ++ tailWord_3629492) baseStart_3629492 baseEnd_3629492 := by
    simpa [prefixWord, tailWord_3629492, baseEnd_3629492] using wordTrace_append hprefix tailTrace_3629492
  have hstable : (prefixWord ++ tailWord_3629492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629492).length < 2 ^ (prefixWord ++ tailWord_3629492).sum := by decide
  have hdescent : baseEnd_3629492 < baseStart_3629492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629501 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 1, 3, 2]
def baseStart_3629501 : Nat := 118140960795 + 3629501 * 2 ^ 59
def prefixEnd_3629501 : Nat := 4983230072969 + 3 ^ 40 * 3629501 * 2
def baseEnd_3629501 : Nat := 1863678548974309294345735

theorem tailTrace_3629501 : CollatzResearch.WordTrace tailWord_3629501 prefixEnd_3629501 1863678548974309294345735 := by
  unfold tailWord_3629501
  simp only [CollatzResearch.WordTrace]
  refine ⟨132378776823945221265584357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88252517882630147510389571 132378776823945221265584357)
  ·
    refine ⟨24821020654489728987297067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132378776823945221265584357 24821020654489728987297067)
    ·
      refine ⟨37231530981734593480945601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24821020654489728987297067 37231530981734593480945601)
      ·
        refine ⟨27923648236300945110709201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37231530981734593480945601 27923648236300945110709201)
        ·
          refine ⟨20942736177225708833031901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27923648236300945110709201 20942736177225708833031901)
          ·
            refine ⟨7853526066459640812386963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20942736177225708833031901 7853526066459640812386963)
            ·
              refine ⟨11780289099689461218580445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7853526066459640812386963 11780289099689461218580445)
              ·
                refine ⟨4417608412383547956967667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11780289099689461218580445 4417608412383547956967667)
                ·
                  refine ⟨6626412618575321935451501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417608412383547956967667 6626412618575321935451501)
                  ·
                    refine ⟨2484904731965745725794313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6626412618575321935451501 2484904731965745725794313)
                    ·
                      refine ⟨1863678548974309294345735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484904731965745725794313 1863678548974309294345735)
                      ·
                        rfl

theorem cell23_3629501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_3629501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629501 prefixEnd_3629501 := by exact prefixLift 3629501
  have htrace : WordTrace (prefixWord ++ tailWord_3629501) baseStart_3629501 baseEnd_3629501 := by
    simpa [prefixWord, tailWord_3629501, baseEnd_3629501] using wordTrace_append hprefix tailTrace_3629501
  have hstable : (prefixWord ++ tailWord_3629501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629501).length < 2 ^ (prefixWord ++ tailWord_3629501).sum := by decide
  have hdescent : baseEnd_3629501 < baseStart_3629501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629567 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 2, 5]
def baseStart_3629567 : Nat := 118140960795 + 3629567 * 2 ^ 59
def prefixEnd_3629567 : Nat := 4983230072969 + 3 ^ 40 * 3629567 * 2
def baseEnd_3629567 : Nat := 621237479565835345373477

theorem tailTrace_3629567 : CollatzResearch.WordTrace tailWord_3629567 prefixEnd_3629567 621237479565835345373477 := by
  unfold tailWord_3629567
  simp only [CollatzResearch.WordTrace]
  refine ⟨132381184041706114537486955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88254122694470743024991303 132381184041706114537486955)
  ·
    refine ⟨198571776062559171806230433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132381184041706114537486955 198571776062559171806230433)
    ·
      refine ⟨148928832046919378854672825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198571776062559171806230433 148928832046919378854672825)
      ·
        refine ⟨111696624035189534141004619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148928832046919378854672825 111696624035189534141004619)
        ·
          refine ⟨167544936052784301211506929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111696624035189534141004619 167544936052784301211506929)
          ·
            refine ⟨125658702039588225908630197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167544936052784301211506929 125658702039588225908630197)
            ·
              refine ⟨11780503316211396178934081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125658702039588225908630197 11780503316211396178934081)
              ·
                refine ⟨8835377487158547134200561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11780503316211396178934081 8835377487158547134200561)
                ·
                  refine ⟨6626533115368910350650421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8835377487158547134200561 6626533115368910350650421)
                  ·
                    refine ⟨621237479565835345373477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6626533115368910350650421 621237479565835345373477)
                    ·
                      rfl

theorem cell23_3629567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_3629567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629567 prefixEnd_3629567 := by exact prefixLift 3629567
  have htrace : WordTrace (prefixWord ++ tailWord_3629567) baseStart_3629567 baseEnd_3629567 := by
    simpa [prefixWord, tailWord_3629567, baseEnd_3629567] using wordTrace_append hprefix tailTrace_3629567
  have hstable : (prefixWord ++ tailWord_3629567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629567).length < 2 ^ (prefixWord ++ tailWord_3629567).sum := by decide
  have hdescent : baseEnd_3629567 < baseStart_3629567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629587 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 4]
def baseStart_3629587 : Nat := 118140960795 + 3629587 * 2 ^ 59
def prefixEnd_3629587 : Nat := 4983230072969 + 3 ^ 40 * 3629587 * 2
def baseEnd_3629587 : Nat := 1863722708310595957870339

theorem tailTrace_3629587 : CollatzResearch.WordTrace tailWord_3629587 prefixEnd_3629587 1863722708310595957870339 := by
  unfold tailWord_3629587
  simp only [CollatzResearch.WordTrace]
  refine ⟨132381913501633657953215015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88254609001089105302143343 132381913501633657953215015)
  ·
    refine ⟨198572870252450486929822523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132381913501633657953215015 198572870252450486929822523)
    ·
      refine ⟨297859305378675730394733785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198572870252450486929822523 297859305378675730394733785)
      ·
        refine ⟨223394479034006797796050339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297859305378675730394733785 223394479034006797796050339)
        ·
          refine ⟨335091718551010196694075509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223394479034006797796050339 335091718551010196694075509)
          ·
            refine ⟨31414848614157205940069579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 335091718551010196694075509 31414848614157205940069579)
            ·
              refine ⟨47122272921235808910104369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31414848614157205940069579 47122272921235808910104369)
              ·
                refine ⟨35341704690926856682578277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47122272921235808910104369 35341704690926856682578277)
                ·
                  refine ⟨6626569629548785627983427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35341704690926856682578277 6626569629548785627983427)
                  ·
                    refine ⟨9939854444323178441975141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626569629548785627983427 9939854444323178441975141)
                    ·
                      refine ⟨1863722708310595957870339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9939854444323178441975141 1863722708310595957870339)
                      ·
                        rfl

theorem cell23_3629587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_3629587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629587 prefixEnd_3629587 := by exact prefixLift 3629587
  have htrace : WordTrace (prefixWord ++ tailWord_3629587) baseStart_3629587 baseEnd_3629587 := by
    simpa [prefixWord, tailWord_3629587, baseEnd_3629587] using wordTrace_append hprefix tailTrace_3629587
  have hstable : (prefixWord ++ tailWord_3629587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629587).length < 2 ^ (prefixWord ++ tailWord_3629587).sum := by decide
  have hdescent : baseEnd_3629587 < baseStart_3629587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629624 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 2, 2, 3]
def baseStart_3629624 : Nat := 118140960795 + 3629624 * 2 ^ 59
def prefixEnd_3629624 : Nat := 4983230072969 + 3 ^ 40 * 3629624 * 2
def baseEnd_3629624 : Nat := 1863741707094812313107669

theorem tailTrace_3629624 : CollatzResearch.WordTrace tailWord_3629624 prefixEnd_3629624 1863741707094812313107669 := by
  unfold tailWord_3629624
  simp only [CollatzResearch.WordTrace]
  refine ⟨66191631501249806636155963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88255508668333075514874617 66191631501249806636155963)
  ·
    refine ⟨99287447251874709954233945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66191631501249806636155963 99287447251874709954233945)
    ·
      refine ⟨74465585438906032465675459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99287447251874709954233945 74465585438906032465675459)
      ·
        refine ⟨111698378158359048698513189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74465585438906032465675459 111698378158359048698513189)
        ·
          refine ⟨20943445904692321630971223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111698378158359048698513189 20943445904692321630971223)
          ·
            refine ⟨31415168857038482446456835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20943445904692321630971223 31415168857038482446456835)
            ·
              refine ⟨47122753285557723669685253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31415168857038482446456835 47122753285557723669685253)
              ·
                refine ⟨8835516241042073188065985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47122753285557723669685253 8835516241042073188065985)
                ·
                  refine ⟨6626637180781554891049489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8835516241042073188065985 6626637180781554891049489)
                  ·
                    refine ⟨4969977885586166168287117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6626637180781554891049489 4969977885586166168287117)
                    ·
                      refine ⟨1863741707094812313107669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4969977885586166168287117 1863741707094812313107669)
                      ·
                        rfl

theorem cell23_3629624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_3629624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629624 prefixEnd_3629624 := by exact prefixLift 3629624
  have htrace : WordTrace (prefixWord ++ tailWord_3629624) baseStart_3629624 baseEnd_3629624 := by
    simpa [prefixWord, tailWord_3629624, baseEnd_3629624] using wordTrace_append hprefix tailTrace_3629624
  have hstable : (prefixWord ++ tailWord_3629624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629624).length < 2 ^ (prefixWord ++ tailWord_3629624).sum := by decide
  have hdescent : baseEnd_3629624 < baseStart_3629624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629631 : List Nat := [1, 1, 2, 2, 3, 2, 3, 4, 1, 4]
def baseStart_3629631 : Nat := 118140960795 + 3629631 * 2 ^ 59
def prefixEnd_3629631 : Nat := 4983230072969 + 3 ^ 40 * 3629631 * 2
def baseEnd_3629631 : Nat := 621248433819797928573379

theorem tailTrace_3629631 : CollatzResearch.WordTrace tailWord_3629631 prefixEnd_3629631 621248433819797928573379 := by
  unfold tailWord_3629631
  simp only [CollatzResearch.WordTrace]
  refine ⟨132383518313474253467816747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88255678875649502311877831 132383518313474253467816747)
  ·
    refine ⟨198575277470211380201725121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132383518313474253467816747 198575277470211380201725121)
    ·
      refine ⟨148931458102658535151293841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198575277470211380201725121 148931458102658535151293841)
      ·
        refine ⟨111698593576993901363470381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148931458102658535151293841 111698593576993901363470381)
        ·
          refine ⟨41886972591372713011301393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111698593576993901363470381 41886972591372713011301393)
          ·
            refine ⟨31415229443529534758476045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41886972591372713011301393 31415229443529534758476045)
            ·
              refine ⟨11780711041323575534428517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31415229443529534758476045 11780711041323575534428517)
              ·
                refine ⟨2208883320248170412705347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11780711041323575534428517 2208883320248170412705347)
                ·
                  refine ⟨3313324980372255619058021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2208883320248170412705347 3313324980372255619058021)
                  ·
                    refine ⟨621248433819797928573379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313324980372255619058021 621248433819797928573379)
                    ·
                      rfl

theorem cell23_3629631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 4].length) (baseStart_3629631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629631 prefixEnd_3629631 := by exact prefixLift 3629631
  have htrace : WordTrace (prefixWord ++ tailWord_3629631) baseStart_3629631 baseEnd_3629631 := by
    simpa [prefixWord, tailWord_3629631, baseEnd_3629631] using wordTrace_append hprefix tailTrace_3629631
  have hstable : (prefixWord ++ tailWord_3629631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629631).length < 2 ^ (prefixWord ++ tailWord_3629631).sum := by decide
  have hdescent : baseEnd_3629631 < baseStart_3629631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629638 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_3629638 : Nat := 118140960795 + 3629638 * 2 ^ 59
def prefixEnd_3629638 : Nat := 4983230072969 + 3 ^ 40 * 3629638 * 2
def baseEnd_3629638 : Nat := 1863748895823975258332605

theorem tailTrace_3629638 : CollatzResearch.WordTrace tailWord_3629638 prefixEnd_3629638 1863748895823975258332605 := by
  unfold tailWord_3629638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4136992925764027926978799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88255849082965929108881045 4136992925764027926978799)
  ·
    refine ⟨6205489388646041890468199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4136992925764027926978799 6205489388646041890468199)
    ·
      refine ⟨9308234082969062835702299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6205489388646041890468199 9308234082969062835702299)
      ·
        refine ⟨13962351124453594253553449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9308234082969062835702299 13962351124453594253553449)
        ·
          refine ⟨10471763343340195690165087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13962351124453594253553449 10471763343340195690165087)
          ·
            refine ⟨15707645015010293535247631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10471763343340195690165087 15707645015010293535247631)
            ·
              refine ⟨23561467522515440302871447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15707645015010293535247631 23561467522515440302871447)
              ·
                refine ⟨35342201283773160454307171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23561467522515440302871447 35342201283773160454307171)
                ·
                  refine ⟨53013301925659740681460757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35342201283773160454307171 53013301925659740681460757)
                  ·
                    refine ⟨2484998527765300344443473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53013301925659740681460757 2484998527765300344443473)
                    ·
                      refine ⟨1863748895823975258332605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2484998527765300344443473 1863748895823975258332605)
                      ·
                        rfl

theorem cell23_3629638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_3629638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629638 prefixEnd_3629638 := by exact prefixLift 3629638
  have htrace : WordTrace (prefixWord ++ tailWord_3629638) baseStart_3629638 baseEnd_3629638 := by
    simpa [prefixWord, tailWord_3629638, baseEnd_3629638] using wordTrace_append hprefix tailTrace_3629638
  have hstable : (prefixWord ++ tailWord_3629638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629638).length < 2 ^ (prefixWord ++ tailWord_3629638).sum := by decide
  have hdescent : baseEnd_3629638 < baseStart_3629638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629687 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 3, 6]
def baseStart_3629687 : Nat := 118140960795 + 3629687 * 2 ^ 59
def prefixEnd_3629687 : Nat := 4983230072969 + 3 ^ 40 * 3629687 * 2
def baseEnd_3629687 : Nat := 621258018792015188873293

theorem tailTrace_3629687 : CollatzResearch.WordTrace tailWord_3629687 prefixEnd_3629687 621258018792015188873293 := by
  unfold tailWord_3629687
  simp only [CollatzResearch.WordTrace]
  refine ⟨132385560801271375031855315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88257040534180916687903543 132385560801271375031855315)
  ·
    refine ⟨198578341201907062547782973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132385560801271375031855315 198578341201907062547782973)
    ·
      refine ⟨74466877950715148455418615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198578341201907062547782973 74466877950715148455418615)
      ·
        refine ⟨111700316926072722683127923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74466877950715148455418615 111700316926072722683127923)
        ·
          refine ⟨167550475389109084024691885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111700316926072722683127923 167550475389109084024691885)
          ·
            refine ⟨62831428270915906509259457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167550475389109084024691885 62831428270915906509259457)
            ·
              refine ⟨47123571203186929881944593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62831428270915906509259457 47123571203186929881944593)
              ·
                refine ⟨35342678402390197411458445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47123571203186929881944593 35342678402390197411458445)
                ·
                  refine ⟨13253504400896324029296917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35342678402390197411458445 13253504400896324029296917)
                  ·
                    refine ⟨621258018792015188873293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13253504400896324029296917 621258018792015188873293)
                    ·
                      rfl

theorem cell23_3629687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_3629687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629687 prefixEnd_3629687 := by exact prefixLift 3629687
  have htrace : WordTrace (prefixWord ++ tailWord_3629687) baseStart_3629687 baseEnd_3629687 := by
    simpa [prefixWord, tailWord_3629687, baseEnd_3629687] using wordTrace_append hprefix tailTrace_3629687
  have hstable : (prefixWord ++ tailWord_3629687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629687).length < 2 ^ (prefixWord ++ tailWord_3629687).sum := by decide
  have hdescent : baseEnd_3629687 < baseStart_3629687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629737 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_3629737 : Nat := 118140960795 + 3629737 * 2 ^ 59
def prefixEnd_3629737 : Nat := 4983230072969 + 3 ^ 40 * 3629737 * 2
def baseEnd_3629737 : Nat := 1863799730408770370994649

theorem tailTrace_3629737 : CollatzResearch.WordTrace tailWord_3629737 prefixEnd_3629737 1863799730408770370994649 := by
  unfold tailWord_3629737
  simp only [CollatzResearch.WordTrace]
  refine ⟨132387384451090233571175465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88258256300726822380783643 132387384451090233571175465)
  ·
    refine ⟨99290538338317675178381599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132387384451090233571175465 99290538338317675178381599)
    ·
      refine ⟨148935807507476512767572399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99290538338317675178381599 148935807507476512767572399)
      ·
        refine ⟨223403711261214769151358599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148935807507476512767572399 223403711261214769151358599)
        ·
          refine ⟨335105566891822153727037899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223403711261214769151358599 335105566891822153727037899)
          ·
            refine ⟨502658350337733230590556849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335105566891822153727037899 502658350337733230590556849)
            ·
              refine ⟨376993762753299922942917637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502658350337733230590556849 376993762753299922942917637)
              ·
                refine ⟨70686330516243735551797057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 376993762753299922942917637 70686330516243735551797057)
                ·
                  refine ⟨53014747887182801663847793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70686330516243735551797057 53014747887182801663847793)
                  ·
                    refine ⟨39761060915387101247885845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53014747887182801663847793 39761060915387101247885845)
                    ·
                      refine ⟨1863799730408770370994649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39761060915387101247885845 1863799730408770370994649)
                      ·
                        rfl

theorem cell23_3629737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_3629737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629737 prefixEnd_3629737 := by exact prefixLift 3629737
  have htrace : WordTrace (prefixWord ++ tailWord_3629737) baseStart_3629737 baseEnd_3629737 := by
    simpa [prefixWord, tailWord_3629737, baseEnd_3629737] using wordTrace_append hprefix tailTrace_3629737
  have hstable : (prefixWord ++ tailWord_3629737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629737).length < 2 ^ (prefixWord ++ tailWord_3629737).sum := by decide
  have hdescent : baseEnd_3629737 < baseStart_3629737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629778 : List Nat := [3, 2, 2, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3629778 : Nat := 118140960795 + 3629778 * 2 ^ 59
def prefixEnd_3629778 : Nat := 4983230072969 + 3 ^ 40 * 3629778 * 2
def baseEnd_3629778 : Nat := 1863820783115604710581961

theorem tailTrace_3629778 : CollatzResearch.WordTrace tailWord_3629778 prefixEnd_3629778 1863820783115604710581961 := by
  unfold tailWord_3629778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33097219960985424393354497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88259253229294465048945325 33097219960985424393354497)
  ·
    refine ⟨24822914970739068295015873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33097219960985424393354497 24822914970739068295015873)
    ·
      refine ⟨18617186228054301221261905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24822914970739068295015873 18617186228054301221261905)
      ·
        refine ⟨13962889671040725915946429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18617186228054301221261905 13962889671040725915946429)
        ·
          refine ⟨5236083626640272218479911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13962889671040725915946429 5236083626640272218479911)
          ·
            refine ⟨7854125439960408327719867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236083626640272218479911 7854125439960408327719867)
            ·
              refine ⟨11781188159940612491579801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854125439960408327719867 11781188159940612491579801)
              ·
                refine ⟨8835891119955459368684851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11781188159940612491579801 8835891119955459368684851)
                ·
                  refine ⟨13253836679933189053027277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835891119955459368684851 13253836679933189053027277)
                  ·
                    refine ⟨4970188754974945894885229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13253836679933189053027277 4970188754974945894885229)
                    ·
                      refine ⟨1863820783115604710581961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4970188754974945894885229 1863820783115604710581961)
                      ·
                        rfl

theorem cell23_3629778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3629778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629778 prefixEnd_3629778 := by exact prefixLift 3629778
  have htrace : WordTrace (prefixWord ++ tailWord_3629778) baseStart_3629778 baseEnd_3629778 := by
    simpa [prefixWord, tailWord_3629778, baseEnd_3629778] using wordTrace_append hprefix tailTrace_3629778
  have hstable : (prefixWord ++ tailWord_3629778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629778).length < 2 ^ (prefixWord ++ tailWord_3629778).sum := by decide
  have hdescent : baseEnd_3629778 < baseStart_3629778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629795 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3629795 : Nat := 118140960795 + 3629795 * 2 ^ 59
def prefixEnd_3629795 : Nat := 4983230072969 + 3 ^ 40 * 3629795 * 2
def baseEnd_3629795 : Nat := 1863829512286731144069383

theorem tailTrace_3629795 : CollatzResearch.WordTrace tailWord_3629795 prefixEnd_3629795 1863829512286731144069383 := by
  unfold tailWord_3629795
  simp only [CollatzResearch.WordTrace]
  refine ⟨132389499884880109476786839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88259666589920072984524559 132389499884880109476786839)
  ·
    refine ⟨198584249827320164215180259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132389499884880109476786839 198584249827320164215180259)
    ·
      refine ⟨297876374740980246322770389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198584249827320164215180259 297876374740980246322770389)
      ·
        refine ⟨6981477532991724523189931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 297876374740980246322770389 6981477532991724523189931)
        ·
          refine ⟨10472216299487586784784897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6981477532991724523189931 10472216299487586784784897)
          ·
            refine ⟨7854162224615690088588673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10472216299487586784784897 7854162224615690088588673)
            ·
              refine ⟨5890621668461767566441505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7854162224615690088588673 5890621668461767566441505)
              ·
                refine ⟨4417966251346325674831129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890621668461767566441505 4417966251346325674831129)
                ·
                  refine ⟨3313474688509744256123347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4417966251346325674831129 3313474688509744256123347)
                  ·
                    refine ⟨4970212032764616384185021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3313474688509744256123347 4970212032764616384185021)
                    ·
                      refine ⟨1863829512286731144069383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4970212032764616384185021 1863829512286731144069383)
                      ·
                        rfl

theorem cell23_3629795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3629795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629795 prefixEnd_3629795 := by exact prefixLift 3629795
  have htrace : WordTrace (prefixWord ++ tailWord_3629795) baseStart_3629795 baseEnd_3629795 := by
    simpa [prefixWord, tailWord_3629795, baseEnd_3629795] using wordTrace_append hprefix tailTrace_3629795
  have hstable : (prefixWord ++ tailWord_3629795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629795).length < 2 ^ (prefixWord ++ tailWord_3629795).sum := by decide
  have hdescent : baseEnd_3629795 < baseStart_3629795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629812 : List Nat := [2, 6, 1, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3629812 : Nat := 118140960795 + 3629812 * 2 ^ 59
def prefixEnd_3629812 : Nat := 4983230072969 + 3 ^ 40 * 3629812 * 2
def baseEnd_3629812 : Nat := 1863838241457857577556805

theorem tailTrace_3629812 : CollatzResearch.WordTrace tailWord_3629812 prefixEnd_3629812 1863838241457857577556805 := by
  unfold tailWord_3629812
  simp only [CollatzResearch.WordTrace]
  refine ⟨66195059962909260690077845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88260079950545680920103793 66195059962909260690077845)
  ·
    refine ⟨3102893435761371594847399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66195059962909260690077845 3102893435761371594847399)
    ·
      refine ⟨4654340153642057392271099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3102893435761371594847399 4654340153642057392271099)
      ·
        refine ⟨6981510230463086088406649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4654340153642057392271099 6981510230463086088406649)
        ·
          refine ⟨5236132672847314566304987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6981510230463086088406649 5236132672847314566304987)
          ·
            refine ⟨7854199009270971849457481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236132672847314566304987 7854199009270971849457481)
            ·
              refine ⟨5890649256953228887093111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7854199009270971849457481 5890649256953228887093111)
              ·
                refine ⟨8835973885429843330639667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890649256953228887093111 8835973885429843330639667)
                ·
                  refine ⟨13253960828144764995959501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835973885429843330639667 13253960828144764995959501)
                  ·
                    refine ⟨4970235310554286873484813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13253960828144764995959501 4970235310554286873484813)
                    ·
                      refine ⟨1863838241457857577556805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4970235310554286873484813 1863838241457857577556805)
                      ·
                        rfl

theorem cell23_3629812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3629812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629812 prefixEnd_3629812 := by exact prefixLift 3629812
  have htrace : WordTrace (prefixWord ++ tailWord_3629812) baseStart_3629812 baseEnd_3629812 := by
    simpa [prefixWord, tailWord_3629812, baseEnd_3629812] using wordTrace_append hprefix tailTrace_3629812
  have hstable : (prefixWord ++ tailWord_3629812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629812).length < 2 ^ (prefixWord ++ tailWord_3629812).sum := by decide
  have hdescent : baseEnd_3629812 < baseStart_3629812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629841 : List Nat := [1, 2, 2, 1, 1, 3, 3, 5, 5]
def baseStart_3629841 : Nat := 118140960795 + 3629841 * 2 ^ 59
def prefixEnd_3629841 : Nat := 4983230072969 + 3 ^ 40 * 3629841 * 2
def baseEnd_3629841 : Nat := 207094792488537551566019

theorem tailTrace_3629841 : CollatzResearch.WordTrace tailWord_3629841 prefixEnd_3629841 207094792488537551566019 := by
  unfold tailWord_3629841
  simp only [CollatzResearch.WordTrace]
  refine ⟨132391177642713459332961377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88260785095142306221974251 132391177642713459332961377)
  ·
    refine ⟨99293383232035094499721033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132391177642713459332961377 99293383232035094499721033)
    ·
      refine ⟨74470037424026320874790775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99293383232035094499721033 74470037424026320874790775)
      ·
        refine ⟨111705056136039481312186163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74470037424026320874790775 111705056136039481312186163)
        ·
          refine ⟨167557584204059221968279245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111705056136039481312186163 167557584204059221968279245)
          ·
            refine ⟨62834094076522208238104717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167557584204059221968279245 62834094076522208238104717)
            ·
              refine ⟨23562785278695828089289269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62834094076522208238104717 23562785278695828089289269)
              ·
                refine ⟨2209011119877733883370869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23562785278695828089289269 2209011119877733883370869)
                ·
                  refine ⟨207094792488537551566019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209011119877733883370869 207094792488537551566019)
                  ·
                    rfl

theorem cell23_3629841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 5].length) (baseStart_3629841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629841 prefixEnd_3629841 := by exact prefixLift 3629841
  have htrace : WordTrace (prefixWord ++ tailWord_3629841) baseStart_3629841 baseEnd_3629841 := by
    simpa [prefixWord, tailWord_3629841, baseEnd_3629841] using wordTrace_append hprefix tailTrace_3629841
  have hstable : (prefixWord ++ tailWord_3629841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629841).length < 2 ^ (prefixWord ++ tailWord_3629841).sum := by decide
  have hdescent : baseEnd_3629841 < baseStart_3629841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629852 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_3629852 : Nat := 118140960795 + 3629852 * 2 ^ 59
def prefixEnd_3629852 : Nat := 4983230072969 + 3 ^ 40 * 3629852 * 2
def baseEnd_3629852 : Nat := 1863858780684037421056621

theorem tailTrace_3629852 : CollatzResearch.WordTrace tailWord_3629852 prefixEnd_3629852 1863858780684037421056621 := by
  unfold tailWord_3629852
  simp only [CollatzResearch.WordTrace]
  refine ⟨66195789422836804105805905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88261052563782405474407873 66195789422836804105805905)
  ·
    refine ⟨49646842067127603079354429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66195789422836804105805905 49646842067127603079354429)
    ·
      refine ⟨18617565775172851154757911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49646842067127603079354429 18617565775172851154757911)
      ·
        refine ⟨27926348662759276732136867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18617565775172851154757911 27926348662759276732136867)
        ·
          refine ⟨41889522994138915098205301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27926348662759276732136867 41889522994138915098205301)
          ·
            refine ⟨3927142780700523290456747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41889522994138915098205301 3927142780700523290456747)
            ·
              refine ⟨5890714171050784935685121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927142780700523290456747 5890714171050784935685121)
              ·
                refine ⟨4418035628288088701763841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890714171050784935685121 4418035628288088701763841)
                ·
                  refine ⟨3313526721216066526322881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418035628288088701763841 3313526721216066526322881)
                  ·
                    refine ⟨2485145040912049894742161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3313526721216066526322881 2485145040912049894742161)
                    ·
                      refine ⟨1863858780684037421056621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485145040912049894742161 1863858780684037421056621)
                      ·
                        rfl

theorem cell23_3629852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_3629852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629852 prefixEnd_3629852 := by exact prefixLift 3629852
  have htrace : WordTrace (prefixWord ++ tailWord_3629852) baseStart_3629852 baseEnd_3629852 := by
    simpa [prefixWord, tailWord_3629852, baseEnd_3629852] using wordTrace_append hprefix tailTrace_3629852
  have hstable : (prefixWord ++ tailWord_3629852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629852).length < 2 ^ (prefixWord ++ tailWord_3629852).sum := by decide
  have hdescent : baseEnd_3629852 < baseStart_3629852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629858 : List Nat := [3, 3, 1, 1, 2, 2, 2, 4, 5]
def baseStart_3629858 : Nat := 118140960795 + 3629858 * 2 ^ 59
def prefixEnd_3629858 : Nat := 4983230072969 + 3 ^ 40 * 3629858 * 2
def baseEnd_3629858 : Nat := 207095762396440488620177

theorem tailTrace_3629858 : CollatzResearch.WordTrace tailWord_3629858 prefixEnd_3629858 207095762396440488620177 := by
  unfold tailWord_3629858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33097949420912967809082557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88261198455767914157553485 33097949420912967809082557)
  ·
    refine ⟨12411731032842362928405959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33097949420912967809082557 12411731032842362928405959)
    ·
      refine ⟨18617596549263544392608939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12411731032842362928405959 18617596549263544392608939)
      ·
        refine ⟨27926394823895316588913409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18617596549263544392608939 27926394823895316588913409)
        ·
          refine ⟨20944796117921487441685057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27926394823895316588913409 20944796117921487441685057)
          ·
            refine ⟨15708597088441115581263793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20944796117921487441685057 15708597088441115581263793)
            ·
              refine ⟨11781447816330836685947845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15708597088441115581263793 11781447816330836685947845)
              ·
                refine ⟨2209021465562031878615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11781447816330836685947845 2209021465562031878615221)
                ·
                  refine ⟨207095762396440488620177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209021465562031878615221 207095762396440488620177)
                  ·
                    rfl

theorem cell23_3629858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_3629858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629858 prefixEnd_3629858 := by exact prefixLift 3629858
  have htrace : WordTrace (prefixWord ++ tailWord_3629858) baseStart_3629858 baseEnd_3629858 := by
    simpa [prefixWord, tailWord_3629858, baseEnd_3629858] using wordTrace_append hprefix tailTrace_3629858
  have hstable : (prefixWord ++ tailWord_3629858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629858).length < 2 ^ (prefixWord ++ tailWord_3629858).sum := by decide
  have hdescent : baseEnd_3629858 < baseStart_3629858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629869 : List Nat := [1, 5, 3, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3629869 : Nat := 118140960795 + 3629869 * 2 ^ 59
def prefixEnd_3629869 : Nat := 4983230072969 + 3 ^ 40 * 3629869 * 2
def baseEnd_3629869 : Nat := 1863867509855163854544043

theorem tailTrace_3629869 : CollatzResearch.WordTrace tailWord_3629869 prefixEnd_3629869 1863867509855163854544043 := by
  unfold tailWord_3629869
  simp only [CollatzResearch.WordTrace]
  refine ⟨132392198886612020114980661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88261465924408013409987107 132392198886612020114980661)
  ·
    refine ⟨12411768645619876885779437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132392198886612020114980661 12411768645619876885779437)
    ·
      refine ⟨4654413242107453832167289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12411768645619876885779437 4654413242107453832167289)
      ·
        refine ⟨3490809931580590374125467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4654413242107453832167289 3490809931580590374125467)
        ·
          refine ⟨5236214897370885561188201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490809931580590374125467 5236214897370885561188201)
          ·
            refine ⟨3927161173028164170891151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5236214897370885561188201 3927161173028164170891151)
            ·
              refine ⟨5890741759542246256336727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927161173028164170891151 5890741759542246256336727)
              ·
                refine ⟨8836112639313369384505091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890741759542246256336727 8836112639313369384505091)
                ·
                  refine ⟨13254168958970054076757637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8836112639313369384505091 13254168958970054076757637)
                  ·
                    refine ⟨2485156679806885139392057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13254168958970054076757637 2485156679806885139392057)
                    ·
                      refine ⟨1863867509855163854544043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485156679806885139392057 1863867509855163854544043)
                      ·
                        rfl

theorem cell23_3629869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3629869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629869 prefixEnd_3629869 := by exact prefixLift 3629869
  have htrace : WordTrace (prefixWord ++ tailWord_3629869) baseStart_3629869 baseEnd_3629869 := by
    simpa [prefixWord, tailWord_3629869, baseEnd_3629869] using wordTrace_append hprefix tailTrace_3629869
  have hstable : (prefixWord ++ tailWord_3629869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629869).length < 2 ^ (prefixWord ++ tailWord_3629869).sum := by decide
  have hdescent : baseEnd_3629869 < baseStart_3629869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629884 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_3629884 : Nat := 118140960795 + 3629884 * 2 ^ 59
def prefixEnd_3629884 : Nat := 4983230072969 + 3 ^ 40 * 3629884 * 2
def baseEnd_3629884 : Nat := 621291737354993765285491

theorem tailTrace_3629884 : CollatzResearch.WordTrace tailWord_3629884 prefixEnd_3629884 621291737354993765285491 := by
  unfold tailWord_3629884
  simp only [CollatzResearch.WordTrace]
  refine ⟨66196372990778838838388353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88261830654371785117851137 66196372990778838838388353)
  ·
    refine ⟨49647279743084129128791265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66196372990778838838388353 49647279743084129128791265)
    ·
      refine ⟨37235459807313096846593449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49647279743084129128791265 37235459807313096846593449)
      ·
        refine ⟨27926594855484822634945087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37235459807313096846593449 27926594855484822634945087)
        ·
          refine ⟨41889892283227233952417631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27926594855484822634945087 41889892283227233952417631)
          ·
            refine ⟨62834838424840850928626447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41889892283227233952417631 62834838424840850928626447)
            ·
              refine ⟨94252257637261276392939671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62834838424840850928626447 94252257637261276392939671)
              ·
                refine ⟨141378386455891914589409507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94252257637261276392939671 141378386455891914589409507)
                ·
                  refine ⟨212067579683837871884114261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141378386455891914589409507 212067579683837871884114261)
                  ·
                    refine ⟨621291737354993765285491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 212067579683837871884114261 621291737354993765285491)
                    ·
                      rfl

theorem cell23_3629884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_3629884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629884 prefixEnd_3629884 := by exact prefixLift 3629884
  have htrace : WordTrace (prefixWord ++ tailWord_3629884) baseStart_3629884 baseEnd_3629884 := by
    simpa [prefixWord, tailWord_3629884, baseEnd_3629884] using wordTrace_append hprefix tailTrace_3629884
  have hstable : (prefixWord ++ tailWord_3629884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629884).length < 2 ^ (prefixWord ++ tailWord_3629884).sum := by decide
  have hdescent : baseEnd_3629884 < baseStart_3629884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629891 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 4]
def baseStart_3629891 : Nat := 118140960795 + 3629891 * 2 ^ 59
def prefixEnd_3629891 : Nat := 4983230072969 + 3 ^ 40 * 3629891 * 2
def baseEnd_3629891 : Nat := 1863878806429562768468941

theorem tailTrace_3629891 : CollatzResearch.WordTrace tailWord_3629891 prefixEnd_3629891 1863878806429562768468941 := by
  unfold tailWord_3629891
  simp only [CollatzResearch.WordTrace]
  refine ⟨132393001292532317872281527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88262000861688211914854351 132393001292532317872281527)
  ·
    refine ⟨198589501938798476808422291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132393001292532317872281527 198589501938798476808422291)
    ·
      refine ⟨297884252908197715212633437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198589501938798476808422291 297884252908197715212633437)
      ·
        refine ⟨111706594840574143204737539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297884252908197715212633437 111706594840574143204737539)
        ·
          refine ⟨167559892260861214807106309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111706594840574143204737539 167559892260861214807106309)
          ·
            refine ⟨31417479798911477776332433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167559892260861214807106309 31417479798911477776332433)
            ·
              refine ⟨23563109849183608332249325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31417479798911477776332433 23563109849183608332249325)
              ·
                refine ⟨8836166193443853124593497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23563109849183608332249325 8836166193443853124593497)
                ·
                  refine ⟨6627124645082889843445123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8836166193443853124593497 6627124645082889843445123)
                  ·
                    refine ⟨9940686967624334765167685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6627124645082889843445123 9940686967624334765167685)
                    ·
                      refine ⟨1863878806429562768468941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9940686967624334765167685 1863878806429562768468941)
                      ·
                        rfl

theorem cell23_3629891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_3629891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629891 prefixEnd_3629891 := by exact prefixLift 3629891
  have htrace : WordTrace (prefixWord ++ tailWord_3629891) baseStart_3629891 baseEnd_3629891 := by
    simpa [prefixWord, tailWord_3629891, baseEnd_3629891] using wordTrace_append hprefix tailTrace_3629891
  have hstable : (prefixWord ++ tailWord_3629891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629891).length < 2 ^ (prefixWord ++ tailWord_3629891).sum := by decide
  have hdescent : baseEnd_3629891 < baseStart_3629891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3629904 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6]
def baseStart_3629904 : Nat := 118140960795 + 3629904 * 2 ^ 59
def prefixEnd_3629904 : Nat := 4983230072969 + 3 ^ 40 * 3629904 * 2
def baseEnd_3629904 : Nat := 1863885481678071217606381

theorem tailTrace_3629904 : CollatzResearch.WordTrace tailWord_3629904 prefixEnd_3629904 1863885481678071217606381 := by
  unfold tailWord_3629904
  simp only [CollatzResearch.WordTrace]
  refine ⟨66196737720742610546252383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88262316960990147395003177 66196737720742610546252383)
  ·
    refine ⟨99295106581113915819378575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66196737720742610546252383 99295106581113915819378575)
    ·
      refine ⟨148942659871670873729067863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99295106581113915819378575 148942659871670873729067863)
      ·
        refine ⟨223413989807506310593601795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148942659871670873729067863 223413989807506310593601795)
        ·
          refine ⟨335120984711259465890402693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223413989807506310593601795 335120984711259465890402693)
          ·
            refine ⟨62835184633361149854450505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335120984711259465890402693 62835184633361149854450505)
            ·
              refine ⟨47126388475020862390837879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62835184633361149854450505 47126388475020862390837879)
              ·
                refine ⟨70689582712531293586256819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47126388475020862390837879 70689582712531293586256819)
                ·
                  refine ⟨106034374068796940379385229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70689582712531293586256819 106034374068796940379385229)
                  ·
                    refine ⟨39762890275798852642269461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106034374068796940379385229 39762890275798852642269461)
                    ·
                      refine ⟨1863885481678071217606381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39762890275798852642269461 1863885481678071217606381)
                      ·
                        rfl

theorem cell23_3629904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_3629904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3629904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3629904 prefixEnd_3629904 := by exact prefixLift 3629904
  have htrace : WordTrace (prefixWord ++ tailWord_3629904) baseStart_3629904 baseEnd_3629904 := by
    simpa [prefixWord, tailWord_3629904, baseEnd_3629904] using wordTrace_append hprefix tailTrace_3629904
  have hstable : (prefixWord ++ tailWord_3629904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3629904).length < 2 ^ (prefixWord ++ tailWord_3629904).sum := by decide
  have hdescent : baseEnd_3629904 < baseStart_3629904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3629904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630042 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 2, 4]
def baseStart_3630042 : Nat := 118140960795 + 3630042 * 2 ^ 59
def prefixEnd_3630042 : Nat := 4983230072969 + 3 ^ 40 * 3630042 * 2
def baseEnd_3630042 : Nat := 621318780669463892560249

theorem tailTrace_3630042 : CollatzResearch.WordTrace tailWord_3630042 prefixEnd_3630042 621318780669463892560249 := by
  unfold tailWord_3630042
  simp only [CollatzResearch.WordTrace]
  refine ⟨33099627178746317665257095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88265672476656847107352253 33099627178746317665257095)
  ·
    refine ⟨49649440768119476497885643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33099627178746317665257095 49649440768119476497885643)
    ·
      refine ⟨74474161152179214746828465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49649440768119476497885643 74474161152179214746828465)
      ·
        refine ⟨55855620864134411060121349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74474161152179214746828465 55855620864134411060121349)
        ·
          refine ⟨10472928912025202073772753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55855620864134411060121349 10472928912025202073772753)
          ·
            refine ⟨7854696684018901555329565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10472928912025202073772753 7854696684018901555329565)
            ·
              refine ⟨2945511256507088083248587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7854696684018901555329565 2945511256507088083248587)
              ·
                refine ⟨4418266884760632124872881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945511256507088083248587 4418266884760632124872881)
                ·
                  refine ⟨3313700163570474093654661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4418266884760632124872881 3313700163570474093654661)
                  ·
                    refine ⟨621318780669463892560249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313700163570474093654661 621318780669463892560249)
                    ·
                      rfl

theorem cell23_3630042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_3630042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630042 prefixEnd_3630042 := by exact prefixLift 3630042
  have htrace : WordTrace (prefixWord ++ tailWord_3630042) baseStart_3630042 baseEnd_3630042 := by
    simpa [prefixWord, tailWord_3630042, baseEnd_3630042] using wordTrace_append hprefix tailTrace_3630042
  have hstable : (prefixWord ++ tailWord_3630042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630042).length < 2 ^ (prefixWord ++ tailWord_3630042).sum := by decide
  have hdescent : baseEnd_3630042 < baseStart_3630042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630045 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3630045 : Nat := 118140960795 + 3630045 * 2 ^ 59
def prefixEnd_3630045 : Nat := 4983230072969 + 3 ^ 40 * 3630045 * 2
def baseEnd_3630045 : Nat := 1863957882450355165943233

theorem tailTrace_3630045 : CollatzResearch.WordTrace tailWord_3630045 prefixEnd_3630045 1863957882450355165943233 := by
  unfold tailWord_3630045
  simp only [CollatzResearch.WordTrace]
  refine ⟨132398618133974402173387589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88265745422649601448925059 132398618133974402173387589)
  ·
    refine ⟨24824740900120200407510173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132398618133974402173387589 24824740900120200407510173)
    ·
      refine ⟨9309277837545075152816315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24824740900120200407510173 9309277837545075152816315)
      ·
        refine ⟨13963916756317612729224473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9309277837545075152816315 13963916756317612729224473)
        ·
          refine ⟨10472937567238209546918355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13963916756317612729224473 10472937567238209546918355)
          ·
            refine ⟨15709406350857314320377533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472937567238209546918355 15709406350857314320377533)
            ·
              refine ⟨5891027381571492870141575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15709406350857314320377533 5891027381571492870141575)
              ·
                refine ⟨8836541072357239305212363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891027381571492870141575 8836541072357239305212363)
                ·
                  refine ⟨13254811608535858957818545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8836541072357239305212363 13254811608535858957818545)
                  ·
                    refine ⟨9941108706401894218363909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13254811608535858957818545 9941108706401894218363909)
                    ·
                      refine ⟨1863957882450355165943233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9941108706401894218363909 1863957882450355165943233)
                      ·
                        rfl

theorem cell23_3630045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3630045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630045 prefixEnd_3630045 := by exact prefixLift 3630045
  have htrace : WordTrace (prefixWord ++ tailWord_3630045) baseStart_3630045 baseEnd_3630045 := by
    simpa [prefixWord, tailWord_3630045, baseEnd_3630045] using wordTrace_append hprefix tailTrace_3630045
  have hstable : (prefixWord ++ tailWord_3630045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630045).length < 2 ^ (prefixWord ++ tailWord_3630045).sum := by decide
  have hdescent : baseEnd_3630045 < baseStart_3630045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630055 : List Nat := [1, 1, 5, 2, 2, 3, 2, 7]
def baseStart_3630055 : Nat := 118140960795 + 3630055 * 2 ^ 59
def prefixEnd_3630055 : Nat := 4983230072969 + 3 ^ 40 * 3630055 * 2
def baseEnd_3630055 : Nat := 69035667305811115808081

theorem tailTrace_3630055 : CollatzResearch.WordTrace tailWord_3630055 prefixEnd_3630055 69035667305811115808081 := by
  unfold tailWord_3630055
  simp only [CollatzResearch.WordTrace]
  refine ⟨132398982863938173881251619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88265988575958782587501079 132398982863938173881251619)
  ·
    refine ⟨198598474295907260821877429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132398982863938173881251619 198598474295907260821877429)
    ·
      refine ⟨18618606965241305702051009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198598474295907260821877429 18618606965241305702051009)
      ·
        refine ⟨13963955223930979276538257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18618606965241305702051009 13963955223930979276538257)
        ·
          refine ⟨10472966417948234457403693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13963955223930979276538257 10472966417948234457403693)
          ·
            refine ⟨3927362406730587921526385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10472966417948234457403693 3927362406730587921526385)
            ·
              refine ⟨2945521805047940941144789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3927362406730587921526385 2945521805047940941144789)
              ·
                refine ⟨69035667305811115808081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2945521805047940941144789 69035667305811115808081)
                ·
                  rfl

theorem cell23_3630055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 7].length) (baseStart_3630055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630055 prefixEnd_3630055 := by exact prefixLift 3630055
  have htrace : WordTrace (prefixWord ++ tailWord_3630055) baseStart_3630055 baseEnd_3630055 := by
    simpa [prefixWord, tailWord_3630055, baseEnd_3630055] using wordTrace_append hprefix tailTrace_3630055
  have hstable : (prefixWord ++ tailWord_3630055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630055).length < 2 ^ (prefixWord ++ tailWord_3630055).sum := by decide
  have hdescent : baseEnd_3630055 < baseStart_3630055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630065 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_3630065 : Nat := 118140960795 + 3630065 * 2 ^ 59
def prefixEnd_3630065 : Nat := 4983230072969 + 3 ^ 40 * 3630065 * 2
def baseEnd_3630065 : Nat := 1863968152063445087693141

theorem tailTrace_3630065 : CollatzResearch.WordTrace tailWord_3630065 prefixEnd_3630065 1863968152063445087693141 := by
  unfold tailWord_3630065
  simp only [CollatzResearch.WordTrace]
  refine ⟨132399347593901945589115649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88266231729267963726077099 132399347593901945589115649)
  ·
    refine ⟨99299510695426459191836737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132399347593901945589115649 99299510695426459191836737)
    ·
      refine ⟨74474633021569844393877553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99299510695426459191836737 74474633021569844393877553)
      ·
        refine ⟨55855974766177383295408165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74474633021569844393877553 55855974766177383295408165)
        ·
          refine ⟨10472995268658259367889031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55855974766177383295408165 10472995268658259367889031)
          ·
            refine ⟨15709492902987389051833547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472995268658259367889031 15709492902987389051833547)
            ·
              refine ⟨23564239354481083577750321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15709492902987389051833547 23564239354481083577750321)
              ·
                refine ⟨17673179515860812683312741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23564239354481083577750321 17673179515860812683312741)
                ·
                  refine ⟨3313721159223902378121139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17673179515860812683312741 3313721159223902378121139)
                  ·
                    refine ⟨4970581738835853567181709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3313721159223902378121139 4970581738835853567181709)
                    ·
                      refine ⟨1863968152063445087693141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4970581738835853567181709 1863968152063445087693141)
                      ·
                        rfl

theorem cell23_3630065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_3630065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630065 prefixEnd_3630065 := by exact prefixLift 3630065
  have htrace : WordTrace (prefixWord ++ tailWord_3630065) baseStart_3630065 baseEnd_3630065 := by
    simpa [prefixWord, tailWord_3630065, baseEnd_3630065] using wordTrace_append hprefix tailTrace_3630065
  have hstable : (prefixWord ++ tailWord_3630065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630065).length < 2 ^ (prefixWord ++ tailWord_3630065).sum := by decide
  have hdescent : baseEnd_3630065 < baseStart_3630065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630158 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_3630158 : Nat := 118140960795 + 3630158 * 2 ^ 59
def prefixEnd_3630158 : Nat := 4983230072969 + 3 ^ 40 * 3630158 * 2
def baseEnd_3630158 : Nat := 621338635254771074610071

theorem tailTrace_3630158 : CollatzResearch.WordTrace tailWord_3630158 prefixEnd_3630158 621338635254771074610071 := by
  unfold tailWord_3630158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16550342447820627809031391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88268493055043348314834085 16550342447820627809031391)
  ·
    refine ⟨24825513671730941713547087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16550342447820627809031391 24825513671730941713547087)
    ·
      refine ⟨37238270507596412570320631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24825513671730941713547087 37238270507596412570320631)
      ·
        refine ⟨55857405761394618855480947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37238270507596412570320631 55857405761394618855480947)
        ·
          refine ⟨83786108642091928283221421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55857405761394618855480947 83786108642091928283221421)
          ·
            refine ⟨31419790740784473106208033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83786108642091928283221421 31419790740784473106208033)
            ·
              refine ⟨23564843055588354829656025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31419790740784473106208033 23564843055588354829656025)
              ·
                refine ⟨17673632291691266122242019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23564843055588354829656025 17673632291691266122242019)
                ·
                  refine ⟨26510448437536899183363029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17673632291691266122242019 26510448437536899183363029)
                  ·
                    refine ⟨621338635254771074610071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26510448437536899183363029 621338635254771074610071)
                    ·
                      rfl

theorem cell23_3630158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_3630158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630158 prefixEnd_3630158 := by exact prefixLift 3630158
  have htrace : WordTrace (prefixWord ++ tailWord_3630158) baseStart_3630158 baseEnd_3630158 := by
    simpa [prefixWord, tailWord_3630158, baseEnd_3630158] using wordTrace_append hprefix tailTrace_3630158
  have hstable : (prefixWord ++ tailWord_3630158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630158).length < 2 ^ (prefixWord ++ tailWord_3630158).sum := by decide
  have hdescent : baseEnd_3630158 < baseStart_3630158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630165 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_3630165 : Nat := 118140960795 + 3630165 * 2 ^ 59
def prefixEnd_3630165 : Nat := 4983230072969 + 3 ^ 40 * 3630165 * 2
def baseEnd_3630165 : Nat := 1864019500128894696442681

theorem tailTrace_3630165 : CollatzResearch.WordTrace tailWord_3630165 prefixEnd_3630165 1864019500128894696442681 := by
  unfold tailWord_3630165
  simp only [CollatzResearch.WordTrace]
  refine ⟨132402994893539662667755949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88268663262359775111837299 132402994893539662667755949)
  ·
    refine ⟨49651123085077373500408481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132402994893539662667755949 49651123085077373500408481)
    ·
      refine ⟨37238342313808030125306361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49651123085077373500408481 37238342313808030125306361)
      ·
        refine ⟨27928756735356022593979771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37238342313808030125306361 27928756735356022593979771)
        ·
          refine ⟨41893135103034033890969657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27928756735356022593979771 41893135103034033890969657)
          ·
            refine ⟨31419851327275525418227243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41893135103034033890969657 31419851327275525418227243)
            ·
              refine ⟨47129776990913288127340865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31419851327275525418227243 47129776990913288127340865)
              ·
                refine ⟨35347332743184966095505649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47129776990913288127340865 35347332743184966095505649)
                ·
                  refine ⟨26510499557388724571629237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35347332743184966095505649 26510499557388724571629237)
                  ·
                    refine ⟨2485359333505192928590241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26510499557388724571629237 2485359333505192928590241)
                    ·
                      refine ⟨1864019500128894696442681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485359333505192928590241 1864019500128894696442681)
                      ·
                        rfl

theorem cell23_3630165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_3630165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630165 prefixEnd_3630165 := by exact prefixLift 3630165
  have htrace : WordTrace (prefixWord ++ tailWord_3630165) baseStart_3630165 baseEnd_3630165 := by
    simpa [prefixWord, tailWord_3630165, baseEnd_3630165] using wordTrace_append hprefix tailTrace_3630165
  have hstable : (prefixWord ++ tailWord_3630165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630165).length < 2 ^ (prefixWord ++ tailWord_3630165).sum := by decide
  have hdescent : baseEnd_3630165 < baseStart_3630165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630212 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 2, 4, 2]
def baseStart_3630212 : Nat := 118140960795 + 3630212 * 2 ^ 59
def prefixEnd_3630212 : Nat := 4983230072969 + 3 ^ 40 * 3630212 * 2
def baseEnd_3630212 : Nat := 1864043633719656012554965

theorem tailTrace_3630212 : CollatzResearch.WordTrace tailWord_3630212 prefixEnd_3630212 1864043633719656012554965 := by
  unfold tailWord_3630212
  simp only [CollatzResearch.WordTrace]
  refine ⟨66202354562184694847358445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88269806082912926463144593 66202354562184694847358445)
  ·
    refine ⟨24825882960819260567759417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66202354562184694847358445 24825882960819260567759417)
    ·
      refine ⟨18619412220614445425819563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24825882960819260567759417 18619412220614445425819563)
      ·
        refine ⟨27929118330921668138729345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18619412220614445425819563 27929118330921668138729345)
        ·
          refine ⟨20946838748191251104047009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27929118330921668138729345 20946838748191251104047009)
          ·
            refine ⟨15710129061143438328035257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20946838748191251104047009 15710129061143438328035257)
            ·
              refine ⟨11782596795857578746026443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15710129061143438328035257 11782596795857578746026443)
              ·
                refine ⟨17673895193786368119039665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11782596795857578746026443 17673895193786368119039665)
                ·
                  refine ⟨13255421395339776089279749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17673895193786368119039665 13255421395339776089279749)
                  ·
                    refine ⟨2485391511626208016739953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13255421395339776089279749 2485391511626208016739953)
                    ·
                      refine ⟨1864043633719656012554965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485391511626208016739953 1864043633719656012554965)
                      ·
                        rfl

theorem cell23_3630212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_3630212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630212 prefixEnd_3630212 := by exact prefixLift 3630212
  have htrace : WordTrace (prefixWord ++ tailWord_3630212) baseStart_3630212 baseEnd_3630212 := by
    simpa [prefixWord, tailWord_3630212, baseEnd_3630212] using wordTrace_append hprefix tailTrace_3630212
  have hstable : (prefixWord ++ tailWord_3630212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630212).length < 2 ^ (prefixWord ++ tailWord_3630212).sum := by decide
  have hdescent : baseEnd_3630212 < baseStart_3630212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630222 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_3630222 : Nat := 118140960795 + 3630222 * 2 ^ 59
def prefixEnd_3630222 : Nat := 4983230072969 + 3 ^ 40 * 3630222 * 2
def baseEnd_3630222 : Nat := 621349589508733657809973

theorem tailTrace_3630222 : CollatzResearch.WordTrace tailWord_3630222 prefixEnd_3630222 621349589508733657809973 := by
  unfold tailWord_3630222
  simp only [CollatzResearch.WordTrace]
  refine ⟨16550634231791645175322615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88270049236222107601720613 16550634231791645175322615)
  ·
    refine ⟨24825951347687467762983923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16550634231791645175322615 24825951347687467762983923)
    ·
      refine ⟨37238927021531201644475885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24825951347687467762983923 37238927021531201644475885)
      ·
        refine ⟨13964597633074200616678457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37238927021531201644475885 13964597633074200616678457)
        ·
          refine ⟨10473448224805650462508843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13964597633074200616678457 10473448224805650462508843)
          ·
            refine ⟨15710172337208475693763265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10473448224805650462508843 15710172337208475693763265)
            ·
              refine ⟨11782629252906356770322449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15710172337208475693763265 11782629252906356770322449)
              ·
                refine ⟨8836971939679767577741837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11782629252906356770322449 8836971939679767577741837)
                ·
                  refine ⟨3313864477379912841653189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8836971939679767577741837 3313864477379912841653189)
                  ·
                    refine ⟨621349589508733657809973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313864477379912841653189 621349589508733657809973)
                    ·
                      rfl

theorem cell23_3630222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_3630222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630222 prefixEnd_3630222 := by exact prefixLift 3630222
  have htrace : WordTrace (prefixWord ++ tailWord_3630222) baseStart_3630222 baseEnd_3630222 := by
    simpa [prefixWord, tailWord_3630222, baseEnd_3630222] using wordTrace_append hprefix tailTrace_3630222
  have hstable : (prefixWord ++ tailWord_3630222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630222).length < 2 ^ (prefixWord ++ tailWord_3630222).sum := by decide
  have hdescent : baseEnd_3630222 < baseStart_3630222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630282 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_3630282 : Nat := 118140960795 + 3630282 * 2 ^ 59
def prefixEnd_3630282 : Nat := 4983230072969 + 3 ^ 40 * 3630282 * 2
def baseEnd_3630282 : Nat := 621359859121823579559881

theorem tailTrace_3630282 : CollatzResearch.WordTrace tailWord_3630282 prefixEnd_3630282 621359859121823579559881 := by
  unfold tailWord_3630282
  simp only [CollatzResearch.WordTrace]
  refine ⟨33101815558528947912441275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88271508156077194433176733 33101815558528947912441275)
  ·
    refine ⟨49652723337793421868661913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33101815558528947912441275 49652723337793421868661913)
    ·
      refine ⟨37239542503345066401496435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49652723337793421868661913 37239542503345066401496435)
      ·
        refine ⟨55859313755017599602244653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37239542503345066401496435 55859313755017599602244653)
        ·
          refine ⟨20947242658131599850841745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55859313755017599602244653 20947242658131599850841745)
          ·
            refine ⟨15710431993598699888131309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20947242658131599850841745 15710431993598699888131309)
            ·
              refine ⟨5891411997599512458049241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15710431993598699888131309 5891411997599512458049241)
              ·
                refine ⟨4418558998199634343536931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5891411997599512458049241 4418558998199634343536931)
                ·
                  refine ⟨6627838497299451515305397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418558998199634343536931 6627838497299451515305397)
                  ·
                    refine ⟨621359859121823579559881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6627838497299451515305397 621359859121823579559881)
                    ·
                      rfl

theorem cell23_3630282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_3630282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630282 prefixEnd_3630282 := by exact prefixLift 3630282
  have htrace : WordTrace (prefixWord ++ tailWord_3630282) baseStart_3630282 baseEnd_3630282 := by
    simpa [prefixWord, tailWord_3630282, baseEnd_3630282] using wordTrace_append hprefix tailTrace_3630282
  have hstable : (prefixWord ++ tailWord_3630282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630282).length < 2 ^ (prefixWord ++ tailWord_3630282).sum := by decide
  have hdescent : baseEnd_3630282 < baseStart_3630282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630288 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5]
def baseStart_3630288 : Nat := 118140960795 + 3630288 * 2 ^ 59
def prefixEnd_3630288 : Nat := 4983230072969 + 3 ^ 40 * 3630288 * 2
def baseEnd_3630288 : Nat := 1864082658249397715204615

theorem tailTrace_3630288 : CollatzResearch.WordTrace tailWord_3630288 prefixEnd_3630288 1864082658249397715204615 := by
  unfold tailWord_3630288
  simp only [CollatzResearch.WordTrace]
  refine ⟨66203740536047027337241759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88271654048062703116322345 66203740536047027337241759)
  ·
    refine ⟨99305610804070541005862639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66203740536047027337241759 99305610804070541005862639)
    ·
      refine ⟨148958416206105811508793959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99305610804070541005862639 148958416206105811508793959)
      ·
        refine ⟨223437624309158717263190939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148958416206105811508793959 223437624309158717263190939)
        ·
          refine ⟨335156436463738075894786409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223437624309158717263190939 335156436463738075894786409)
          ·
            refine ⟨251367327347803556921089807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335156436463738075894786409 251367327347803556921089807)
            ·
              refine ⟨377050991021705335381634711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251367327347803556921089807 377050991021705335381634711)
              ·
                refine ⟨565576486532558003072452067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377050991021705335381634711 565576486532558003072452067)
                ·
                  refine ⟨848364729798837004608678101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 565576486532558003072452067 848364729798837004608678101)
                  ·
                    refine ⟨19883548354660242295515893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 848364729798837004608678101 19883548354660242295515893)
                    ·
                      refine ⟨1864082658249397715204615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19883548354660242295515893 1864082658249397715204615)
                      ·
                        rfl

theorem cell23_3630288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_3630288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630288 prefixEnd_3630288 := by exact prefixLift 3630288
  have htrace : WordTrace (prefixWord ++ tailWord_3630288) baseStart_3630288 baseEnd_3630288 := by
    simpa [prefixWord, tailWord_3630288, baseEnd_3630288] using wordTrace_append hprefix tailTrace_3630288
  have hstable : (prefixWord ++ tailWord_3630288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630288).length < 2 ^ (prefixWord ++ tailWord_3630288).sum := by decide
  have hdescent : baseEnd_3630288 < baseStart_3630288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630295 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 6, 4]
def baseStart_3630295 : Nat := 118140960795 + 3630295 * 2 ^ 59
def prefixEnd_3630295 : Nat := 4983230072969 + 3 ^ 40 * 3630295 * 2
def baseEnd_3630295 : Nat := 621362084204659729272361

theorem tailTrace_3630295 : CollatzResearch.WordTrace tailWord_3630295 prefixEnd_3630295 621362084204659729272361 := by
  unfold tailWord_3630295
  simp only [CollatzResearch.WordTrace]
  refine ⟨132407736383068694869988339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88271824255379129913325559 132407736383068694869988339)
  ·
    refine ⟨198611604574603042304982509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132407736383068694869988339 198611604574603042304982509)
    ·
      refine ⟨74479351715476140864368441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198611604574603042304982509 74479351715476140864368441)
      ·
        refine ⟨55859513786607105648276331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74479351715476140864368441 55859513786607105648276331)
        ·
          refine ⟨83789270679910658472414497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55859513786607105648276331 83789270679910658472414497)
          ·
            refine ⟨62841953009932993854310873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83789270679910658472414497 62841953009932993854310873)
            ·
              refine ⟨47131464757449745390733155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62841953009932993854310873 47131464757449745390733155)
              ·
                refine ⟨70697197136174618086099733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47131464757449745390733155 70697197136174618086099733)
                ·
                  refine ⟨3313931115758185222785925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 70697197136174618086099733 3313931115758185222785925)
                  ·
                    refine ⟨621362084204659729272361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3313931115758185222785925 621362084204659729272361)
                    ·
                      rfl

theorem cell23_3630295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_3630295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630295 prefixEnd_3630295 := by exact prefixLift 3630295
  have htrace : WordTrace (prefixWord ++ tailWord_3630295) baseStart_3630295 baseEnd_3630295 := by
    simpa [prefixWord, tailWord_3630295, baseEnd_3630295] using wordTrace_append hprefix tailTrace_3630295
  have hstable : (prefixWord ++ tailWord_3630295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630295).length < 2 ^ (prefixWord ++ tailWord_3630295).sum := by decide
  have hdescent : baseEnd_3630295 < baseStart_3630295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630395 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 3]
def baseStart_3630395 : Nat := 118140960795 + 3630395 * 2 ^ 59
def prefixEnd_3630395 : Nat := 4983230072969 + 3 ^ 40 * 3630395 * 2
def baseEnd_3630395 : Nat := 1864137600679428796566623

theorem tailTrace_3630395 : CollatzResearch.WordTrace tailWord_3630395 prefixEnd_3630395 1864137600679428796566623 := by
  unfold tailWord_3630395
  simp only [CollatzResearch.WordTrace]
  refine ⟨132411383682706411948628639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88274255788470941299085759 132411383682706411948628639)
  ·
    refine ⟨198617075524059617922942959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132411383682706411948628639 198617075524059617922942959)
    ·
      refine ⟨297925613286089426884414439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198617075524059617922942959 297925613286089426884414439)
      ·
        refine ⟨446888419929134140326621659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297925613286089426884414439 446888419929134140326621659)
        ·
          refine ⟨670332629893701210489932489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446888419929134140326621659 670332629893701210489932489)
          ·
            refine ⟨502749472420275907867449367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670332629893701210489932489 502749472420275907867449367)
            ·
              refine ⟨754124208630413861801174051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502749472420275907867449367 754124208630413861801174051)
              ·
                refine ⟨1131186312945620792701761077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754124208630413861801174051 1131186312945620792701761077)
                ·
                  refine ⟨106048716838651949315790101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1131186312945620792701761077 106048716838651949315790101)
                  ·
                    refine ⟨4971033601811810124177661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106048716838651949315790101 4971033601811810124177661)
                    ·
                      refine ⟨1864137600679428796566623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4971033601811810124177661 1864137600679428796566623)
                      ·
                        rfl

theorem cell23_3630395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 3].length) (baseStart_3630395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630395 prefixEnd_3630395 := by exact prefixLift 3630395
  have htrace : WordTrace (prefixWord ++ tailWord_3630395) baseStart_3630395 baseEnd_3630395 := by
    simpa [prefixWord, tailWord_3630395, baseEnd_3630395] using wordTrace_append hprefix tailTrace_3630395
  have hstable : (prefixWord ++ tailWord_3630395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630395).length < 2 ^ (prefixWord ++ tailWord_3630395).sum := by decide
  have hdescent : baseEnd_3630395 < baseStart_3630395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630396 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_3630396 : Nat := 118140960795 + 3630396 * 2 ^ 59
def prefixEnd_3630396 : Nat := 4983230072969 + 3 ^ 40 * 3630396 * 2
def baseEnd_3630396 : Nat := 1864138114160083292654119

theorem tailTrace_3630396 : CollatzResearch.WordTrace tailWord_3630396 prefixEnd_3630396 1864138114160083292654119 := by
  unfold tailWord_3630396
  simp only [CollatzResearch.WordTrace]
  refine ⟨66205710077851394559707521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88274280103801859412943361 66205710077851394559707521)
  ·
    refine ⟨49654282558388545919780641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66205710077851394559707521 49654282558388545919780641)
    ·
      refine ⟨37240711918791409439835481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49654282558388545919780641 37240711918791409439835481)
      ·
        refine ⟨27930533939093557079876611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37240711918791409439835481 27930533939093557079876611)
        ·
          refine ⟨41895800908640335619814917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27930533939093557079876611 41895800908640335619814917)
          ·
            refine ⟨7855462670370062928715297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41895800908640335619814917 7855462670370062928715297)
            ·
              refine ⟨5891597002777547196536473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7855462670370062928715297 5891597002777547196536473)
              ·
                refine ⟨4418697752083160397402355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5891597002777547196536473 4418697752083160397402355)
                ·
                  refine ⟨6628046628124740596103533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418697752083160397402355 6628046628124740596103533)
                  ·
                    refine ⟨2485517485546777723538825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6628046628124740596103533 2485517485546777723538825)
                    ·
                      refine ⟨1864138114160083292654119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485517485546777723538825 1864138114160083292654119)
                      ·
                        rfl

theorem cell23_3630396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_3630396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630396 prefixEnd_3630396 := by exact prefixLift 3630396
  have htrace : WordTrace (prefixWord ++ tailWord_3630396) baseStart_3630396 baseEnd_3630396 := by
    simpa [prefixWord, tailWord_3630396, baseEnd_3630396] using wordTrace_append hprefix tailTrace_3630396
  have hstable : (prefixWord ++ tailWord_3630396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630396).length < 2 ^ (prefixWord ++ tailWord_3630396).sum := by decide
  have hdescent : baseEnd_3630396 < baseStart_3630396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630405 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3630405 : Nat := 118140960795 + 3630405 * 2 ^ 59
def prefixEnd_3630405 : Nat := 4983230072969 + 3 ^ 40 * 3630405 * 2
def baseEnd_3630405 : Nat := 1864142735485973757441577

theorem tailTrace_3630405 : CollatzResearch.WordTrace tailWord_3630405 prefixEnd_3630405 1864142735485973757441577 := by
  unfold tailWord_3630405
  simp only [CollatzResearch.WordTrace]
  refine ⟨132411748412670183656492669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88274498941780122437661779 132411748412670183656492669)
  ·
    refine ⟨49654405654751318871184751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132411748412670183656492669 49654405654751318871184751)
    ·
      refine ⟨74481608482126978306777127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49654405654751318871184751 74481608482126978306777127)
      ·
        refine ⟨111722412723190467460165691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74481608482126978306777127 111722412723190467460165691)
        ·
          refine ⟨167583619084785701190248537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111722412723190467460165691 167583619084785701190248537)
          ·
            refine ⟨125687714313589275892686403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167583619084785701190248537 125687714313589275892686403)
            ·
              refine ⟨188531571470383913839029605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125687714313589275892686403 188531571470383913839029605)
              ·
                refine ⟨35349669650696983844818051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188531571470383913839029605 35349669650696983844818051)
                ·
                  refine ⟨53024504476045475767227077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35349669650696983844818051 53024504476045475767227077)
                  ·
                    refine ⟨9942094589258526706355077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53024504476045475767227077 9942094589258526706355077)
                    ·
                      refine ⟨1864142735485973757441577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9942094589258526706355077 1864142735485973757441577)
                      ·
                        rfl

theorem cell23_3630405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3630405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630405 prefixEnd_3630405 := by exact prefixLift 3630405
  have htrace : WordTrace (prefixWord ++ tailWord_3630405) baseStart_3630405 baseEnd_3630405 := by
    simpa [prefixWord, tailWord_3630405, baseEnd_3630405] using wordTrace_append hprefix tailTrace_3630405
  have hstable : (prefixWord ++ tailWord_3630405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630405).length < 2 ^ (prefixWord ++ tailWord_3630405).sum := by decide
  have hdescent : baseEnd_3630405 < baseStart_3630405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630409 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 4, 2, 2]
def baseStart_3630409 : Nat := 118140960795 + 3630409 * 2 ^ 59
def prefixEnd_3630409 : Nat := 4983230072969 + 3 ^ 40 * 3630409 * 2
def baseEnd_3630409 : Nat := 1864144789408591741791559

theorem tailTrace_3630409 : CollatzResearch.WordTrace tailWord_3630409 prefixEnd_3630409 1864144789408591741791559 := by
  unfold tailWord_3630409
  simp only [CollatzResearch.WordTrace]
  refine ⟨132411894304655692339638281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88274596203103794893092187 132411894304655692339638281)
  ·
    refine ⟨99308920728491769254728711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132411894304655692339638281 99308920728491769254728711)
    ·
      refine ⟨148963381092737653882093067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99308920728491769254728711 148963381092737653882093067)
      ·
        refine ⟨223445071639106480823139601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148963381092737653882093067 223445071639106480823139601)
        ·
          refine ⟨167583803729329860617354701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223445071639106480823139601 167583803729329860617354701)
          ·
            refine ⟨62843926398498697731508013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167583803729329860617354701 62843926398498697731508013)
            ·
              refine ⟨23566472399437011649315505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62843926398498697731508013 23566472399437011649315505)
              ·
                refine ⟨17674854299577758736986629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23566472399437011649315505 17674854299577758736986629)
                ·
                  refine ⟨3314035181170829763184993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17674854299577758736986629 3314035181170829763184993)
                  ·
                    refine ⟨2485526385878122322388745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3314035181170829763184993 2485526385878122322388745)
                    ·
                      refine ⟨1864144789408591741791559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485526385878122322388745 1864144789408591741791559)
                      ·
                        rfl

theorem cell23_3630409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 2, 2].length) (baseStart_3630409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630409 prefixEnd_3630409 := by exact prefixLift 3630409
  have htrace : WordTrace (prefixWord ++ tailWord_3630409) baseStart_3630409 baseEnd_3630409 := by
    simpa [prefixWord, tailWord_3630409, baseEnd_3630409] using wordTrace_append hprefix tailTrace_3630409
  have hstable : (prefixWord ++ tailWord_3630409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630409).length < 2 ^ (prefixWord ++ tailWord_3630409).sum := by decide
  have hdescent : baseEnd_3630409 < baseStart_3630409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630412 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3630412 : Nat := 118140960795 + 3630412 * 2 ^ 59
def prefixEnd_3630412 : Nat := 4983230072969 + 3 ^ 40 * 3630412 * 2
def baseEnd_3630412 : Nat := 1864146329850555230054045

theorem tailTrace_3630412 : CollatzResearch.WordTrace tailWord_3630412 prefixEnd_3630412 1864146329850555230054045 := by
  unfold tailWord_3630412
  simp only [CollatzResearch.WordTrace]
  refine ⟨66206001861822411925998745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88274669149096549234664993 66206001861822411925998745)
  ·
    refine ⟨49654501396366808944499059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66206001861822411925998745 49654501396366808944499059)
    ·
      refine ⟨74481752094550213416748589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49654501396366808944499059 74481752094550213416748589)
      ·
        refine ⟨27930657035456330031280721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74481752094550213416748589 27930657035456330031280721)
        ·
          refine ⟨20947992776592247523460541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27930657035456330031280721 20947992776592247523460541)
          ·
            refine ⟨7855497291222092821297703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20947992776592247523460541 7855497291222092821297703)
            ·
              refine ⟨11783245936833139231946555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7855497291222092821297703 11783245936833139231946555)
              ·
                refine ⟨17674868905249708847919833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11783245936833139231946555 17674868905249708847919833)
                ·
                  refine ⟨13256151678937281635939875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17674868905249708847919833 13256151678937281635939875)
                  ·
                    refine ⟨19884227518405922453909813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13256151678937281635939875 19884227518405922453909813)
                    ·
                      refine ⟨1864146329850555230054045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19884227518405922453909813 1864146329850555230054045)
                      ·
                        rfl

theorem cell23_3630412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3630412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630412 prefixEnd_3630412 := by exact prefixLift 3630412
  have htrace : WordTrace (prefixWord ++ tailWord_3630412) baseStart_3630412 baseEnd_3630412 := by
    simpa [prefixWord, tailWord_3630412, baseEnd_3630412] using wordTrace_append hprefix tailTrace_3630412
  have hstable : (prefixWord ++ tailWord_3630412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630412).length < 2 ^ (prefixWord ++ tailWord_3630412).sum := by decide
  have hdescent : baseEnd_3630412 < baseStart_3630412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630432 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 7]
def baseStart_3630432 : Nat := 118140960795 + 3630432 * 2 ^ 59
def prefixEnd_3630432 : Nat := 4983230072969 + 3 ^ 40 * 3630432 * 2
def baseEnd_3630432 : Nat := 207128511051516127978217

theorem tailTrace_3630432 : CollatzResearch.WordTrace tailWord_3630432 prefixEnd_3630432 207128511051516127978217 := by
  unfold tailWord_3630432
  simp only [CollatzResearch.WordTrace]
  refine ⟨66206366591786183633862775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88275155455714911511817033 66206366591786183633862775)
  ·
    refine ⟨99309549887679275450794163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66206366591786183633862775 99309549887679275450794163)
    ·
      refine ⟨148964324831518913176191245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99309549887679275450794163 148964324831518913176191245)
      ·
        refine ⟨55861621811819592441071717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148964324831518913176191245 55861621811819592441071717)
        ·
          refine ⟨10474054089716173582700947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55861621811819592441071717 10474054089716173582700947)
          ·
            refine ⟨15711081134574260374051421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10474054089716173582700947 15711081134574260374051421)
            ·
              refine ⟨5891655425465347640269283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15711081134574260374051421 5891655425465347640269283)
              ·
                refine ⟨8837483138198021460403925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891655425465347640269283 8837483138198021460403925)
                ·
                  refine ⟨207128511051516127978217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8837483138198021460403925 207128511051516127978217)
                  ·
                    rfl

theorem cell23_3630432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 7].length) (baseStart_3630432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630432 prefixEnd_3630432 := by exact prefixLift 3630432
  have htrace : WordTrace (prefixWord ++ tailWord_3630432) baseStart_3630432 baseEnd_3630432 := by
    simpa [prefixWord, tailWord_3630432, baseEnd_3630432] using wordTrace_append hprefix tailTrace_3630432
  have hstable : (prefixWord ++ tailWord_3630432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630432).length < 2 ^ (prefixWord ++ tailWord_3630432).sum := by decide
  have hdescent : baseEnd_3630432 < baseStart_3630432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630455 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_3630455 : Nat := 118140960795 + 3630455 * 2 ^ 59
def prefixEnd_3630455 : Nat := 4983230072969 + 3 ^ 40 * 3630455 * 2
def baseEnd_3630455 : Nat := 1864168409518698561816347

theorem tailTrace_3630455 : CollatzResearch.WordTrace tailWord_3630455 prefixEnd_3630455 1864168409518698561816347 := by
  unfold tailWord_3630455
  simp only [CollatzResearch.WordTrace]
  refine ⟨132413572062489042195812819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88275714708326028130541879 132413572062489042195812819)
  ·
    refine ⟨198620358093733563293719229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132413572062489042195812819 198620358093733563293719229)
    ·
      refine ⟨74482634285150086235144711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198620358093733563293719229 74482634285150086235144711)
      ·
        refine ⟨111723951427725129352717067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74482634285150086235144711 111723951427725129352717067)
        ·
          refine ⟨167585927141587694029075601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111723951427725129352717067 167585927141587694029075601)
          ·
            refine ⟨125689445356190770521806701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167585927141587694029075601 125689445356190770521806701)
            ·
              refine ⟨47133542008571538945677513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125689445356190770521806701 47133542008571538945677513)
              ·
                refine ⟨35350156506428654209258135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47133542008571538945677513 35350156506428654209258135)
                ·
                  refine ⟨53025234759642981313887203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35350156506428654209258135 53025234759642981313887203)
                  ·
                    refine ⟨79537852139464471970830805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53025234759642981313887203 79537852139464471970830805)
                    ·
                      refine ⟨1864168409518698561816347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79537852139464471970830805 1864168409518698561816347)
                      ·
                        rfl

theorem cell23_3630455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_3630455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630455 prefixEnd_3630455 := by exact prefixLift 3630455
  have htrace : WordTrace (prefixWord ++ tailWord_3630455) baseStart_3630455 baseEnd_3630455 := by
    simpa [prefixWord, tailWord_3630455, baseEnd_3630455] using wordTrace_append hprefix tailTrace_3630455
  have hstable : (prefixWord ++ tailWord_3630455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630455).length < 2 ^ (prefixWord ++ tailWord_3630455).sum := by decide
  have hdescent : baseEnd_3630455 < baseStart_3630455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630472 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3630472 : Nat := 118140960795 + 3630472 * 2 ^ 59
def prefixEnd_3630472 : Nat := 4983230072969 + 3 ^ 40 * 3630472 * 2
def baseEnd_3630472 : Nat := 1864177138689824995303769

theorem tailTrace_3630472 : CollatzResearch.WordTrace tailWord_3630472 prefixEnd_3630472 1864177138689824995303769 := by
  unfold tailWord_3630472
  simp only [CollatzResearch.WordTrace]
  refine ⟨66207096051713727049590835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88276128068951636066121113 66207096051713727049590835)
  ·
    refine ⟨99310644077570590574386253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66207096051713727049590835 99310644077570590574386253)
    ·
      refine ⟨37241491529088971465394845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99310644077570590574386253 37241491529088971465394845)
      ·
        refine ⟨13965559323408364299523067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37241491529088971465394845 13965559323408364299523067)
        ·
          refine ⟨20948338985112546449284601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13965559323408364299523067 20948338985112546449284601)
          ·
            refine ⟨15711254238834409836963451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20948338985112546449284601 15711254238834409836963451)
            ·
              refine ⟨23566881358251614755445177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15711254238834409836963451 23566881358251614755445177)
              ·
                refine ⟨17675161018688711066583883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23566881358251614755445177 17675161018688711066583883)
                ·
                  refine ⟨26512741528033066599875825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17675161018688711066583883 26512741528033066599875825)
                  ·
                    refine ⟨19884556146024799949906869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26512741528033066599875825 19884556146024799949906869)
                    ·
                      refine ⟨1864177138689824995303769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19884556146024799949906869 1864177138689824995303769)
                      ·
                        rfl

theorem cell23_3630472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3630472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630472 prefixEnd_3630472 := by exact prefixLift 3630472
  have htrace : WordTrace (prefixWord ++ tailWord_3630472) baseStart_3630472 baseEnd_3630472 := by
    simpa [prefixWord, tailWord_3630472, baseEnd_3630472] using wordTrace_append hprefix tailTrace_3630472
  have hstable : (prefixWord ++ tailWord_3630472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630472).length < 2 ^ (prefixWord ++ tailWord_3630472).sum := by decide
  have hdescent : baseEnd_3630472 < baseStart_3630472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630499 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 2, 4, 2]
def baseStart_3630499 : Nat := 118140960795 + 3630499 * 2 ^ 59
def prefixEnd_3630499 : Nat := 4983230072969 + 3 ^ 40 * 3630499 * 2
def baseEnd_3630499 : Nat := 1864191002667496389666145

theorem tailTrace_3630499 : CollatzResearch.WordTrace tailWord_3630499 prefixEnd_3630499 1864191002667496389666145 := by
  unfold tailWord_3630499
  simp only [CollatzResearch.WordTrace]
  refine ⟨132415176874329637710414551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88276784582886425140276367 132415176874329637710414551)
  ·
    refine ⟨198622765311494456565621827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132415176874329637710414551 198622765311494456565621827)
    ·
      refine ⟨297934147967241684848432741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198622765311494456565621827 297934147967241684848432741)
      ·
        refine ⟨55862652743857815909081139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297934147967241684848432741 55862652743857815909081139)
        ·
          refine ⟨83793979115786723863621709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55862652743857815909081139 83793979115786723863621709)
          ·
            refine ⟨31422742168420021448858141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83793979115786723863621709 31422742168420021448858141)
            ·
              refine ⟨11783528313157508043321803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31422742168420021448858141 11783528313157508043321803)
              ·
                refine ⟨17675292469736262064982705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11783528313157508043321803 17675292469736262064982705)
                ·
                  refine ⟨13256469352302196548737029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17675292469736262064982705 13256469352302196548737029)
                  ·
                    refine ⟨2485588003556661852888193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13256469352302196548737029 2485588003556661852888193)
                    ·
                      refine ⟨1864191002667496389666145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485588003556661852888193 1864191002667496389666145)
                      ·
                        rfl

theorem cell23_3630499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_3630499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630499 prefixEnd_3630499 := by exact prefixLift 3630499
  have htrace : WordTrace (prefixWord ++ tailWord_3630499) baseStart_3630499 baseEnd_3630499 := by
    simpa [prefixWord, tailWord_3630499, baseEnd_3630499] using wordTrace_append hprefix tailTrace_3630499
  have hstable : (prefixWord ++ tailWord_3630499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630499).length < 2 ^ (prefixWord ++ tailWord_3630499).sum := by decide
  have hdescent : baseEnd_3630499 < baseStart_3630499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630505 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 12]
def baseStart_3630505 : Nat := 118140960795 + 3630505 * 2 ^ 59
def prefixEnd_3630505 : Nat := 4983230072969 + 3 ^ 40 * 3630505 * 2
def baseEnd_3630505 : Nat := 207132675950158151799013

theorem tailTrace_3630505 : CollatzResearch.WordTrace tailWord_3630505 prefixEnd_3630505 207132675950158151799013 := by
  unfold tailWord_3630505
  simp only [CollatzResearch.WordTrace]
  refine ⟨132415395712307900735132969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88276930474871933823421979 132415395712307900735132969)
  ·
    refine ⟨99311546784230925551349727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132415395712307900735132969 99311546784230925551349727)
    ·
      refine ⟨148967320176346388327024591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99311546784230925551349727 148967320176346388327024591)
      ·
        refine ⟨223450980264519582490536887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148967320176346388327024591 223450980264519582490536887)
        ·
          refine ⟨335176470396779373735805331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223450980264519582490536887 335176470396779373735805331)
          ·
            refine ⟨502764705595169060603707997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335176470396779373735805331 502764705595169060603707997)
            ·
              refine ⟨188536764598188397726390499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502764705595169060603707997 188536764598188397726390499)
              ·
                refine ⟨282805146897282596589585749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188536764598188397726390499 282805146897282596589585749)
                ·
                  refine ⟨207132675950158151799013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 282805146897282596589585749 207132675950158151799013)
                  ·
                    rfl

theorem cell23_3630505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_3630505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630505 prefixEnd_3630505 := by exact prefixLift 3630505
  have htrace : WordTrace (prefixWord ++ tailWord_3630505) baseStart_3630505 baseEnd_3630505 := by
    simpa [prefixWord, tailWord_3630505, baseEnd_3630505] using wordTrace_append hprefix tailTrace_3630505
  have hstable : (prefixWord ++ tailWord_3630505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630505).length < 2 ^ (prefixWord ++ tailWord_3630505).sum := by decide
  have hdescent : baseEnd_3630505 < baseStart_3630505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630542 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3630542 : Nat := 118140960795 + 3630542 * 2 ^ 59
def prefixEnd_3630542 : Nat := 4983230072969 + 3 ^ 40 * 3630542 * 2
def baseEnd_3630542 : Nat := 1864213082335639721428447

theorem tailTrace_3630542 : CollatzResearch.WordTrace tailWord_3630542 prefixEnd_3630542 1864213082335639721428447 := by
  unfold tailWord_3630542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16552093151646732006778735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88277830142115904036153253 16552093151646732006778735)
  ·
    refine ⟨24828139727470098010168103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16552093151646732006778735 24828139727470098010168103)
    ·
      refine ⟨37242209591205147015252155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24828139727470098010168103 37242209591205147015252155)
      ·
        refine ⟨55863314386807720522878233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37242209591205147015252155 55863314386807720522878233)
        ·
          refine ⟨41897485790105790392158675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55863314386807720522878233 41897485790105790392158675)
          ·
            refine ⟨62846228685158685588238013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41897485790105790392158675 62846228685158685588238013)
            ·
              refine ⟨23567335756934507095589255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62846228685158685588238013 23567335756934507095589255)
              ·
                refine ⟨35351003635401760643383883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23567335756934507095589255 35351003635401760643383883)
                ·
                  refine ⟨53026505453102640965075825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35351003635401760643383883 53026505453102640965075825)
                  ·
                    refine ⟨39769879089826980723806869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53026505453102640965075825 39769879089826980723806869)
                    ·
                      refine ⟨1864213082335639721428447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39769879089826980723806869 1864213082335639721428447)
                      ·
                        rfl

theorem cell23_3630542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3630542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630542 prefixEnd_3630542 := by exact prefixLift 3630542
  have htrace : WordTrace (prefixWord ++ tailWord_3630542) baseStart_3630542 baseEnd_3630542 := by
    simpa [prefixWord, tailWord_3630542, baseEnd_3630542] using wordTrace_append hprefix tailTrace_3630542
  have hstable : (prefixWord ++ tailWord_3630542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630542).length < 2 ^ (prefixWord ++ tailWord_3630542).sum := by decide
  have hdescent : baseEnd_3630542 < baseStart_3630542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630552 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 5, 5]
def baseStart_3630552 : Nat := 118140960795 + 3630552 * 2 ^ 59
def prefixEnd_3630552 : Nat := 4983230072969 + 3 ^ 40 * 3630552 * 2
def baseEnd_3630552 : Nat := 621406072380728227434467

theorem tailTrace_3630552 : CollatzResearch.WordTrace tailWord_3630552 prefixEnd_3630552 621406072380728227434467 := by
  unfold tailWord_3630552
  simp only [CollatzResearch.WordTrace]
  refine ⟨66208554971568813881046955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88278073295425085174729273 66208554971568813881046955)
  ·
    refine ⟨99312832457353220821570433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66208554971568813881046955 99312832457353220821570433)
    ·
      refine ⟨74484624343014915616177825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99312832457353220821570433 74484624343014915616177825)
      ·
        refine ⟨55863468257261186712133369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74484624343014915616177825 55863468257261186712133369)
        ·
          refine ⟨41897601192945890034100027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55863468257261186712133369 41897601192945890034100027)
          ·
            refine ⟨62846401789418835051150041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41897601192945890034100027 62846401789418835051150041)
            ·
              refine ⟨47134801342064126288362531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62846401789418835051150041 47134801342064126288362531)
              ·
                refine ⟨70702202013096189432543797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47134801342064126288362531 70702202013096189432543797)
                ·
                  refine ⟨6628331438727767759300981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70702202013096189432543797 6628331438727767759300981)
                  ·
                    refine ⟨621406072380728227434467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6628331438727767759300981 621406072380728227434467)
                    ·
                      rfl

theorem cell23_3630552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_3630552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630552 prefixEnd_3630552 := by exact prefixLift 3630552
  have htrace : WordTrace (prefixWord ++ tailWord_3630552) baseStart_3630552 baseEnd_3630552 := by
    simpa [prefixWord, tailWord_3630552, baseEnd_3630552] using wordTrace_append hprefix tailTrace_3630552
  have hstable : (prefixWord ++ tailWord_3630552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630552).length < 2 ^ (prefixWord ++ tailWord_3630552).sum := by decide
  have hdescent : baseEnd_3630552 < baseStart_3630552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630559 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 3, 5, 2]
def baseStart_3630559 : Nat := 118140960795 + 3630559 * 2 ^ 59
def prefixEnd_3630559 : Nat := 4983230072969 + 3 ^ 40 * 3630559 * 2
def baseEnd_3630559 : Nat := 1864221811506766154915869

theorem tailTrace_3630559 : CollatzResearch.WordTrace tailWord_3630559 prefixEnd_3630559 1864221811506766154915869 := by
  unfold tailWord_3630559
  simp only [CollatzResearch.WordTrace]
  refine ⟨132417365254112267957598731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88278243502741511971732487 132417365254112267957598731)
  ·
    refine ⟨198626047881168401936398097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132417365254112267957598731 198626047881168401936398097)
    ·
      refine ⟨148969535910876301452298573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198626047881168401936398097 148969535910876301452298573)
      ·
        refine ⟨55863575966578613044611965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148969535910876301452298573 55863575966578613044611965)
        ·
          refine ⟨20948840987466979891729487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55863575966578613044611965 20948840987466979891729487)
          ·
            refine ⟨31423261481200469837594231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20948840987466979891729487 31423261481200469837594231)
            ·
              refine ⟨47134892221800704756391347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31423261481200469837594231 47134892221800704756391347)
              ·
                refine ⟨70702338332701057134587021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47134892221800704756391347 70702338332701057134587021)
                ·
                  refine ⟨26513376874762896425470133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70702338332701057134587021 26513376874762896425470133)
                  ·
                    refine ⟨2485629082009021539887825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26513376874762896425470133 2485629082009021539887825)
                    ·
                      refine ⟨1864221811506766154915869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485629082009021539887825 1864221811506766154915869)
                      ·
                        rfl

theorem cell23_3630559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_3630559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630559 prefixEnd_3630559 := by exact prefixLift 3630559
  have htrace : WordTrace (prefixWord ++ tailWord_3630559) baseStart_3630559 baseEnd_3630559 := by
    simpa [prefixWord, tailWord_3630559, baseEnd_3630559] using wordTrace_append hprefix tailTrace_3630559
  have hstable : (prefixWord ++ tailWord_3630559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630559).length < 2 ^ (prefixWord ++ tailWord_3630559).sum := by decide
  have hdescent : baseEnd_3630559 < baseStart_3630559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630593 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_3630593 : Nat := 118140960795 + 3630593 * 2 ^ 59
def prefixEnd_3630593 : Nat := 4983230072969 + 3 ^ 40 * 3630593 * 2
def baseEnd_3630593 : Nat := 1864239269849019021890713

theorem tailTrace_3630593 : CollatzResearch.WordTrace tailWord_3630593 prefixEnd_3630593 1864239269849019021890713 := by
  unfold tailWord_3630593
  simp only [CollatzResearch.WordTrace]
  refine ⟨132418605335989091764336433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88279070223992727842890955 132418605335989091764336433)
  ·
    refine ⟨99313954001991818823252325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132418605335989091764336433 99313954001991818823252325)
    ·
      refine ⟨18621366375373466029359811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99313954001991818823252325 18621366375373466029359811)
      ·
        refine ⟨27932049563060199044039717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18621366375373466029359811 27932049563060199044039717)
        ·
          refine ⟨5237259293073787320757447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27932049563060199044039717 5237259293073787320757447)
          ·
            refine ⟨7855888939610680981136171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237259293073787320757447 7855888939610680981136171)
            ·
              refine ⟨11783833409416021471704257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7855888939610680981136171 11783833409416021471704257)
              ·
                refine ⟨8837875057062016103778193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11783833409416021471704257 8837875057062016103778193)
                ·
                  refine ⟨6628406292796512077833645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8837875057062016103778193 6628406292796512077833645)
                  ·
                    refine ⟨2485652359798692029187617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6628406292796512077833645 2485652359798692029187617)
                    ·
                      refine ⟨1864239269849019021890713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485652359798692029187617 1864239269849019021890713)
                      ·
                        rfl

theorem cell23_3630593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_3630593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630593 prefixEnd_3630593 := by exact prefixLift 3630593
  have htrace : WordTrace (prefixWord ++ tailWord_3630593) baseStart_3630593 baseEnd_3630593 := by
    simpa [prefixWord, tailWord_3630593, baseEnd_3630593] using wordTrace_append hprefix tailTrace_3630593
  have hstable : (prefixWord ++ tailWord_3630593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630593).length < 2 ^ (prefixWord ++ tailWord_3630593).sum := by decide
  have hdescent : baseEnd_3630593 < baseStart_3630593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630609 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_3630609 : Nat := 118140960795 + 3630609 * 2 ^ 59
def prefixEnd_3630609 : Nat := 4983230072969 + 3 ^ 40 * 3630609 * 2
def baseEnd_3630609 : Nat := 1864247485539490959290639

theorem tailTrace_3630609 : CollatzResearch.WordTrace tailWord_3630609 prefixEnd_3630609 1864247485539490959290639 := by
  unfold tailWord_3630609
  simp only [CollatzResearch.WordTrace]
  refine ⟨132419188903931126496918881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88279459269287417664612587 132419188903931126496918881)
  ·
    refine ⟨99314391677948344872689161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132419188903931126496918881 99314391677948344872689161)
    ·
      refine ⟨74485793758461258654516871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99314391677948344872689161 74485793758461258654516871)
      ·
        refine ⟨111728690637691887981775307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74485793758461258654516871 111728690637691887981775307)
        ·
          refine ⟨167593035956537831972662961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111728690637691887981775307 167593035956537831972662961)
          ·
            refine ⟨125694776967403373979497221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167593035956537831972662961 125694776967403373979497221)
            ·
              refine ⟨23567770681388132621155729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125694776967403373979497221 23567770681388132621155729)
              ·
                refine ⟨17675828011041099465866797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23567770681388132621155729 17675828011041099465866797)
                ·
                  refine ⟨6628435504140412299700049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17675828011041099465866797 6628435504140412299700049)
                  ·
                    refine ⟨4971326628105309224775037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6628435504140412299700049 4971326628105309224775037)
                    ·
                      refine ⟨1864247485539490959290639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4971326628105309224775037 1864247485539490959290639)
                      ·
                        rfl

theorem cell23_3630609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_3630609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630609 prefixEnd_3630609 := by exact prefixLift 3630609
  have htrace : WordTrace (prefixWord ++ tailWord_3630609) baseStart_3630609 baseEnd_3630609 := by
    simpa [prefixWord, tailWord_3630609, baseEnd_3630609] using wordTrace_append hprefix tailTrace_3630609
  have hstable : (prefixWord ++ tailWord_3630609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630609).length < 2 ^ (prefixWord ++ tailWord_3630609).sum := by decide
  have hdescent : baseEnd_3630609 < baseStart_3630609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630643 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 1, 2, 3]
def baseStart_3630643 : Nat := 118140960795 + 3630643 * 2 ^ 59
def prefixEnd_3630643 : Nat := 4983230072969 + 3 ^ 40 * 3630643 * 2
def baseEnd_3630643 : Nat := 1864264943881743826265483

theorem tailTrace_3630643 : CollatzResearch.WordTrace tailWord_3630643 prefixEnd_3630643 1864264943881743826265483 := by
  unfold tailWord_3630643
  simp only [CollatzResearch.WordTrace]
  refine ⟨132420428985807950303656583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88280285990538633535771055 132420428985807950303656583)
  ·
    refine ⟨198630643478711925455484875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132420428985807950303656583 198630643478711925455484875)
    ·
      refine ⟨297945965218067888183227313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198630643478711925455484875 297945965218067888183227313)
      ·
        refine ⟨223459473913550916137420485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297945965218067888183227313 223459473913550916137420485)
        ·
          refine ⟨41898651358790796775766341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223459473913550916137420485 41898651358790796775766341)
          ·
            refine ⟨7855997129773274395456189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41898651358790796775766341 7855997129773274395456189)
            ·
              refine ⟨2945998923664977898296071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7855997129773274395456189 2945998923664977898296071)
              ·
                refine ⟨4418998385497466847444107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2945998923664977898296071 4418998385497466847444107)
                ·
                  refine ⟨6628497578246200271166161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418998385497466847444107 6628497578246200271166161)
                  ·
                    refine ⟨4971373183684650203374621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6628497578246200271166161 4971373183684650203374621)
                    ·
                      refine ⟨1864264943881743826265483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4971373183684650203374621 1864264943881743826265483)
                      ·
                        rfl

theorem cell23_3630643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 1, 2, 3].length) (baseStart_3630643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630643 prefixEnd_3630643 := by exact prefixLift 3630643
  have htrace : WordTrace (prefixWord ++ tailWord_3630643) baseStart_3630643 baseEnd_3630643 := by
    simpa [prefixWord, tailWord_3630643, baseEnd_3630643] using wordTrace_append hprefix tailTrace_3630643
  have hstable : (prefixWord ++ tailWord_3630643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630643).length < 2 ^ (prefixWord ++ tailWord_3630643).sum := by decide
  have hdescent : baseEnd_3630643 < baseStart_3630643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630646 : List Nat := [5, 1, 2, 1, 4, 10]
def baseStart_3630646 : Nat := 118140960795 + 3630646 * 2 ^ 59
def prefixEnd_3630646 : Nat := 4983230072969 + 3 ^ 40 * 3630646 * 2
def baseEnd_3630646 : Nat := 7671878536311552734683

theorem tailTrace_3630646 : CollatzResearch.WordTrace tailWord_3630646 prefixEnd_3630646 7671878536311552734683 := by
  unfold tailWord_3630646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276283650299817613500987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88280358936531387877343861 8276283650299817613500987)
  ·
    refine ⟨12414425475449726420251481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8276283650299817613500987 12414425475449726420251481)
    ·
      refine ⟨9310819106587294815188611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12414425475449726420251481 9310819106587294815188611)
      ·
        refine ⟨13966228659880942222782917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310819106587294815188611 13966228659880942222782917)
        ·
          refine ⟨2618667873727676666771797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13966228659880942222782917 2618667873727676666771797)
          ·
            refine ⟨7671878536311552734683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2618667873727676666771797 7671878536311552734683)
            ·
              rfl

theorem cell23_3630646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 10].length) (baseStart_3630646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630646 prefixEnd_3630646 := by exact prefixLift 3630646
  have htrace : WordTrace (prefixWord ++ tailWord_3630646) baseStart_3630646 baseEnd_3630646 := by
    simpa [prefixWord, tailWord_3630646, baseEnd_3630646] using wordTrace_append hprefix tailTrace_3630646
  have hstable : (prefixWord ++ tailWord_3630646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630646).length < 2 ^ (prefixWord ++ tailWord_3630646).sum := by decide
  have hdescent : baseEnd_3630646 < baseStart_3630646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630666 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_3630666 : Nat := 118140960795 + 3630666 * 2 ^ 59
def prefixEnd_3630666 : Nat := 4983230072969 + 3 ^ 40 * 3630666 * 2
def baseEnd_3630666 : Nat := 1864276753936797236277877

theorem tailTrace_3630666 : CollatzResearch.WordTrace tailWord_3630666 prefixEnd_3630666 1864276753936797236277877 := by
  unfold tailWord_3630666
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105316966181156307935963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88280845243149750154495901 33105316966181156307935963)
  ·
    refine ⟨49657975449271734461903945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33105316966181156307935963 49657975449271734461903945)
    ·
      refine ⟨37243481586953800846427959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49657975449271734461903945 37243481586953800846427959)
      ·
        refine ⟨55865222380430701269641939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37243481586953800846427959 55865222380430701269641939)
        ·
          refine ⟨83797833570646051904462909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55865222380430701269641939 83797833570646051904462909)
          ·
            refine ⟨31424187588992269464173591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83797833570646051904462909 31424187588992269464173591)
            ·
              refine ⟨47136281383488404196260387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31424187588992269464173591 47136281383488404196260387)
              ·
                refine ⟨70704422075232606294390581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47136281383488404196260387 70704422075232606294390581)
                ·
                  refine ⟨6628539569553056840099117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70704422075232606294390581 6628539569553056840099117)
                  ·
                    refine ⟨2485702338582396315037169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6628539569553056840099117 2485702338582396315037169)
                    ·
                      refine ⟨1864276753936797236277877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485702338582396315037169 1864276753936797236277877)
                      ·
                        rfl

theorem cell23_3630666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_3630666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630666 prefixEnd_3630666 := by exact prefixLift 3630666
  have htrace : WordTrace (prefixWord ++ tailWord_3630666) baseStart_3630666 baseEnd_3630666 := by
    simpa [prefixWord, tailWord_3630666, baseEnd_3630666] using wordTrace_append hprefix tailTrace_3630666
  have hstable : (prefixWord ++ tailWord_3630666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630666).length < 2 ^ (prefixWord ++ tailWord_3630666).sum := by decide
  have hdescent : baseEnd_3630666 < baseStart_3630666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630713 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 4, 2, 2]
def baseStart_3630713 : Nat := 118140960795 + 3630713 * 2 ^ 59
def prefixEnd_3630713 : Nat := 4983230072969 + 3 ^ 40 * 3630713 * 2
def baseEnd_3630713 : Nat := 1864300887527558552390161

theorem tailTrace_3630713 : CollatzResearch.WordTrace tailWord_3630713 prefixEnd_3630713 1864300887527558552390161 := by
  unfold tailWord_3630713
  simp only [CollatzResearch.WordTrace]
  refine ⟨132422982095554352258704793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88281988063702901505803195 132422982095554352258704793)
  ·
    refine ⟨99317236571665764194028595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132422982095554352258704793 99317236571665764194028595)
    ·
      refine ⟨148975854857498646291042893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99317236571665764194028595 148975854857498646291042893)
      ·
        refine ⟨55865945571561992359141085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148975854857498646291042893 55865945571561992359141085)
        ·
          refine ⟨20949729589335747134677907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55865945571561992359141085 20949729589335747134677907)
          ·
            refine ⟨31424594384003620702016861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20949729589335747134677907 31424594384003620702016861)
            ·
              refine ⟨11784222894001357763256323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31424594384003620702016861 11784222894001357763256323)
              ·
                refine ⟨17676334341002036644884485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11784222894001357763256323 17676334341002036644884485)
                ·
                  refine ⟨3314312688937881870915841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17676334341002036644884485 3314312688937881870915841)
                  ·
                    refine ⟨2485734516703411403186881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3314312688937881870915841 2485734516703411403186881)
                    ·
                      refine ⟨1864300887527558552390161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485734516703411403186881 1864300887527558552390161)
                      ·
                        rfl

theorem cell23_3630713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_3630713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630713 prefixEnd_3630713 := by exact prefixLift 3630713
  have htrace : WordTrace (prefixWord ++ tailWord_3630713) baseStart_3630713 baseEnd_3630713 := by
    simpa [prefixWord, tailWord_3630713, baseEnd_3630713] using wordTrace_append hprefix tailTrace_3630713
  have hstable : (prefixWord ++ tailWord_3630713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630713).length < 2 ^ (prefixWord ++ tailWord_3630713).sum := by decide
  have hdescent : baseEnd_3630713 < baseStart_3630713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630730 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_3630730 : Nat := 118140960795 + 3630730 * 2 ^ 59
def prefixEnd_3630730 : Nat := 4983230072969 + 3 ^ 40 * 3630730 * 2
def baseEnd_3630730 : Nat := 1864309616698684985877583

theorem tailTrace_3630730 : CollatzResearch.WordTrace tailWord_3630730 prefixEnd_3630730 1864309616698684985877583 := by
  unfold tailWord_3630730
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105900534123191040518411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88282401424328509441382429 33105900534123191040518411)
  ·
    refine ⟨49658850801184786560777617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33105900534123191040518411 49658850801184786560777617)
    ·
      refine ⟨37244138100888589920583213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49658850801184786560777617 37244138100888589920583213)
      ·
        refine ⟨13966551787833221220218705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37244138100888589920583213 13966551787833221220218705)
        ·
          refine ⟨10474913840874915915164029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13966551787833221220218705 10474913840874915915164029)
          ·
            refine ⟨3928092690328093468186511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10474913840874915915164029 3928092690328093468186511)
            ·
              refine ⟨5892139035492140202279767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3928092690328093468186511 5892139035492140202279767)
              ·
                refine ⟨8838208553238210303419651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892139035492140202279767 8838208553238210303419651)
                ·
                  refine ⟨13257312829857315455129477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8838208553238210303419651 13257312829857315455129477)
                  ·
                    refine ⟨2485746155598246647836777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13257312829857315455129477 2485746155598246647836777)
                    ·
                      refine ⟨1864309616698684985877583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485746155598246647836777 1864309616698684985877583)
                      ·
                        rfl

theorem cell23_3630730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_3630730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630730 prefixEnd_3630730 := by exact prefixLift 3630730
  have htrace : WordTrace (prefixWord ++ tailWord_3630730) baseStart_3630730 baseEnd_3630730 := by
    simpa [prefixWord, tailWord_3630730, baseEnd_3630730] using wordTrace_append hprefix tailTrace_3630730
  have hstable : (prefixWord ++ tailWord_3630730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630730).length < 2 ^ (prefixWord ++ tailWord_3630730).sum := by decide
  have hdescent : baseEnd_3630730 < baseStart_3630730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630753 : List Nat := [1, 2, 3, 3, 2, 1, 3, 3, 5]
def baseStart_3630753 : Nat := 118140960795 + 3630753 * 2 ^ 59
def prefixEnd_3630753 : Nat := 4983230072969 + 3 ^ 40 * 3630753 * 2
def baseEnd_3630753 : Nat := 207146825194859821765553

theorem tailTrace_3630753 : CollatzResearch.WordTrace tailWord_3630753 prefixEnd_3630753 207146825194859821765553 := by
  unfold tailWord_3630753
  simp only [CollatzResearch.WordTrace]
  refine ⟨132424441015409439090160913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88282960676939626060107275 132424441015409439090160913)
  ·
    refine ⟨99318330761557079317620685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132424441015409439090160913 99318330761557079317620685)
    ·
      refine ⟨37244374035583904744107757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99318330761557079317620685 37244374035583904744107757)
      ·
        refine ⟨13966640263343964279040409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37244374035583904744107757 13966640263343964279040409)
        ·
          refine ⟨10474980197507973209280307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13966640263343964279040409 10474980197507973209280307)
          ·
            refine ⟨15712470296261959813920461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10474980197507973209280307 15712470296261959813920461)
            ·
              refine ⟨5892176361098234930220173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15712470296261959813920461 5892176361098234930220173)
              ·
                refine ⟨2209566135411838098832565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5892176361098234930220173 2209566135411838098832565)
                ·
                  refine ⟨207146825194859821765553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209566135411838098832565 207146825194859821765553)
                  ·
                    rfl

theorem cell23_3630753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 5].length) (baseStart_3630753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630753 prefixEnd_3630753 := by exact prefixLift 3630753
  have htrace : WordTrace (prefixWord ++ tailWord_3630753) baseStart_3630753 baseEnd_3630753 := by
    simpa [prefixWord, tailWord_3630753, baseEnd_3630753] using wordTrace_append hprefix tailTrace_3630753
  have hstable : (prefixWord ++ tailWord_3630753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630753).length < 2 ^ (prefixWord ++ tailWord_3630753).sum := by decide
  have hdescent : baseEnd_3630753 < baseStart_3630753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630799 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_3630799 : Nat := 118140960795 + 3630799 * 2 ^ 59
def prefixEnd_3630799 : Nat := 4983230072969 + 3 ^ 40 * 3630799 * 2
def baseEnd_3630799 : Nat := 1864345046863845215914765

theorem tailTrace_3630799 : CollatzResearch.WordTrace tailWord_3630799 prefixEnd_3630799 1864345046863845215914765 := by
  unfold tailWord_3630799
  simp only [CollatzResearch.WordTrace]
  refine ⟨132426118773242788946335451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88284079182161859297556967 132426118773242788946335451)
  ·
    refine ⟨198639178159864183419503177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132426118773242788946335451 198639178159864183419503177)
    ·
      refine ⟨148979383619898137564627383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198639178159864183419503177 148979383619898137564627383)
      ·
        refine ⟨223469075429847206346941075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148979383619898137564627383 223469075429847206346941075)
        ·
          refine ⟨335203613144770809520411613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223469075429847206346941075 335203613144770809520411613)
          ·
            refine ⟨125701354929289053570154355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335203613144770809520411613 125701354929289053570154355)
            ·
              refine ⟨188552032393933580355231533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125701354929289053570154355 188552032393933580355231533)
              ·
                refine ⟨70707012147725092633211825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188552032393933580355231533 70707012147725092633211825)
                ·
                  refine ⟨53030259110793819474908869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70707012147725092633211825 53030259110793819474908869)
                  ·
                    refine ⟨9943173583273841151545413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53030259110793819474908869 9943173583273841151545413)
                    ·
                      refine ⟨1864345046863845215914765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9943173583273841151545413 1864345046863845215914765)
                      ·
                        rfl

theorem cell23_3630799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_3630799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630799 prefixEnd_3630799 := by exact prefixLift 3630799
  have htrace : WordTrace (prefixWord ++ tailWord_3630799) baseStart_3630799 baseEnd_3630799 := by
    simpa [prefixWord, tailWord_3630799, baseEnd_3630799] using wordTrace_append hprefix tailTrace_3630799
  have hstable : (prefixWord ++ tailWord_3630799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630799).length < 2 ^ (prefixWord ++ tailWord_3630799).sum := by decide
  have hdescent : baseEnd_3630799 < baseStart_3630799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630826 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 6]
def baseStart_3630826 : Nat := 118140960795 + 3630826 * 2 ^ 59
def prefixEnd_3630826 : Nat := 4983230072969 + 3 ^ 40 * 3630826 * 2
def baseEnd_3630826 : Nat := 207150990093501845586349

theorem tailTrace_3630826 : CollatzResearch.WordTrace tailWord_3630826 prefixEnd_3630826 207150990093501845586349 := by
  unfold tailWord_3630826
  simp only [CollatzResearch.WordTrace]
  refine ⟨33106775886036243139392083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88284735696096648371712221 33106775886036243139392083)
  ·
    refine ⟨49660163829054364709088125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33106775886036243139392083 49660163829054364709088125)
    ·
      refine ⟨18622561435895386765908047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49660163829054364709088125 18622561435895386765908047)
      ·
        refine ⟨27933842153843080148862071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18622561435895386765908047 27933842153843080148862071)
        ·
          refine ⟨41900763230764620223293107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27933842153843080148862071 41900763230764620223293107)
          ·
            refine ⟨62851144846146930334939661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41900763230764620223293107 62851144846146930334939661)
            ·
              refine ⟨23569179317305098875602373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62851144846146930334939661 23569179317305098875602373)
              ·
                refine ⟨4419221121994706039175445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23569179317305098875602373 4419221121994706039175445)
                ·
                  refine ⟨207150990093501845586349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4419221121994706039175445 207150990093501845586349)
                  ·
                    rfl

theorem cell23_3630826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_3630826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630826 prefixEnd_3630826 := by exact prefixLift 3630826
  have htrace : WordTrace (prefixWord ++ tailWord_3630826) baseStart_3630826 baseEnd_3630826 := by
    simpa [prefixWord, tailWord_3630826, baseEnd_3630826] using wordTrace_append hprefix tailTrace_3630826
  have hstable : (prefixWord ++ tailWord_3630826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630826).length < 2 ^ (prefixWord ++ tailWord_3630826).sum := by decide
  have hdescent : baseEnd_3630826 < baseStart_3630826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630830 : List Nat := [4, 1, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3630830 : Nat := 118140960795 + 3630830 * 2 ^ 59
def prefixEnd_3630830 : Nat := 4983230072969 + 3 ^ 40 * 3630830 * 2
def baseEnd_3630830 : Nat := 621453654921378198209041

theorem tailTrace_3630830 : CollatzResearch.WordTrace tailWord_3630830 prefixEnd_3630830 621453654921378198209041 := by
  unfold tailWord_3630830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553406179516310155089243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88284832957420320827142629 16553406179516310155089243)
  ·
    refine ⟨24830109269274465232633865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16553406179516310155089243 24830109269274465232633865)
    ·
      refine ⟨18622581951955848924475399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24830109269274465232633865 18622581951955848924475399)
      ·
        refine ⟨27933872927933773386713099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18622581951955848924475399 27933872927933773386713099)
        ·
          refine ⟨41900809391900660080069649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27933872927933773386713099 41900809391900660080069649)
          ·
            refine ⟨31425607043925495060052237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41900809391900660080069649 31425607043925495060052237)
            ·
              refine ⟨11784602641472060647519589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31425607043925495060052237 11784602641472060647519589)
              ·
                refine ⟨2209612995276011371409923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11784602641472060647519589 2209612995276011371409923)
                ·
                  refine ⟨3314419492914017057114885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2209612995276011371409923 3314419492914017057114885)
                  ·
                    refine ⟨621453654921378198209041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3314419492914017057114885 621453654921378198209041)
                    ·
                      rfl

theorem cell23_3630830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3630830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630830 prefixEnd_3630830 := by exact prefixLift 3630830
  have htrace : WordTrace (prefixWord ++ tailWord_3630830) baseStart_3630830 baseEnd_3630830 := by
    simpa [prefixWord, tailWord_3630830, baseEnd_3630830] using wordTrace_append hprefix tailTrace_3630830
  have hstable : (prefixWord ++ tailWord_3630830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630830).length < 2 ^ (prefixWord ++ tailWord_3630830).sum := by decide
  have hdescent : baseEnd_3630830 < baseStart_3630830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630856 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 3, 5]
def baseStart_3630856 : Nat := 118140960795 + 3630856 * 2 ^ 59
def prefixEnd_3630856 : Nat := 4983230072969 + 3 ^ 40 * 3630856 * 2
def baseEnd_3630856 : Nat := 621458105087050497634001

theorem tailTrace_3630856 : CollatzResearch.WordTrace tailWord_3630856 prefixEnd_3630856 621458105087050497634001 := by
  unfold tailWord_3630856
  simp only [CollatzResearch.WordTrace]
  refine ⟨66214098867018143840580211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88285465156024191787440281 66214098867018143840580211)
  ·
    refine ⟨99321148300527215760870317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66214098867018143840580211 99321148300527215760870317)
    ·
      refine ⟨37245430612697705910326369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99321148300527215760870317 37245430612697705910326369)
      ·
        refine ⟨27934072959523279432744777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37245430612697705910326369 27934072959523279432744777)
        ·
          refine ⟨20950554719642459574558583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27934072959523279432744777 20950554719642459574558583)
          ·
            refine ⟨31425832079463689361837875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20950554719642459574558583 31425832079463689361837875)
            ·
              refine ⟨47138748119195534042756813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31425832079463689361837875 47138748119195534042756813)
              ·
                refine ⟨17677030544698325266033805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47138748119195534042756813 17677030544698325266033805)
                ·
                  refine ⟨6628886454261871974762677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17677030544698325266033805 6628886454261871974762677)
                  ·
                    refine ⟨621458105087050497634001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6628886454261871974762677 621458105087050497634001)
                    ·
                      rfl

theorem cell23_3630856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_3630856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630856 prefixEnd_3630856 := by exact prefixLift 3630856
  have htrace : WordTrace (prefixWord ++ tailWord_3630856) baseStart_3630856 baseEnd_3630856 := by
    simpa [prefixWord, tailWord_3630856, baseEnd_3630856] using wordTrace_append hprefix tailTrace_3630856
  have hstable : (prefixWord ++ tailWord_3630856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630856).length < 2 ^ (prefixWord ++ tailWord_3630856).sum := by decide
  have hdescent : baseEnd_3630856 < baseStart_3630856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630863 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 2, 3, 2]
def baseStart_3630863 : Nat := 118140960795 + 3630863 * 2 ^ 59
def prefixEnd_3630863 : Nat := 4983230072969 + 3 ^ 40 * 3630863 * 2
def baseEnd_3630863 : Nat := 1864377909625732965514471

theorem tailTrace_3630863 : CollatzResearch.WordTrace tailWord_3630863 prefixEnd_3630863 1864377909625732965514471 := by
  unfold tailWord_3630863
  simp only [CollatzResearch.WordTrace]
  refine ⟨132428453045010927876665243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88285635363340618584443495 132428453045010927876665243)
  ·
    refine ⟨198642679567516391814997865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132428453045010927876665243 198642679567516391814997865)
    ·
      refine ⟨148982009675637293861248399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198642679567516391814997865 148982009675637293861248399)
      ·
        refine ⟨223473014513455940791872599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148982009675637293861248399 223473014513455940791872599)
        ·
          refine ⟨335209521770183911187808899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223473014513455940791872599 335209521770183911187808899)
          ·
            refine ⟨502814282655275866781713349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335209521770183911187808899 502814282655275866781713349)
            ·
              refine ⟨94277677997864225021571253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502814282655275866781713349 94277677997864225021571253)
              ·
                refine ⟨8838532312299771095772305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94277677997864225021571253 8838532312299771095772305)
                ·
                  refine ⟨6628899234224828321829229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838532312299771095772305 6628899234224828321829229)
                  ·
                    refine ⟨2485837212834310620685961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6628899234224828321829229 2485837212834310620685961)
                    ·
                      refine ⟨1864377909625732965514471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485837212834310620685961 1864377909625732965514471)
                      ·
                        rfl

theorem cell23_3630863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3, 2].length) (baseStart_3630863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630863 prefixEnd_3630863 := by exact prefixLift 3630863
  have htrace : WordTrace (prefixWord ++ tailWord_3630863) baseStart_3630863 baseEnd_3630863 := by
    simpa [prefixWord, tailWord_3630863, baseEnd_3630863] using wordTrace_append hprefix tailTrace_3630863
  have hstable : (prefixWord ++ tailWord_3630863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630863).length < 2 ^ (prefixWord ++ tailWord_3630863).sum := by decide
  have hdescent : baseEnd_3630863 < baseStart_3630863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630910 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3630910 : Nat := 118140960795 + 3630910 * 2 ^ 59
def prefixEnd_3630910 : Nat := 4983230072969 + 3 ^ 40 * 3630910 * 2
def baseEnd_3630910 : Nat := 1864402043216494281626755

theorem tailTrace_3630910 : CollatzResearch.WordTrace tailWord_3630910 prefixEnd_3630910 1864402043216494281626755 := by
  unfold tailWord_3630910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553770909480081862953273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88286778183893769935750789 16553770909480081862953273)
  ·
    refine ⟨12415328182110061397214955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16553770909480081862953273 12415328182110061397214955)
    ·
      refine ⟨18622992273165092095822433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12415328182110061397214955 18622992273165092095822433)
      ·
        refine ⟨13967244204873819071866825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18622992273165092095822433 13967244204873819071866825)
        ·
          refine ⟨10475433153655364303900119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13967244204873819071866825 10475433153655364303900119)
          ·
            refine ⟨15713149730483046455850179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10475433153655364303900119 15713149730483046455850179)
            ·
              refine ⟨23569724595724569683775269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15713149730483046455850179 23569724595724569683775269)
              ·
                refine ⟨4419323361698356815707863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23569724595724569683775269 4419323361698356815707863)
                ·
                  refine ⟨6628985042547535223561795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419323361698356815707863 6628985042547535223561795)
                  ·
                    refine ⟨9943477563821302835342693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6628985042547535223561795 9943477563821302835342693)
                    ·
                      refine ⟨1864402043216494281626755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9943477563821302835342693 1864402043216494281626755)
                      ·
                        rfl

theorem cell23_3630910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3630910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630910 prefixEnd_3630910 := by exact prefixLift 3630910
  have htrace : WordTrace (prefixWord ++ tailWord_3630910) baseStart_3630910 baseEnd_3630910 := by
    simpa [prefixWord, tailWord_3630910, baseEnd_3630910] using wordTrace_append hprefix tailTrace_3630910
  have hstable : (prefixWord ++ tailWord_3630910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630910).length < 2 ^ (prefixWord ++ tailWord_3630910).sum := by decide
  have hdescent : baseEnd_3630910 < baseStart_3630910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630930 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3630930 : Nat := 118140960795 + 3630930 * 2 ^ 59
def prefixEnd_3630930 : Nat := 4983230072969 + 3 ^ 40 * 3630930 * 2
def baseEnd_3630930 : Nat := 1864412312829584203376663

theorem tailTrace_3630930 : CollatzResearch.WordTrace tailWord_3630930 prefixEnd_3630930 1864412312829584203376663 := by
  unfold tailWord_3630930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33107724183942049579838561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88287264490512132212902829 33107724183942049579838561)
  ·
    refine ⟨24830793137956537184878921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33107724183942049579838561 24830793137956537184878921)
    ·
      refine ⟨18623094853467402888659191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24830793137956537184878921 18623094853467402888659191)
      ·
        refine ⟨27934642280201104332988787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18623094853467402888659191 27934642280201104332988787)
        ·
          refine ⟨41901963420301656499483181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27934642280201104332988787 41901963420301656499483181)
          ·
            refine ⟨15713236282613121187306193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41901963420301656499483181 15713236282613121187306193)
            ·
              refine ⟨11784927211959840890479645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15713236282613121187306193 11784927211959840890479645)
              ·
                refine ⟨4419347704484940333929867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11784927211959840890479645 4419347704484940333929867)
                ·
                  refine ⟨6629021556727410500894801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419347704484940333929867 6629021556727410500894801)
                  ·
                    refine ⟨4971766167545557875671101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6629021556727410500894801 4971766167545557875671101)
                    ·
                      refine ⟨1864412312829584203376663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4971766167545557875671101 1864412312829584203376663)
                      ·
                        rfl

theorem cell23_3630930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3630930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630930 prefixEnd_3630930 := by exact prefixLift 3630930
  have htrace : WordTrace (prefixWord ++ tailWord_3630930) baseStart_3630930 baseEnd_3630930 := by
    simpa [prefixWord, tailWord_3630930, baseEnd_3630930] using wordTrace_append hprefix tailTrace_3630930
  have hstable : (prefixWord ++ tailWord_3630930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630930).length < 2 ^ (prefixWord ++ tailWord_3630930).sum := by decide
  have hdescent : baseEnd_3630930 < baseStart_3630930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630977 : List Nat := [1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3630977 : Nat := 118140960795 + 3630977 * 2 ^ 59
def prefixEnd_3630977 : Nat := 4983230072969 + 3 ^ 40 * 3630977 * 2
def baseEnd_3630977 : Nat := 1864436446420345519488947

theorem tailTrace_3630977 : CollatzResearch.WordTrace tailWord_3630977 prefixEnd_3630977 1864436446420345519488947 := by
  unfold tailWord_3630977
  simp only [CollatzResearch.WordTrace]
  refine ⟨132432610966597925346315185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88288407311065283564210123 132432610966597925346315185)
  ·
    refine ⟨99324458224948444009736389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132432610966597925346315185 99324458224948444009736389)
    ·
      refine ⟨18623335917177833251825573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99324458224948444009736389 18623335917177833251825573)
      ·
        refine ⟨3491875484470843734717295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18623335917177833251825573 3491875484470843734717295)
        ·
          refine ⟨5237813226706265602075943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491875484470843734717295 5237813226706265602075943)
          ·
            refine ⟨7856719840059398403113915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237813226706265602075943 7856719840059398403113915)
            ·
              refine ⟨11785079760089097604670873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856719840059398403113915 11785079760089097604670873)
              ·
                refine ⟨8838809820066823203503155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11785079760089097604670873 8838809820066823203503155)
                ·
                  refine ⟨13258214730100234805254733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8838809820066823203503155 13258214730100234805254733)
                  ·
                    refine ⟨4971830523787588051970525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13258214730100234805254733 4971830523787588051970525)
                    ·
                      refine ⟨1864436446420345519488947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4971830523787588051970525 1864436446420345519488947)
                      ·
                        rfl

theorem cell23_3630977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3630977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630977 prefixEnd_3630977 := by exact prefixLift 3630977
  have htrace : WordTrace (prefixWord ++ tailWord_3630977) baseStart_3630977 baseEnd_3630977 := by
    simpa [prefixWord, tailWord_3630977, baseEnd_3630977] using wordTrace_append hprefix tailTrace_3630977
  have hstable : (prefixWord ++ tailWord_3630977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630977).length < 2 ^ (prefixWord ++ tailWord_3630977).sum := by decide
  have hdescent : baseEnd_3630977 < baseStart_3630977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3630994 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_3630994 : Nat := 118140960795 + 3630994 * 2 ^ 59
def prefixEnd_3630994 : Nat := 4983230072969 + 3 ^ 40 * 3630994 * 2
def baseEnd_3630994 : Nat := 1864445175591471952976369

theorem tailTrace_3630994 : CollatzResearch.WordTrace tailWord_3630994 prefixEnd_3630994 1864445175591471952976369 := by
  unfold tailWord_3630994
  simp only [CollatzResearch.WordTrace]
  refine ⟨33108307751884084312421009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88288820671690891499789357 33108307751884084312421009)
  ·
    refine ⟨24831230813913063234315757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33108307751884084312421009 24831230813913063234315757)
    ·
      refine ⟨9311711555217398712868409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24831230813913063234315757 9311711555217398712868409)
      ·
        refine ⟨6983783666413049034651307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9311711555217398712868409 6983783666413049034651307)
        ·
          refine ⟨10475675499619573551976961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6983783666413049034651307 10475675499619573551976961)
          ·
            refine ⟨7856756624714680163982721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10475675499619573551976961 7856756624714680163982721)
            ·
              refine ⟨5892567468536010122987041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7856756624714680163982721 5892567468536010122987041)
              ·
                refine ⟨4419425601402007592240281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5892567468536010122987041 4419425601402007592240281)
                ·
                  refine ⟨3314569201051505694180211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4419425601402007592240281 3314569201051505694180211)
                  ·
                    refine ⟨4971853801577258541270317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3314569201051505694180211 4971853801577258541270317)
                    ·
                      refine ⟨1864445175591471952976369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4971853801577258541270317 1864445175591471952976369)
                      ·
                        rfl

theorem cell23_3630994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_3630994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3630994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3630994 prefixEnd_3630994 := by exact prefixLift 3630994
  have htrace : WordTrace (prefixWord ++ tailWord_3630994) baseStart_3630994 baseEnd_3630994 := by
    simpa [prefixWord, tailWord_3630994, baseEnd_3630994] using wordTrace_append hprefix tailTrace_3630994
  have hstable : (prefixWord ++ tailWord_3630994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3630994).length < 2 ^ (prefixWord ++ tailWord_3630994).sum := by decide
  have hdescent : baseEnd_3630994 < baseStart_3630994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3630994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631010 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3631010 : Nat := 118140960795 + 3631010 * 2 ^ 59
def prefixEnd_3631010 : Nat := 4983230072969 + 3 ^ 40 * 3631010 * 2
def baseEnd_3631010 : Nat := 621484463760647963458765

theorem tailTrace_3631010 : CollatzResearch.WordTrace tailWord_3631010 prefixEnd_3631010 621484463760647963458765 := by
  unfold tailWord_3631010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33108453643869592995566621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88289209716985581321510989 33108453643869592995566621)
  ·
    refine ⟨12415670116451097373337483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33108453643869592995566621 12415670116451097373337483)
    ·
      refine ⟨18623505174676646060006225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12415670116451097373337483 18623505174676646060006225)
      ·
        refine ⟨13967628881007484545004669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18623505174676646060006225 13967628881007484545004669)
        ·
          refine ⟨5237860830377806704376751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13967628881007484545004669 5237860830377806704376751)
          ·
            refine ⟨7856791245566710056565127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237860830377806704376751 7856791245566710056565127)
            ·
              refine ⟨11785186868350065084847691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856791245566710056565127 11785186868350065084847691)
              ·
                refine ⟨17677780302525097627271537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11785186868350065084847691 17677780302525097627271537)
                ·
                  refine ⟨13258335226893823220453653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17677780302525097627271537 13258335226893823220453653)
                  ·
                    refine ⟨621484463760647963458765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13258335226893823220453653 621484463760647963458765)
                    ·
                      rfl

theorem cell23_3631010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3631010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631010 prefixEnd_3631010 := by exact prefixLift 3631010
  have htrace : WordTrace (prefixWord ++ tailWord_3631010) baseStart_3631010 baseEnd_3631010 := by
    simpa [prefixWord, tailWord_3631010, baseEnd_3631010] using wordTrace_append hprefix tailTrace_3631010
  have hstable : (prefixWord ++ tailWord_3631010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631010).length < 2 ^ (prefixWord ++ tailWord_3631010).sum := by decide
  have hdescent : baseEnd_3631010 < baseStart_3631010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631033 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3631033 : Nat := 118140960795 + 3631033 * 2 ^ 59
def prefixEnd_3631033 : Nat := 4983230072969 + 3 ^ 40 * 3631033 * 2
def baseEnd_3631033 : Nat := 1864465201336997300388689

theorem tailTrace_3631033 : CollatzResearch.WordTrace tailWord_3631033 prefixEnd_3631033 1864465201336997300388689 := by
  unfold tailWord_3631033
  simp only [CollatzResearch.WordTrace]
  refine ⟨132434653454395046910353753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88289768969596697940235835 132434653454395046910353753)
  ·
    refine ⟨99325990090796285182765315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132434653454395046910353753 99325990090796285182765315)
    ·
      refine ⟨148988985136194427774147973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99325990090796285182765315 148988985136194427774147973)
      ·
        refine ⟨27935434713036455207652745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148988985136194427774147973 27935434713036455207652745)
        ·
          refine ⟨20951576034777341405739559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27935434713036455207652745 20951576034777341405739559)
          ·
            refine ⟨31427364052166012108609339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20951576034777341405739559 31427364052166012108609339)
            ·
              refine ⟨47141046078249018162914009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31427364052166012108609339 47141046078249018162914009)
              ·
                refine ⟨35355784558686763622185507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47141046078249018162914009 35355784558686763622185507)
                ·
                  refine ⟨53033676838030145433278261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35355784558686763622185507 53033676838030145433278261)
                  ·
                    refine ⟨4971907203565326134369837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53033676838030145433278261 4971907203565326134369837)
                    ·
                      refine ⟨1864465201336997300388689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4971907203565326134369837 1864465201336997300388689)
                      ·
                        rfl

theorem cell23_3631033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3631033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631033 prefixEnd_3631033 := by exact prefixLift 3631033
  have htrace : WordTrace (prefixWord ++ tailWord_3631033) baseStart_3631033 baseEnd_3631033 := by
    simpa [prefixWord, tailWord_3631033, baseEnd_3631033] using wordTrace_append hprefix tailTrace_3631033
  have hstable : (prefixWord ++ tailWord_3631033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631033).length < 2 ^ (prefixWord ++ tailWord_3631033).sum := by decide
  have hdescent : baseEnd_3631033 < baseStart_3631033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631040 : List Nat := [2, 1, 1, 2, 3, 2, 4, 3, 5]
def baseStart_3631040 : Nat := 118140960795 + 3631040 * 2 ^ 59
def prefixEnd_3631040 : Nat := 4983230072969 + 3 ^ 40 * 3631040 * 2
def baseEnd_3631040 : Nat := 207163199522397641444573

theorem tailTrace_3631040 : CollatzResearch.WordTrace tailWord_3631040 prefixEnd_3631040 207163199522397641444573 := by
  unfold tailWord_3631040
  simp only [CollatzResearch.WordTrace]
  refine ⟨66217454382684843552929287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88289939176913124737239049 66217454382684843552929287)
  ·
    refine ⟨99326181574027265329393931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66217454382684843552929287 99326181574027265329393931)
    ·
      refine ⟨148989272361040897994090897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99326181574027265329393931 148989272361040897994090897)
      ·
        refine ⟨111741954270780673495568173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148989272361040897994090897 111741954270780673495568173)
        ·
          refine ⟨41903232851542752560838065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111741954270780673495568173 41903232851542752560838065)
          ·
            refine ⟨31427424638657064420628549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41903232851542752560838065 31427424638657064420628549)
            ·
              refine ⟨5892642119748199578867853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31427424638657064420628549 5892642119748199578867853)
              ·
                refine ⟨2209740794905574842075445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5892642119748199578867853 2209740794905574842075445)
                ·
                  refine ⟨207163199522397641444573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2209740794905574842075445 207163199522397641444573)
                  ·
                    rfl

theorem cell23_3631040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 5].length) (baseStart_3631040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631040 prefixEnd_3631040 := by exact prefixLift 3631040
  have htrace : WordTrace (prefixWord ++ tailWord_3631040) baseStart_3631040 baseEnd_3631040 := by
    simpa [prefixWord, tailWord_3631040, baseEnd_3631040] using wordTrace_append hprefix tailTrace_3631040
  have hstable : (prefixWord ++ tailWord_3631040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631040).length < 2 ^ (prefixWord ++ tailWord_3631040).sum := by decide
  have hdescent : baseEnd_3631040 < baseStart_3631040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631068 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3631068 : Nat := 118140960795 + 3631068 * 2 ^ 59
def prefixEnd_3631068 : Nat := 4983230072969 + 3 ^ 40 * 3631068 * 2
def baseEnd_3631068 : Nat := 1864483173159904663451029

theorem tailTrace_3631068 : CollatzResearch.WordTrace tailWord_3631068 prefixEnd_3631068 1864483173159904663451029 := by
  unfold tailWord_3631068
  simp only [CollatzResearch.WordTrace]
  refine ⟨66217965004634123943938929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88290620006178831925251905 66217965004634123943938929)
  ·
    refine ⟨49663473753475592957954197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66217965004634123943938929 49663473753475592957954197)
    ·
      refine ⟨2327975332194168419904103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49663473753475592957954197 2327975332194168419904103)
      ·
        refine ⟨3491962998291252629856155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327975332194168419904103 3491962998291252629856155)
        ·
          refine ⟨5237944497436878944784233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491962998291252629856155 5237944497436878944784233)
          ·
            refine ⟨3928458373077659208588175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5237944497436878944784233 3928458373077659208588175)
            ·
              refine ⟨5892687559616488812882263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3928458373077659208588175 5892687559616488812882263)
              ·
                refine ⟨8839031339424733219323395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892687559616488812882263 8839031339424733219323395)
                ·
                  refine ⟨13258547009137099828985093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8839031339424733219323395 13258547009137099828985093)
                  ·
                    refine ⟨2485977564213206217934705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13258547009137099828985093 2485977564213206217934705)
                    ·
                      refine ⟨1864483173159904663451029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2485977564213206217934705 1864483173159904663451029)
                      ·
                        rfl

theorem cell23_3631068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3631068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631068 prefixEnd_3631068 := by exact prefixLift 3631068
  have htrace : WordTrace (prefixWord ++ tailWord_3631068) baseStart_3631068 baseEnd_3631068 := by
    simpa [prefixWord, tailWord_3631068, baseEnd_3631068] using wordTrace_append hprefix tailTrace_3631068
  have hstable : (prefixWord ++ tailWord_3631068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631068).length < 2 ^ (prefixWord ++ tailWord_3631068).sum := by decide
  have hdescent : baseEnd_3631068 < baseStart_3631068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631073 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3631073 : Nat := 118140960795 + 3631073 * 2 ^ 59
def prefixEnd_3631073 : Nat := 4983230072969 + 3 ^ 40 * 3631073 * 2
def baseEnd_3631073 : Nat := 1864485740563177143888505

theorem tailTrace_3631073 : CollatzResearch.WordTrace tailWord_3631073 prefixEnd_3631073 1864485740563177143888505 := by
  unfold tailWord_3631073
  simp only [CollatzResearch.WordTrace]
  refine ⟨132436112374250133741809873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88290741582833422494539915 132436112374250133741809873)
  ·
    refine ⟨99327084280687600306357405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132436112374250133741809873 99327084280687600306357405)
    ·
      refine ⟨37247656605257850114884027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99327084280687600306357405 37247656605257850114884027)
      ·
        refine ⟨55871484907886775172326041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37247656605257850114884027 55871484907886775172326041)
        ·
          refine ⟨41903613680915081379244531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55871484907886775172326041 41903613680915081379244531)
          ·
            refine ⟨62855420521372622068866797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41903613680915081379244531 62855420521372622068866797)
            ·
              refine ⟨23570782695514733275825049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62855420521372622068866797 23570782695514733275825049)
              ·
                refine ⟨17678087021636049956868787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23570782695514733275825049 17678087021636049956868787)
                ·
                  refine ⟨26517130532454074935303181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17678087021636049956868787 26517130532454074935303181)
                  ·
                    refine ⟨9943923949670278100738693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26517130532454074935303181 9943923949670278100738693)
                    ·
                      refine ⟨1864485740563177143888505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9943923949670278100738693 1864485740563177143888505)
                      ·
                        rfl

theorem cell23_3631073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3631073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631073 prefixEnd_3631073 := by exact prefixLift 3631073
  have htrace : WordTrace (prefixWord ++ tailWord_3631073) baseStart_3631073 baseEnd_3631073 := by
    simpa [prefixWord, tailWord_3631073, baseEnd_3631073] using wordTrace_append hprefix tailTrace_3631073
  have hstable : (prefixWord ++ tailWord_3631073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631073).length < 2 ^ (prefixWord ++ tailWord_3631073).sum := by decide
  have hdescent : baseEnd_3631073 < baseStart_3631073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631130 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 6]
def baseStart_3631130 : Nat := 118140960795 + 3631130 * 2 ^ 59
def prefixEnd_3631130 : Nat := 4983230072969 + 3 ^ 40 * 3631130 * 2
def baseEnd_3631130 : Nat := 207168334328942602319527

theorem tailTrace_3631130 : CollatzResearch.WordTrace tailWord_3631130 prefixEnd_3631130 207168334328942602319527 := by
  unfold tailWord_3631130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33109547833760908119158711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88292127556695754984423229 33109547833760908119158711)
  ·
    refine ⟨49664321750641362178738067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33109547833760908119158711 49664321750641362178738067)
    ·
      refine ⟨74496482625962043268107101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49664321750641362178738067 74496482625962043268107101)
      ·
        refine ⟨27936180984735766225540163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74496482625962043268107101 27936180984735766225540163)
        ·
          refine ⟨41904271477103649338310245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27936180984735766225540163 41904271477103649338310245)
          ·
            refine ⟨7857050901956934250933171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41904271477103649338310245 7857050901956934250933171)
            ·
              refine ⟨11785576352935401376399757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857050901956934250933171 11785576352935401376399757)
              ·
                refine ⟨4419591132350775516149909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11785576352935401376399757 4419591132350775516149909)
                ·
                  refine ⟨207168334328942602319527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4419591132350775516149909 207168334328942602319527)
                  ·
                    rfl

theorem cell23_3631130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_3631130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631130 prefixEnd_3631130 := by exact prefixLift 3631130
  have htrace : WordTrace (prefixWord ++ tailWord_3631130) baseStart_3631130 baseEnd_3631130 := by
    simpa [prefixWord, tailWord_3631130, baseEnd_3631130] using wordTrace_append hprefix tailTrace_3631130
  have hstable : (prefixWord ++ tailWord_3631130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631130).length < 2 ^ (prefixWord ++ tailWord_3631130).sum := by decide
  have hdescent : baseEnd_3631130 < baseStart_3631130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631167 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 2, 3, 2]
def baseStart_3631167 : Nat := 118140960795 + 3631167 * 2 ^ 59
def prefixEnd_3631167 : Nat := 4983230072969 + 3 ^ 40 * 3631167 * 2
def baseEnd_3631167 : Nat := 1864534007744699776113073

theorem tailTrace_3631167 : CollatzResearch.WordTrace tailWord_3631167 prefixEnd_3631167 1864534007744699776113073 := by
  unfold tailWord_3631167
  simp only [CollatzResearch.WordTrace]
  refine ⟨132439540835909587795731755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88293027223939725197154503 132439540835909587795731755)
  ·
    refine ⟨198659311253864381693597633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132439540835909587795731755 198659311253864381693597633)
    ·
      refine ⟨148994483440398286270198225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198659311253864381693597633 148994483440398286270198225)
      ·
        refine ⟨111745862580298714702648669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148994483440398286270198225 111745862580298714702648669)
        ·
          refine ⟨41904698467612018013493251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111745862580298714702648669 41904698467612018013493251)
          ·
            refine ⟨62857047701418027020239877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41904698467612018013493251 62857047701418027020239877)
            ·
              refine ⟨11785696444015880066294977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62857047701418027020239877 11785696444015880066294977)
              ·
                refine ⟨8839272333011910049721233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11785696444015880066294977 8839272333011910049721233)
                ·
                  refine ⟨6629454249758932537290925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8839272333011910049721233 6629454249758932537290925)
                  ·
                    refine ⟨2486045343659599701484097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6629454249758932537290925 2486045343659599701484097)
                    ·
                      refine ⟨1864534007744699776113073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2486045343659599701484097 1864534007744699776113073)
                      ·
                        rfl

theorem cell23_3631167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 3, 2].length) (baseStart_3631167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631167 prefixEnd_3631167 := by exact prefixLift 3631167
  have htrace : WordTrace (prefixWord ++ tailWord_3631167) baseStart_3631167 baseEnd_3631167 := by
    simpa [prefixWord, tailWord_3631167, baseEnd_3631167] using wordTrace_append hprefix tailTrace_3631167
  have hstable : (prefixWord ++ tailWord_3631167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631167).length < 2 ^ (prefixWord ++ tailWord_3631167).sum := by decide
  have hdescent : baseEnd_3631167 < baseStart_3631167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3631173 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_3631173 : Nat := 118140960795 + 3631173 * 2 ^ 59
def prefixEnd_3631173 : Nat := 4983230072969 + 3 ^ 40 * 3631173 * 2
def baseEnd_3631173 : Nat := 621512362876208917546015

theorem tailTrace_3631173 : CollatzResearch.WordTrace tailWord_3631173 prefixEnd_3631173 621512362876208917546015 := by
  unfold tailWord_3631173
  simp only [CollatzResearch.WordTrace]
  refine ⟨132439759673887850820450173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88293173115925233880300115 132439759673887850820450173)
  ·
    refine ⟨49664909877707944057668815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132439759673887850820450173 49664909877707944057668815)
    ·
      refine ⟨74497364816561916086503223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49664909877707944057668815 74497364816561916086503223)
      ·
        refine ⟨111746047224842874129754835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74497364816561916086503223 111746047224842874129754835)
        ·
          refine ⟨167619070837264311194632253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111746047224842874129754835 167619070837264311194632253)
          ·
            refine ⟨62857151563974116697987095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167619070837264311194632253 62857151563974116697987095)
            ·
              refine ⟨94285727345961175046980643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62857151563974116697987095 94285727345961175046980643)
              ·
                refine ⟨141428591018941762570470965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94285727345961175046980643 141428591018941762570470965)
                ·
                  refine ⟨13258930408025790240981653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141428591018941762570470965 13258930408025790240981653)
                  ·
                    refine ⟨621512362876208917546015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13258930408025790240981653 621512362876208917546015)
                    ·
                      rfl

theorem cell23_3631173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_3631173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3631173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3631173 prefixEnd_3631173 := by exact prefixLift 3631173
  have htrace : WordTrace (prefixWord ++ tailWord_3631173) baseStart_3631173 baseEnd_3631173 := by
    simpa [prefixWord, tailWord_3631173, baseEnd_3631173] using wordTrace_append hprefix tailTrace_3631173
  have hstable : (prefixWord ++ tailWord_3631173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3631173).length < 2 ^ (prefixWord ++ tailWord_3631173).sum := by decide
  have hdescent : baseEnd_3631173 < baseStart_3631173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3631173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
