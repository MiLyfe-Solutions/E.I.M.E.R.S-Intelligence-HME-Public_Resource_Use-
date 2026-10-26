import V185TrunkScan23Chunk1118

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6627836 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_6627836 : Nat := 118140960795 + 6627836 * 2 ^ 59
def prefixEnd_6627836 : Nat := 4983230072969 + 3 ^ 40 * 6627836 * 2
def baseEnd_6627836 : Nat := 3403265567172835794869143

theorem tailTrace_6627836 : CollatzResearch.WordTrace tailWord_6627836 prefixEnd_6627836 3403265567172835794869143 := by
  unfold tailWord_6627836
  simp only [CollatzResearch.WordTrace]
  refine ⟨120868519208244795557611681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161158025610993060743482241 120868519208244795557611681)
  ·
    refine ⟨90651389406183596668208761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120868519208244795557611681 90651389406183596668208761)
    ·
      refine ⟨67988542054637697501156571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90651389406183596668208761 67988542054637697501156571)
      ·
        refine ⟨101982813081956546251734857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67988542054637697501156571 101982813081956546251734857)
        ·
          refine ⟨76487109811467409688801143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101982813081956546251734857 76487109811467409688801143)
          ·
            refine ⟨114730664717201114533201715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76487109811467409688801143 114730664717201114533201715)
            ·
              refine ⟨172095997075801671799802573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114730664717201114533201715 172095997075801671799802573)
              ·
                refine ⟨64535998903425626924925965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172095997075801671799802573 64535998903425626924925965)
                ·
                  refine ⟨24200999588784610096847237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64535998903425626924925965 24200999588784610096847237)
                  ·
                    refine ⟨4537687422897114393158857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24200999588784610096847237 4537687422897114393158857)
                    ·
                      refine ⟨3403265567172835794869143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537687422897114393158857 3403265567172835794869143)
                      ·
                        rfl

theorem cell23_6627836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_6627836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627836 prefixEnd_6627836 := by exact prefixLift 6627836
  have htrace : WordTrace (prefixWord ++ tailWord_6627836) baseStart_6627836 baseEnd_6627836 := by
    simpa [prefixWord, tailWord_6627836, baseEnd_6627836] using wordTrace_append hprefix tailTrace_6627836
  have hstable : (prefixWord ++ tailWord_6627836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627836).length < 2 ^ (prefixWord ++ tailWord_6627836).sum := by decide
  have hdescent : baseEnd_6627836 < baseStart_6627836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627839 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_6627839 : Nat := 118140960795 + 6627839 * 2 ^ 59
def prefixEnd_6627839 : Nat := 4983230072969 + 3 ^ 40 * 6627839 * 2
def baseEnd_6627839 : Nat := 3403267107614799283131629

theorem tailTrace_6627839 : CollatzResearch.WordTrace tailWord_6627839 prefixEnd_6627839 3403267107614799283131629 := by
  unfold tailWord_6627839
  simp only [CollatzResearch.WordTrace]
  refine ⟨241737147835478722627582571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161158098556985815085055047 241737147835478722627582571)
  ·
    refine ⟨362605721753218083941373857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241737147835478722627582571 362605721753218083941373857)
    ·
      refine ⟨271954291314913562956030393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362605721753218083941373857 271954291314913562956030393)
      ·
        refine ⟨203965718486185172217022795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271954291314913562956030393 203965718486185172217022795)
        ·
          refine ⟨305948577729277758325534193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203965718486185172217022795 305948577729277758325534193)
          ·
            refine ⟨229461433296958318744150645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305948577729277758325534193 229461433296958318744150645)
            ·
              refine ⟨21512009371589842382264123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229461433296958318744150645 21512009371589842382264123)
              ·
                refine ⟨32268014057384763573396185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21512009371589842382264123 32268014057384763573396185)
                ·
                  refine ⟨24201010543038572680047139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32268014057384763573396185 24201010543038572680047139)
                  ·
                    refine ⟨36301515814557859020070709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24201010543038572680047139 36301515814557859020070709)
                    ·
                      refine ⟨3403267107614799283131629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36301515814557859020070709 3403267107614799283131629)
                      ·
                        rfl

theorem cell23_6627839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_6627839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627839 prefixEnd_6627839 := by exact prefixLift 6627839
  have htrace : WordTrace (prefixWord ++ tailWord_6627839) baseStart_6627839 baseEnd_6627839 := by
    simpa [prefixWord, tailWord_6627839, baseEnd_6627839] using wordTrace_append hprefix tailTrace_6627839
  have hstable : (prefixWord ++ tailWord_6627839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627839).length < 2 ^ (prefixWord ++ tailWord_6627839).sum := by decide
  have hdescent : baseEnd_6627839 < baseStart_6627839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627849 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_6627849 : Nat := 118140960795 + 6627849 * 2 ^ 59
def prefixEnd_6627849 : Nat := 4983230072969 + 3 ^ 40 * 6627849 * 2
def baseEnd_6627849 : Nat := 3403272242421344244006583

theorem tailTrace_6627849 : CollatzResearch.WordTrace tailWord_6627849 prefixEnd_6627849 3403272242421344244006583 := by
  unfold tailWord_6627849
  simp only [CollatzResearch.WordTrace]
  refine ⟨241737512565442494335446601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161158341710294996223631067 241737512565442494335446601)
  ·
    refine ⟨181303134424081870751584951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241737512565442494335446601 181303134424081870751584951)
    ·
      refine ⟨271954701636122806127377427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181303134424081870751584951 271954701636122806127377427)
      ·
        refine ⟨407932052454184209191066141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271954701636122806127377427 407932052454184209191066141)
        ·
          refine ⟨152974519670319078446649803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407932052454184209191066141 152974519670319078446649803)
          ·
            refine ⟨229461779505478617669974705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152974519670319078446649803 229461779505478617669974705)
            ·
              refine ⟨172096334629108963252481029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229461779505478617669974705 172096334629108963252481029)
              ·
                refine ⟨32268062742957930609840193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172096334629108963252481029 32268062742957930609840193)
                ·
                  refine ⟨24201047057218447957380145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32268062742957930609840193 24201047057218447957380145)
                  ·
                    refine ⟨18150785292913835968035109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24201047057218447957380145 18150785292913835968035109)
                    ·
                      refine ⟨3403272242421344244006583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18150785292913835968035109 3403272242421344244006583)
                      ·
                        rfl

theorem cell23_6627849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_6627849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627849 prefixEnd_6627849 := by exact prefixLift 6627849
  have htrace : WordTrace (prefixWord ++ tailWord_6627849) baseStart_6627849 baseEnd_6627849 := by
    simpa [prefixWord, tailWord_6627849, baseEnd_6627849] using wordTrace_append hprefix tailTrace_6627849
  have hstable : (prefixWord ++ tailWord_6627849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627849).length < 2 ^ (prefixWord ++ tailWord_6627849).sum := by decide
  have hdescent : baseEnd_6627849 < baseStart_6627849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627889 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 1, 7]
def baseStart_6627889 : Nat := 118140960795 + 6627889 * 2 ^ 59
def prefixEnd_6627889 : Nat := 4983230072969 + 3 ^ 40 * 6627889 * 2
def baseEnd_6627889 : Nat := 1134430927215841362502133

theorem tailTrace_6627889 : CollatzResearch.WordTrace tailWord_6627889 prefixEnd_6627889 1134430927215841362502133 := by
  unfold tailWord_6627889
  simp only [CollatzResearch.WordTrace]
  refine ⟨241738971485297581166902721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161159314323531720777935147 241738971485297581166902721)
  ·
    refine ⟨181304228613973185875177041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241738971485297581166902721 181304228613973185875177041)
    ·
      refine ⟨135978171460479889406382781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181304228613973185875177041 135978171460479889406382781)
      ·
        refine ⟨50991814297679958527393543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135978171460479889406382781 50991814297679958527393543)
        ·
          refine ⟨76487721446519937791090315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50991814297679958527393543 76487721446519937791090315)
          ·
            refine ⟨114731582169779906686635473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76487721446519937791090315 114731582169779906686635473)
            ·
              refine ⟨86048686627334930014976605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114731582169779906686635473 86048686627334930014976605)
              ·
                refine ⟨32268257485250598755616227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86048686627334930014976605 32268257485250598755616227)
                ·
                  refine ⟨48402386227875898133424341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32268257485250598755616227 48402386227875898133424341)
                  ·
                    refine ⟨1134430927215841362502133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48402386227875898133424341 1134430927215841362502133)
                    ·
                      rfl

theorem cell23_6627889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_6627889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627889 prefixEnd_6627889 := by exact prefixLift 6627889
  have htrace : WordTrace (prefixWord ++ tailWord_6627889) baseStart_6627889 baseEnd_6627889 := by
    simpa [prefixWord, tailWord_6627889, baseEnd_6627889] using wordTrace_append hprefix tailTrace_6627889
  have hstable : (prefixWord ++ tailWord_6627889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627889).length < 2 ^ (prefixWord ++ tailWord_6627889).sum := by decide
  have hdescent : baseEnd_6627889 < baseStart_6627889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627936 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 5, 4]
def baseStart_6627936 : Nat := 118140960795 + 6627936 * 2 ^ 59
def prefixEnd_6627936 : Nat := 4983230072969 + 3 ^ 40 * 6627936 * 2
def baseEnd_6627936 : Nat := 1134438971746095134539561

theorem tailTrace_6627936 : CollatzResearch.WordTrace tailWord_6627936 prefixEnd_6627936 1134438971746095134539561 := by
  unfold tailWord_6627936
  simp only [CollatzResearch.WordTrace]
  refine ⟨120870342858063654096931831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161160457144084872129242441 120870342858063654096931831)
  ·
    refine ⟨181305514287095481145397747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120870342858063654096931831 181305514287095481145397747)
    ·
      refine ⟨271958271430643221718096621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181305514287095481145397747 271958271430643221718096621)
      ·
        refine ⟨101984351786491208144286233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271958271430643221718096621 101984351786491208144286233)
        ·
          refine ⟨76488263839868406108214675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101984351786491208144286233 76488263839868406108214675)
          ·
            refine ⟨114732395759802609162322013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76488263839868406108214675 114732395759802609162322013)
            ·
              refine ⟨43024648409925978435870755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114732395759802609162322013 43024648409925978435870755)
              ·
                refine ⟨64536972614888967653806133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43024648409925978435870755 64536972614888967653806133)
                ·
                  refine ⟨6050341182645840717544325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64536972614888967653806133 6050341182645840717544325)
                  ·
                    refine ⟨1134438971746095134539561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6050341182645840717544325 1134438971746095134539561)
                    ·
                      rfl

theorem cell23_6627936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_6627936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627936 prefixEnd_6627936 := by exact prefixLift 6627936
  have htrace : WordTrace (prefixWord ++ tailWord_6627936) baseStart_6627936 baseEnd_6627936 := by
    simpa [prefixWord, tailWord_6627936, baseEnd_6627936] using wordTrace_append hprefix tailTrace_6627936
  have hstable : (prefixWord ++ tailWord_6627936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627936).length < 2 ^ (prefixWord ++ tailWord_6627936).sum := by decide
  have hdescent : baseEnd_6627936 < baseStart_6627936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627979 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 9]
def baseStart_6627979 : Nat := 118140960795 + 6627979 * 2 ^ 59
def prefixEnd_6627979 : Nat := 4983230072969 + 3 ^ 40 * 6627979 * 2
def baseEnd_6627979 : Nat := 1134446331635476245126995

theorem tailTrace_6627979 : CollatzResearch.WordTrace tailWord_6627979 prefixEnd_6627979 1134446331635476245126995 := by
  unfold tailWord_6627979
  simp only [CollatzResearch.WordTrace]
  refine ⟨241742254054971526537678991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161161502703314351025119327 241742254054971526537678991)
  ·
    refine ⟨362613381082457289806518487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241742254054971526537678991 362613381082457289806518487)
    ·
      refine ⟨543920071623685934709777731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362613381082457289806518487 543920071623685934709777731)
      ·
        refine ⟨815880107435528902064666597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543920071623685934709777731 815880107435528902064666597)
        ·
          refine ⟨152977520144161669137124987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 815880107435528902064666597 152977520144161669137124987)
          ·
            refine ⟨229466280216242503705687481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152977520144161669137124987 229466280216242503705687481)
            ·
              refine ⟨172099710162181877779265611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229466280216242503705687481 172099710162181877779265611)
              ·
                refine ⟨258149565243272816668898417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172099710162181877779265611 258149565243272816668898417)
                ·
                  refine ⟨193612173932454612501673813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258149565243272816668898417 193612173932454612501673813)
                  ·
                    refine ⟨1134446331635476245126995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193612173932454612501673813 1134446331635476245126995)
                    ·
                      rfl

theorem cell23_6627979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_6627979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627979 prefixEnd_6627979 := by exact prefixLift 6627979
  have htrace : WordTrace (prefixWord ++ tailWord_6627979) baseStart_6627979 baseEnd_6627979 := by
    simpa [prefixWord, tailWord_6627979, baseEnd_6627979] using wordTrace_append hprefix tailTrace_6627979
  have hstable : (prefixWord ++ tailWord_6627979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627979).length < 2 ^ (prefixWord ++ tailWord_6627979).sum := by decide
  have hdescent : baseEnd_6627979 < baseStart_6627979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6627993 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 3]
def baseStart_6627993 : Nat := 118140960795 + 6627993 * 2 ^ 59
def prefixEnd_6627993 : Nat := 4983230072969 + 3 ^ 40 * 6627993 * 2
def baseEnd_6627993 : Nat := 3403346183635591680605921

theorem tailTrace_6627993 : CollatzResearch.WordTrace tailWord_6627993 prefixEnd_6627993 3403346183635591680605921 := by
  unfold tailWord_6627993
  simp only [CollatzResearch.WordTrace]
  refine ⟨241742764676920806928688633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161161843117947204619125755 241742764676920806928688633)
  ·
    refine ⟨181307073507690605196516475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241742764676920806928688633 181307073507690605196516475)
    ·
      refine ⟨271960610261535907794774713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181307073507690605196516475 271960610261535907794774713)
      ·
        refine ⟨203970457696151930846081035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271960610261535907794774713 203970457696151930846081035)
        ·
          refine ⟨305955686544227896269121553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203970457696151930846081035 305955686544227896269121553)
          ·
            refine ⟨229466764908170922201841165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305955686544227896269121553 229466764908170922201841165)
            ·
              refine ⟨86050036840564095825690437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229466764908170922201841165 86050036840564095825690437)
              ·
                refine ⟨16134381907605767967316957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86050036840564095825690437 16134381907605767967316957)
                ·
                  refine ⟨6050393215352162987743859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16134381907605767967316957 6050393215352162987743859)
                  ·
                    refine ⟨9075589823028244481615789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6050393215352162987743859 9075589823028244481615789)
                    ·
                      refine ⟨3403346183635591680605921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9075589823028244481615789 3403346183635591680605921)
                      ·
                        rfl

theorem cell23_6627993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_6627993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6627993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6627993 prefixEnd_6627993 := by exact prefixLift 6627993
  have htrace : WordTrace (prefixWord ++ tailWord_6627993) baseStart_6627993 baseEnd_6627993 := by
    simpa [prefixWord, tailWord_6627993, baseEnd_6627993] using wordTrace_append hprefix tailTrace_6627993
  have hstable : (prefixWord ++ tailWord_6627993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6627993).length < 2 ^ (prefixWord ++ tailWord_6627993).sum := by decide
  have hdescent : baseEnd_6627993 < baseStart_6627993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6627993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628016 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_6628016 : Nat := 118140960795 + 6628016 * 2 ^ 59
def prefixEnd_6628016 : Nat := 4983230072969 + 3 ^ 40 * 6628016 * 2
def baseEnd_6628016 : Nat := 3403357993690645090618315

theorem tailTrace_6628016 : CollatzResearch.WordTrace tailWord_6628016 prefixEnd_6628016 3403357993690645090618315 := by
  unfold tailWord_6628016
  simp only [CollatzResearch.WordTrace]
  refine ⟨120871801777918740928387951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161162402370558321237850601 120871801777918740928387951)
  ·
    refine ⟨181307702666878111392581927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120871801777918740928387951 181307702666878111392581927)
    ·
      refine ⟨271961554000317167088872891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181307702666878111392581927 271961554000317167088872891)
      ·
        refine ⟨407942331000475750633309337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271961554000317167088872891 407942331000475750633309337)
        ·
          refine ⟨305956748250356812974982003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407942331000475750633309337 305956748250356812974982003)
          ·
            refine ⟨458935122375535219462473005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305956748250356812974982003 458935122375535219462473005)
            ·
              refine ⟨172100670890825707298427377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 458935122375535219462473005 172100670890825707298427377)
              ·
                refine ⟨129075503168119280473820533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172100670890825707298427377 129075503168119280473820533)
                ·
                  refine ⟨12100828422011182544420675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129075503168119280473820533 12100828422011182544420675)
                  ·
                    refine ⟨18151242633016773816631013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12100828422011182544420675 18151242633016773816631013)
                    ·
                      refine ⟨3403357993690645090618315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18151242633016773816631013 3403357993690645090618315)
                      ·
                        rfl

theorem cell23_6628016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_6628016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628016 prefixEnd_6628016 := by exact prefixLift 6628016
  have htrace : WordTrace (prefixWord ++ tailWord_6628016) baseStart_6628016 baseEnd_6628016 := by
    simpa [prefixWord, tailWord_6628016, baseEnd_6628016] using wordTrace_append hprefix tailTrace_6628016
  have hstable : (prefixWord ++ tailWord_6628016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628016).length < 2 ^ (prefixWord ++ tailWord_6628016).sum := by decide
  have hdescent : baseEnd_6628016 < baseStart_6628016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628050 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_6628050 : Nat := 118140960795 + 6628050 * 2 ^ 59
def prefixEnd_6628050 : Nat := 4983230072969 + 3 ^ 40 * 6628050 * 2
def baseEnd_6628050 : Nat := 3403375452032897957593159

theorem tailTrace_6628050 : CollatzResearch.WordTrace tailWord_6628050 prefixEnd_6628050 3403375452032897957593159 := by
  unfold tailWord_6628050
  simp only [CollatzResearch.WordTrace]
  refine ⟨60436210909428576415878401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161163229091809537109009069 60436210909428576415878401)
  ·
    refine ⟨45327158182071432311908801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60436210909428576415878401 45327158182071432311908801)
    ·
      refine ⟨33995368636553574233931601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45327158182071432311908801 33995368636553574233931601)
      ·
        refine ⟨25496526477415180675448701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33995368636553574233931601 25496526477415180675448701)
        ·
          refine ⟨9561197429030692753293263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25496526477415180675448701 9561197429030692753293263)
          ·
            refine ⟨14341796143546039129939895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561197429030692753293263 14341796143546039129939895)
            ·
              refine ⟨21512694215319058694909843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14341796143546039129939895 21512694215319058694909843)
              ·
                refine ⟨32269041322978588042364765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21512694215319058694909843 32269041322978588042364765)
                ·
                  refine ⟨12100890496116970515886787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32269041322978588042364765 12100890496116970515886787)
                  ·
                    refine ⟨18151335744175455773830181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12100890496116970515886787 18151335744175455773830181)
                    ·
                      refine ⟨3403375452032897957593159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18151335744175455773830181 3403375452032897957593159)
                      ·
                        rfl

theorem cell23_6628050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_6628050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628050 prefixEnd_6628050 := by exact prefixLift 6628050
  have htrace : WordTrace (prefixWord ++ tailWord_6628050) baseStart_6628050 baseEnd_6628050 := by
    simpa [prefixWord, tailWord_6628050, baseEnd_6628050] using wordTrace_append hprefix tailTrace_6628050
  have hstable : (prefixWord ++ tailWord_6628050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628050).length < 2 ^ (prefixWord ++ tailWord_6628050).sum := by decide
  have hdescent : baseEnd_6628050 < baseStart_6628050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628056 : List Nat := [2, 1, 2, 2, 3, 2, 2, 9]
def baseStart_6628056 : Nat := 118140960795 + 6628056 * 2 ^ 59
def prefixEnd_6628056 : Nat := 4983230072969 + 3 ^ 40 * 6628056 * 2
def baseEnd_6628056 : Nat := 126051056774697219782153

theorem tailTrace_6628056 : CollatzResearch.WordTrace tailWord_6628056 prefixEnd_6628056 126051056774697219782153 := by
  unfold tailWord_6628056
  simp only [CollatzResearch.WordTrace]
  refine ⟨120872531237846284344116011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161163374983795045792154681 120872531237846284344116011)
  ·
    refine ⟨181308796856769426516174017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120872531237846284344116011 181308796856769426516174017)
    ·
      refine ⟨135981597642577069887130513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181308796856769426516174017 135981597642577069887130513)
      ·
        refine ⟨101986198231932802415347885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135981597642577069887130513 101986198231932802415347885)
        ·
          refine ⟨38244824336974800905755457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101986198231932802415347885 38244824336974800905755457)
          ·
            refine ⟨28683618252731100679316593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38244824336974800905755457 28683618252731100679316593)
            ·
              refine ⟨21512713689548325509487445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28683618252731100679316593 21512713689548325509487445)
              ·
                refine ⟨126051056774697219782153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21512713689548325509487445 126051056774697219782153)
                ·
                  rfl

theorem cell23_6628056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 9].length) (baseStart_6628056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628056 prefixEnd_6628056 := by exact prefixLift 6628056
  have htrace : WordTrace (prefixWord ++ tailWord_6628056) baseStart_6628056 baseEnd_6628056 := by
    simpa [prefixWord, tailWord_6628056, baseEnd_6628056] using wordTrace_append hprefix tailTrace_6628056
  have hstable : (prefixWord ++ tailWord_6628056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628056).length < 2 ^ (prefixWord ++ tailWord_6628056).sum := by decide
  have hdescent : baseEnd_6628056 < baseStart_6628056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628060 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6628060 : Nat := 118140960795 + 6628060 * 2 ^ 59
def prefixEnd_6628060 : Nat := 4983230072969 + 3 ^ 40 * 6628060 * 2
def baseEnd_6628060 : Nat := 1134460195613147639489371

theorem tailTrace_6628060 : CollatzResearch.WordTrace tailWord_6628060 prefixEnd_6628060 1134460195613147639489371 := by
  unfold tailWord_6628060
  simp only [CollatzResearch.WordTrace]
  refine ⟨120872604183839038685688817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161163472245118718247585089 120872604183839038685688817)
  ·
    refine ⟨90654453137879279014266613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120872604183839038685688817 90654453137879279014266613)
    ·
      refine ⟨8498854981676182407587495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90654453137879279014266613 8498854981676182407587495)
      ·
        refine ⟨12748282472514273611381243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8498854981676182407587495 12748282472514273611381243)
        ·
          refine ⟨19122423708771410417071865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12748282472514273611381243 19122423708771410417071865)
          ·
            refine ⟨14341817781578557812803899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19122423708771410417071865 14341817781578557812803899)
            ·
              refine ⟨21512726672367836719205849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14341817781578557812803899 21512726672367836719205849)
              ·
                refine ⟨16134545004275877539404387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21512726672367836719205849 16134545004275877539404387)
                ·
                  refine ⟨24201817506413816309106581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16134545004275877539404387 24201817506413816309106581)
                  ·
                    refine ⟨1134460195613147639489371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24201817506413816309106581 1134460195613147639489371)
                    ·
                      rfl

theorem cell23_6628060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6628060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628060 prefixEnd_6628060 := by exact prefixLift 6628060
  have htrace : WordTrace (prefixWord ++ tailWord_6628060) baseStart_6628060 baseEnd_6628060 := by
    simpa [prefixWord, tailWord_6628060, baseEnd_6628060] using wordTrace_append hprefix tailTrace_6628060
  have hstable : (prefixWord ++ tailWord_6628060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628060).length < 2 ^ (prefixWord ++ tailWord_6628060).sum := by decide
  have hdescent : baseEnd_6628060 < baseStart_6628060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628063 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_6628063 : Nat := 118140960795 + 6628063 * 2 ^ 59
def prefixEnd_6628063 : Nat := 4983230072969 + 3 ^ 40 * 6628063 * 2
def baseEnd_6628063 : Nat := 3403382127281406406730599

theorem tailTrace_6628063 : CollatzResearch.WordTrace tailWord_6628063 prefixEnd_6628063 3403382127281406406730599 := by
  unfold tailWord_6628063
  simp only [CollatzResearch.WordTrace]
  refine ⟨241745317786667208883736843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161163545191111472589157895 241745317786667208883736843)
  ·
    refine ⟨362617976680000813325605265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241745317786667208883736843 362617976680000813325605265)
    ·
      refine ⟨271963482510000609994203949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362617976680000813325605265 271963482510000609994203949)
      ·
        refine ⟨101986305941250228747826481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271963482510000609994203949 101986305941250228747826481)
        ·
          refine ⟨76489729455937671560869861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101986305941250228747826481 76489729455937671560869861)
          ·
            refine ⟨14341824272988313417663099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76489729455937671560869861 14341824272988313417663099)
            ·
              refine ⟨21512736409482470126494649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14341824272988313417663099 21512736409482470126494649)
              ·
                refine ⟨16134552307111852594870987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21512736409482470126494649 16134552307111852594870987)
                ·
                  refine ⟨24201828460667778892306481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16134552307111852594870987 24201828460667778892306481)
                  ·
                    refine ⟨18151371345500834169229861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24201828460667778892306481 18151371345500834169229861)
                    ·
                      refine ⟨3403382127281406406730599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18151371345500834169229861 3403382127281406406730599)
                      ·
                        rfl

theorem cell23_6628063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_6628063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628063 prefixEnd_6628063 := by exact prefixLift 6628063
  have htrace : WordTrace (prefixWord ++ tailWord_6628063) baseStart_6628063 baseEnd_6628063 := by
    simpa [prefixWord, tailWord_6628063, baseEnd_6628063] using wordTrace_append hprefix tailTrace_6628063
  have hstable : (prefixWord ++ tailWord_6628063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628063).length < 2 ^ (prefixWord ++ tailWord_6628063).sum := by decide
  have hdescent : baseEnd_6628063 < baseStart_6628063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628067 : List Nat := [1, 1, 1, 7, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6628067 : Nat := 118140960795 + 6628067 * 2 ^ 59
def prefixEnd_6628067 : Nat := 4983230072969 + 3 ^ 40 * 6628067 * 2
def baseEnd_6628067 : Nat := 3403384181204024391080581

theorem tailTrace_6628067 : CollatzResearch.WordTrace tailWord_6628067 prefixEnd_6628067 3403384181204024391080581 := by
  unfold tailWord_6628067
  simp only [CollatzResearch.WordTrace]
  refine ⟨241745463678652717566882455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161163642452435145044588303 241745463678652717566882455)
  ·
    refine ⟨362618195517979076350323683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241745463678652717566882455 362618195517979076350323683)
    ·
      refine ⟨543927293276968614525485525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362618195517979076350323683 543927293276968614525485525)
      ·
        refine ⟨12748295936178951902941067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 543927293276968614525485525 12748295936178951902941067)
        ·
          refine ⟨19122443904268427854411601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12748295936178951902941067 19122443904268427854411601)
          ·
            refine ⟨14341832928201320890808701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19122443904268427854411601 14341832928201320890808701)
            ·
              refine ⟨5378187348075495334053263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14341832928201320890808701 5378187348075495334053263)
              ·
                refine ⟨8067281022113243001079895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5378187348075495334053263 8067281022113243001079895)
                ·
                  refine ⟨12100921533169864501619843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8067281022113243001079895 12100921533169864501619843)
                  ·
                    refine ⟨18151382299754796752429765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12100921533169864501619843 18151382299754796752429765)
                    ·
                      refine ⟨3403384181204024391080581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18151382299754796752429765 3403384181204024391080581)
                      ·
                        rfl

theorem cell23_6628067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6628067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628067 prefixEnd_6628067 := by exact prefixLift 6628067
  have htrace : WordTrace (prefixWord ++ tailWord_6628067) baseStart_6628067 baseEnd_6628067 := by
    simpa [prefixWord, tailWord_6628067, baseEnd_6628067] using wordTrace_append hprefix tailTrace_6628067
  have hstable : (prefixWord ++ tailWord_6628067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628067).length < 2 ^ (prefixWord ++ tailWord_6628067).sum := by decide
  have hdescent : baseEnd_6628067 < baseStart_6628067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628100 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_6628100 : Nat := 118140960795 + 6628100 * 2 ^ 59
def prefixEnd_6628100 : Nat := 4983230072969 + 3 ^ 40 * 6628100 * 2
def baseEnd_6628100 : Nat := 3403401126065622761967929

theorem tailTrace_6628100 : CollatzResearch.WordTrace tailWord_6628100 prefixEnd_6628100 3403401126065622761967929 := by
  unfold tailWord_6628100
  simp only [CollatzResearch.WordTrace]
  refine ⟨120873333643766582101416877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161164444858355442801889169 120873333643766582101416877)
  ·
    refine ⟨45327500116412468288031329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120873333643766582101416877 45327500116412468288031329)
    ·
      refine ⟨33995625087309351216023497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45327500116412468288031329 33995625087309351216023497)
      ·
        refine ⟨25496718815482013412017623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33995625087309351216023497 25496718815482013412017623)
        ·
          refine ⟨38245078223223020118026435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25496718815482013412017623 38245078223223020118026435)
          ·
            refine ⟨57367617334834530177039653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38245078223223020118026435 57367617334834530177039653)
            ·
              refine ⟨10756428250281474408194935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57367617334834530177039653 10756428250281474408194935)
              ·
                refine ⟨16134642375422211612292403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756428250281474408194935 16134642375422211612292403)
                ·
                  refine ⟨24201963563133317418438605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16134642375422211612292403 24201963563133317418438605)
                  ·
                    refine ⟨9075736336174994031914477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24201963563133317418438605 9075736336174994031914477)
                    ·
                      refine ⟨3403401126065622761967929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9075736336174994031914477 3403401126065622761967929)
                      ·
                        rfl

theorem cell23_6628100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_6628100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628100 prefixEnd_6628100 := by exact prefixLift 6628100
  have htrace : WordTrace (prefixWord ++ tailWord_6628100) baseStart_6628100 baseEnd_6628100 := by
    simpa [prefixWord, tailWord_6628100, baseEnd_6628100] using wordTrace_append hprefix tailTrace_6628100
  have hstable : (prefixWord ++ tailWord_6628100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628100).length < 2 ^ (prefixWord ++ tailWord_6628100).sum := by decide
  have hdescent : baseEnd_6628100 < baseStart_6628100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628127 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 1, 3, 2]
def baseStart_6628127 : Nat := 118140960795 + 6628127 * 2 ^ 59
def prefixEnd_6628127 : Nat := 4983230072969 + 3 ^ 40 * 6628127 * 2
def baseEnd_6628127 : Nat := 3403414990043294156330305

theorem tailTrace_6628127 : CollatzResearch.WordTrace tailWord_6628127 prefixEnd_6628127 3403414990043294156330305 := by
  unfold tailWord_6628127
  simp only [CollatzResearch.WordTrace]
  refine ⟨241747652058435347814066635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161165101372290231876044423 241747652058435347814066635)
  ·
    refine ⟨362621478087653021721099953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241747652058435347814066635 362621478087653021721099953)
    ·
      refine ⟨271966108565739766290824965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362621478087653021721099953 271966108565739766290824965)
      ·
        refine ⟨50993645356076206179529681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271966108565739766290824965 50993645356076206179529681)
        ·
          refine ⟨38245234017057154634647261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50993645356076206179529681 38245234017057154634647261)
          ·
            refine ⟨14341962756396432987992723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38245234017057154634647261 14341962756396432987992723)
            ·
              refine ⟨21512944134594649481989085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14341962756396432987992723 21512944134594649481989085)
              ·
                refine ⟨8067354050472993555745907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21512944134594649481989085 8067354050472993555745907)
                ·
                  refine ⟨12101031075709490333618861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8067354050472993555745907 12101031075709490333618861)
                  ·
                    refine ⟨4537886653391058875107073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12101031075709490333618861 4537886653391058875107073)
                    ·
                      refine ⟨3403414990043294156330305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537886653391058875107073 3403414990043294156330305)
                      ·
                        rfl

theorem cell23_6628127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_6628127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628127 prefixEnd_6628127 := by exact prefixLift 6628127
  have htrace : WordTrace (prefixWord ++ tailWord_6628127) baseStart_6628127 baseEnd_6628127 := by
    simpa [prefixWord, tailWord_6628127, baseEnd_6628127] using wordTrace_append hprefix tailTrace_6628127
  have hstable : (prefixWord ++ tailWord_6628127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628127).length < 2 ^ (prefixWord ++ tailWord_6628127).sum := by decide
  have hdescent : baseEnd_6628127 < baseStart_6628127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628161 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6628161 : Nat := 118140960795 + 6628161 * 2 ^ 59
def prefixEnd_6628161 : Nat := 4983230072969 + 3 ^ 40 * 6628161 * 2
def baseEnd_6628161 : Nat := 3403432448385547023305149

theorem tailTrace_6628161 : CollatzResearch.WordTrace tailWord_6628161 prefixEnd_6628161 3403432448385547023305149 := by
  unfold tailWord_6628161
  simp only [CollatzResearch.WordTrace]
  refine ⟨241748892140312171620804337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161165928093541447747202891 241748892140312171620804337)
  ·
    refine ⟨181311669105234128715603253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241748892140312171620804337 181311669105234128715603253)
    ·
      refine ⟨16997968978615699567087805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181311669105234128715603253 16997968978615699567087805)
      ·
        refine ⟨6374238366980887337657927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16997968978615699567087805 6374238366980887337657927)
        ·
          refine ⟨9561357550471331006486891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374238366980887337657927 9561357550471331006486891)
          ·
            refine ⟨14342036325706996509730337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561357550471331006486891 14342036325706996509730337)
            ·
              refine ⟨10756527244280247382297753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14342036325706996509730337 10756527244280247382297753)
              ·
                refine ⟨8067395433210185536723315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10756527244280247382297753 8067395433210185536723315)
                ·
                  refine ⟨12101093149815278305084973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8067395433210185536723315 12101093149815278305084973)
                  ·
                    refine ⟨4537909931180729364406865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12101093149815278305084973 4537909931180729364406865)
                    ·
                      refine ⟨3403432448385547023305149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4537909931180729364406865 3403432448385547023305149)
                      ·
                        rfl

theorem cell23_6628161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6628161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628161 prefixEnd_6628161 := by exact prefixLift 6628161
  have htrace : WordTrace (prefixWord ++ tailWord_6628161) baseStart_6628161 baseEnd_6628161 := by
    simpa [prefixWord, tailWord_6628161, baseEnd_6628161] using wordTrace_append hprefix tailTrace_6628161
  have hstable : (prefixWord ++ tailWord_6628161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628161).length < 2 ^ (prefixWord ++ tailWord_6628161).sum := by decide
  have hdescent : baseEnd_6628161 < baseStart_6628161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628278 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6628278 : Nat := 118140960795 + 6628278 * 2 ^ 59
def prefixEnd_6628278 : Nat := 4983230072969 + 3 ^ 40 * 6628278 * 2
def baseEnd_6628278 : Nat := 1134497508540707688514037

theorem tailTrace_6628278 : CollatzResearch.WordTrace tailWord_6628278 prefixEnd_6628278 1134497508540707688514037 := by
  unfold tailWord_6628278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109572467555518787675843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161168772987258867068542325 15109572467555518787675843)
  ·
    refine ⟨22664358701333278181513765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15109572467555518787675843 22664358701333278181513765)
    ·
      refine ⟨4249567256499989659033831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22664358701333278181513765 4249567256499989659033831)
      ·
        refine ⟨6374350884749984488550747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4249567256499989659033831 6374350884749984488550747)
        ·
          refine ⟨9561526327124976732826121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374350884749984488550747 9561526327124976732826121)
          ·
            refine ⟨7171144745343732549619591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9561526327124976732826121 7171144745343732549619591)
            ·
              refine ⟨10756717118015598824429387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7171144745343732549619591 10756717118015598824429387)
              ·
                refine ⟨16135075677023398236644081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756717118015598824429387 16135075677023398236644081)
                ·
                  refine ⟨12101306757767548677483061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16135075677023398236644081 12101306757767548677483061)
                  ·
                    refine ⟨1134497508540707688514037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12101306757767548677483061 1134497508540707688514037)
                    ·
                      rfl

theorem cell23_6628278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6628278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628278 prefixEnd_6628278 := by exact prefixLift 6628278
  have htrace : WordTrace (prefixWord ++ tailWord_6628278) baseStart_6628278 baseEnd_6628278 := by
    simpa [prefixWord, tailWord_6628278, baseEnd_6628278] using wordTrace_append hprefix tailTrace_6628278
  have hstable : (prefixWord ++ tailWord_6628278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628278).length < 2 ^ (prefixWord ++ tailWord_6628278).sum := by decide
  have hdescent : baseEnd_6628278 < baseStart_6628278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628283 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 7, 5]
def baseStart_6628283 : Nat := 118140960795 + 6628283 * 2 ^ 59
def prefixEnd_6628283 : Nat := 4983230072969 + 3 ^ 40 * 6628283 * 2
def baseEnd_6628283 : Nat := 1134498364341798515326529

theorem tailTrace_6628283 : CollatzResearch.WordTrace tailWord_6628283 prefixEnd_6628283 1134498364341798515326529 := by
  unfold tailWord_6628283
  simp only [CollatzResearch.WordTrace]
  refine ⟨241753341845870186456745503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161168894563913457637830335 241753341845870186456745503)
  ·
    refine ⟨362630012768805279685118255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241753341845870186456745503 362630012768805279685118255)
    ·
      refine ⟨543945019153207919527677383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362630012768805279685118255 543945019153207919527677383)
      ·
        refine ⟨815917528729811879291516075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543945019153207919527677383 815917528729811879291516075)
        ·
          refine ⟨1223876293094717818937274113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815917528729811879291516075 1223876293094717818937274113)
          ·
            refine ⟨917907219821038364202955585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223876293094717818937274113 917907219821038364202955585)
            ·
              refine ⟨688430414865778773152216689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 917907219821038364202955585 688430414865778773152216689)
              ·
                refine ⟨516322811149334079864162517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688430414865778773152216689 516322811149334079864162517)
                ·
                  refine ⟨12101315886312517496816309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 516322811149334079864162517 12101315886312517496816309)
                  ·
                    refine ⟨1134498364341798515326529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12101315886312517496816309 1134498364341798515326529)
                    ·
                      rfl

theorem cell23_6628283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 5].length) (baseStart_6628283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628283 prefixEnd_6628283 := by exact prefixLift 6628283
  have htrace : WordTrace (prefixWord ++ tailWord_6628283) baseStart_6628283 baseEnd_6628283 := by
    simpa [prefixWord, tailWord_6628283, baseEnd_6628283] using wordTrace_append hprefix tailTrace_6628283
  have hstable : (prefixWord ++ tailWord_6628283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628283).length < 2 ^ (prefixWord ++ tailWord_6628283).sum := by decide
  have hdescent : baseEnd_6628283 < baseStart_6628283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628314 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3]
def baseStart_6628314 : Nat := 118140960795 + 6628314 * 2 ^ 59
def prefixEnd_6628314 : Nat := 4983230072969 + 3 ^ 40 * 6628314 * 2
def baseEnd_6628314 : Nat := 3403511010925684924691945

theorem tailTrace_6628314 : CollatzResearch.WordTrace tailWord_6628314 prefixEnd_6628314 3403511010925684924691945 := by
  unfold tailWord_6628314
  simp only [CollatzResearch.WordTrace]
  refine ⟨60438618127189469687780999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161169648339171919167415997 60438618127189469687780999)
  ·
    refine ⟨90657927190784204531671499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60438618127189469687780999 90657927190784204531671499)
    ·
      refine ⟨135986890786176306797507249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90657927190784204531671499 135986890786176306797507249)
      ·
        refine ⟨101990168089632230098130437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135986890786176306797507249 101990168089632230098130437)
        ·
          refine ⟨19123156516806043143399457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101990168089632230098130437 19123156516806043143399457)
          ·
            refine ⟨14342367387604532357549593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19123156516806043143399457 14342367387604532357549593)
            ·
              refine ⟨10756775540703399268162195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14342367387604532357549593 10756775540703399268162195)
              ·
                refine ⟨16135163311055098902243293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756775540703399268162195 16135163311055098902243293)
                ·
                  refine ⟨6050686241645662088341235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16135163311055098902243293 6050686241645662088341235)
                  ·
                    refine ⟨9076029362468493132511853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6050686241645662088341235 9076029362468493132511853)
                    ·
                      refine ⟨3403511010925684924691945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076029362468493132511853 3403511010925684924691945)
                      ·
                        rfl

theorem cell23_6628314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_6628314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628314 prefixEnd_6628314 := by exact prefixLift 6628314
  have htrace : WordTrace (prefixWord ++ tailWord_6628314) baseStart_6628314 baseEnd_6628314 := by
    simpa [prefixWord, tailWord_6628314, baseEnd_6628314] using wordTrace_append hprefix tailTrace_6628314
  have hstable : (prefixWord ++ tailWord_6628314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628314).length < 2 ^ (prefixWord ++ tailWord_6628314).sum := by decide
  have hdescent : baseEnd_6628314 < baseStart_6628314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628334 : List Nat := [4, 1, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_6628334 : Nat := 118140960795 + 6628334 * 2 ^ 59
def prefixEnd_6628334 : Nat := 4983230072969 + 3 ^ 40 * 6628334 * 2
def baseEnd_6628334 : Nat := 1134507093512924948813951

theorem tailTrace_6628334 : CollatzResearch.WordTrace tailWord_6628334 prefixEnd_6628334 1134507093512924948813951 := by
  unfold tailWord_6628334
  simp only [CollatzResearch.WordTrace]
  refine ⟨30219400246085677770856507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161170134645790281444568037 30219400246085677770856507)
  ·
    refine ⟨45329100369128516656284761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30219400246085677770856507 45329100369128516656284761)
    ·
      refine ⟨33996825276846387492213571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45329100369128516656284761 33996825276846387492213571)
      ·
        refine ⟨50995237915269581238320357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33996825276846387492213571 50995237915269581238320357)
        ·
          refine ⟨9561607109113046482185067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50995237915269581238320357 9561607109113046482185067)
          ·
            refine ⟨14342410663669569723277601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561607109113046482185067 14342410663669569723277601)
            ·
              refine ⟨10756807997752177292458201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14342410663669569723277601 10756807997752177292458201)
              ·
                refine ⟨8067605998314132969343651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10756807997752177292458201 8067605998314132969343651)
                ·
                  refine ⟨12101408997471199454015477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8067605998314132969343651 12101408997471199454015477)
                  ·
                    refine ⟨1134507093512924948813951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12101408997471199454015477 1134507093512924948813951)
                    ·
                      rfl

theorem cell23_6628334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_6628334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628334 prefixEnd_6628334 := by exact prefixLift 6628334
  have htrace : WordTrace (prefixWord ++ tailWord_6628334) baseStart_6628334 baseEnd_6628334 := by
    simpa [prefixWord, tailWord_6628334, baseEnd_6628334] using wordTrace_append hprefix tailTrace_6628334
  have hstable : (prefixWord ++ tailWord_6628334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628334).length < 2 ^ (prefixWord ++ tailWord_6628334).sum := by decide
  have hdescent : baseEnd_6628334 < baseStart_6628334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628337 : List Nat := [1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_6628337 : Nat := 118140960795 + 6628337 * 2 ^ 59
def prefixEnd_6628337 : Nat := 4983230072969 + 3 ^ 40 * 6628337 * 2
def baseEnd_6628337 : Nat := 3403522820980738334704339

theorem tailTrace_6628337 : CollatzResearch.WordTrace tailWord_6628337 prefixEnd_6628337 3403522820980738334704339 := by
  unfold tailWord_6628337
  simp only [CollatzResearch.WordTrace]
  refine ⟨241755311387674553679211265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161170207591783035786140843 241755311387674553679211265)
  ·
    refine ⟨181316483540755915259408449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241755311387674553679211265 181316483540755915259408449)
    ·
      refine ⟨135987362655566936444556337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181316483540755915259408449 135987362655566936444556337)
      ·
        refine ⟨101990521991675202333417253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135987362655566936444556337 101990521991675202333417253)
        ·
          refine ⟨19123222873439100437515735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101990521991675202333417253 19123222873439100437515735)
          ·
            refine ⟨28684834310158650656273603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19123222873439100437515735 28684834310158650656273603)
            ·
              refine ⟨43027251465237975984410405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28684834310158650656273603 43027251465237975984410405)
              ·
                refine ⟨8067609649732120497076951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43027251465237975984410405 8067609649732120497076951)
                ·
                  refine ⟨12101414474598180745615427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8067609649732120497076951 12101414474598180745615427)
                  ·
                    refine ⟨18152121711897271118423141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12101414474598180745615427 18152121711897271118423141)
                    ·
                      refine ⟨3403522820980738334704339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18152121711897271118423141 3403522820980738334704339)
                      ·
                        rfl

theorem cell23_6628337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_6628337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628337 prefixEnd_6628337 := by exact prefixLift 6628337
  have htrace : WordTrace (prefixWord ++ tailWord_6628337) baseStart_6628337 baseEnd_6628337 := by
    simpa [prefixWord, tailWord_6628337, baseEnd_6628337] using wordTrace_append hprefix tailTrace_6628337
  have hstable : (prefixWord ++ tailWord_6628337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628337).length < 2 ^ (prefixWord ++ tailWord_6628337).sum := by decide
  have hdescent : baseEnd_6628337 < baseStart_6628337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628357 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_6628357 : Nat := 118140960795 + 6628357 * 2 ^ 59
def prefixEnd_6628357 : Nat := 4983230072969 + 3 ^ 40 * 6628357 * 2
def baseEnd_6628357 : Nat := 3403533090593828256454247

theorem tailTrace_6628357 : CollatzResearch.WordTrace tailWord_6628357 prefixEnd_6628357 3403533090593828256454247 := by
  unfold tailWord_6628357
  simp only [CollatzResearch.WordTrace]
  refine ⟨241756040847602097094939325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161170693898401398063292883 241756040847602097094939325)
  ·
    refine ⟨90658515317850786410602247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241756040847602097094939325 90658515317850786410602247)
    ·
      refine ⟨135987772976776179615903371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90658515317850786410602247 135987772976776179615903371)
      ·
        refine ⟨203981659465164269423855057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135987772976776179615903371 203981659465164269423855057)
        ·
          refine ⟨152986244598873202067891293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203981659465164269423855057 152986244598873202067891293)
          ·
            refine ⟨57369841724577450775459235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152986244598873202067891293 57369841724577450775459235)
            ·
              refine ⟨86054762586866176163188853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57369841724577450775459235 86054762586866176163188853)
              ·
                refine ⟨8067633992518704015298955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86054762586866176163188853 8067633992518704015298955)
                ·
                  refine ⟨12101450988778056022948433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8067633992518704015298955 12101450988778056022948433)
                  ·
                    refine ⟨9076088241583542017211325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12101450988778056022948433 9076088241583542017211325)
                    ·
                      refine ⟨3403533090593828256454247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076088241583542017211325 3403533090593828256454247)
                      ·
                        rfl

theorem cell23_6628357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_6628357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628357 prefixEnd_6628357 := by exact prefixLift 6628357
  have htrace : WordTrace (prefixWord ++ tailWord_6628357) baseStart_6628357 baseEnd_6628357 := by
    simpa [prefixWord, tailWord_6628357, baseEnd_6628357] using wordTrace_append hprefix tailTrace_6628357
  have hstable : (prefixWord ++ tailWord_6628357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628357).length < 2 ^ (prefixWord ++ tailWord_6628357).sum := by decide
  have hdescent : baseEnd_6628357 < baseStart_6628357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628360 : List Nat := [2, 1, 3, 2, 1, 5, 9]
def baseStart_6628360 : Nat := 118140960795 + 6628360 * 2 ^ 59
def prefixEnd_6628360 : Nat := 4983230072969 + 3 ^ 40 * 6628360 * 2
def baseEnd_6628360 : Nat := 42018946062170268453293

theorem tailTrace_6628360 : CollatzResearch.WordTrace tailWord_6628360 prefixEnd_6628360 42018946062170268453293 := by
  unfold tailWord_6628360
  simp only [CollatzResearch.WordTrace]
  refine ⟨120878075133295614303649267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161170766844394152404865689 120878075133295614303649267)
  ·
    refine ⟨181317112699943421455473901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120878075133295614303649267 181317112699943421455473901)
    ·
      refine ⟨67993917262478783045802713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181317112699943421455473901 67993917262478783045802713)
      ·
        refine ⟨50995437946859087284352035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67993917262478783045802713 50995437946859087284352035)
        ·
          refine ⟨76493156920288630926528053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50995437946859087284352035 76493156920288630926528053)
          ·
            refine ⟨7171233461277059149362005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76493156920288630926528053 7171233461277059149362005)
            ·
              refine ⟨42018946062170268453293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7171233461277059149362005 42018946062170268453293)
              ·
                rfl

theorem cell23_6628360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 9].length) (baseStart_6628360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628360 prefixEnd_6628360 := by exact prefixLift 6628360
  have htrace : WordTrace (prefixWord ++ tailWord_6628360) baseStart_6628360 baseEnd_6628360 := by
    simpa [prefixWord, tailWord_6628360, baseEnd_6628360] using wordTrace_append hprefix tailTrace_6628360
  have hstable : (prefixWord ++ tailWord_6628360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628360).length < 2 ^ (prefixWord ++ tailWord_6628360).sum := by decide
  have hdescent : baseEnd_6628360 < baseStart_6628360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628391 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6628391 : Nat := 118140960795 + 6628391 * 2 ^ 59
def prefixEnd_6628391 : Nat := 4983230072969 + 3 ^ 40 * 6628391 * 2
def baseEnd_6628391 : Nat := 3403550548936081123429091

theorem tailTrace_6628391 : CollatzResearch.WordTrace tailWord_6628391 prefixEnd_6628391 3403550548936081123429091 := by
  unfold tailWord_6628391
  simp only [CollatzResearch.WordTrace]
  refine ⟨241757280929478920901677027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161171520619652613934451351 241757280929478920901677027)
  ·
    refine ⟨362635921394218381352515541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241757280929478920901677027 362635921394218381352515541)
    ·
      refine ⟨8499279407676993312949583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 362635921394218381352515541 8499279407676993312949583)
      ·
        refine ⟨12748919111515489969424375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499279407676993312949583 12748919111515489969424375)
        ·
          refine ⟨19123378667273234954136563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12748919111515489969424375 19123378667273234954136563)
          ·
            refine ⟨28685068000909852431204845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19123378667273234954136563 28685068000909852431204845)
            ·
              refine ⟨10756900500341194661701817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28685068000909852431204845 10756900500341194661701817)
              ·
                refine ⟨8067675375255895996276363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10756900500341194661701817 8067675375255895996276363)
                ·
                  refine ⟨12101513062883843994414545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8067675375255895996276363 12101513062883843994414545)
                  ·
                    refine ⟨9076134797162882995810909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12101513062883843994414545 9076134797162882995810909)
                    ·
                      refine ⟨3403550548936081123429091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076134797162882995810909 3403550548936081123429091)
                      ·
                        rfl

theorem cell23_6628391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6628391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628391 prefixEnd_6628391 := by exact prefixLift 6628391
  have htrace : WordTrace (prefixWord ++ tailWord_6628391) baseStart_6628391 baseEnd_6628391 := by
    simpa [prefixWord, tailWord_6628391, baseEnd_6628391] using wordTrace_append hprefix tailTrace_6628391
  have hstable : (prefixWord ++ tailWord_6628391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628391).length < 2 ^ (prefixWord ++ tailWord_6628391).sum := by decide
  have hdescent : baseEnd_6628391 < baseStart_6628391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628404 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6628404 : Nat := 118140960795 + 6628404 * 2 ^ 59
def prefixEnd_6628404 : Nat := 4983230072969 + 3 ^ 40 * 6628404 * 2
def baseEnd_6628404 : Nat := 3403557224184589572566531

theorem tailTrace_6628404 : CollatzResearch.WordTrace tailWord_6628404 prefixEnd_6628404 3403557224184589572566531 := by
  unfold tailWord_6628404
  simp only [CollatzResearch.WordTrace]
  refine ⟨120878877539215912060950133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161171836718954549414600177 120878877539215912060950133)
  ·
    refine ⟨11332394769301491755714075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120878877539215912060950133 11332394769301491755714075)
    ·
      refine ⟨16998592153952237633571113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11332394769301491755714075 16998592153952237633571113)
      ·
        refine ⟨12748944115464178225178335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16998592153952237633571113 12748944115464178225178335)
        ·
          refine ⟨19123416173196267337767503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12748944115464178225178335 19123416173196267337767503)
          ·
            refine ⟨28685124259794401006651255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19123416173196267337767503 28685124259794401006651255)
            ·
              refine ⟨43027686389691601509976883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28685124259794401006651255 43027686389691601509976883)
              ·
                refine ⟨64541529584537402264965325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43027686389691601509976883 64541529584537402264965325)
                ·
                  refine ⟨24203073594201525849361997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64541529584537402264965325 24203073594201525849361997)
                  ·
                    refine ⟨9076152597825572193510749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24203073594201525849361997 9076152597825572193510749)
                    ·
                      refine ⟨3403557224184589572566531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076152597825572193510749 3403557224184589572566531)
                      ·
                        rfl

theorem cell23_6628404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6628404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628404 prefixEnd_6628404 := by exact prefixLift 6628404
  have htrace : WordTrace (prefixWord ++ tailWord_6628404) baseStart_6628404 baseEnd_6628404 := by
    simpa [prefixWord, tailWord_6628404, baseEnd_6628404] using wordTrace_append hprefix tailTrace_6628404
  have hstable : (prefixWord ++ tailWord_6628404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628404).length < 2 ^ (prefixWord ++ tailWord_6628404).sum := by decide
  have hdescent : baseEnd_6628404 < baseStart_6628404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628422 : List Nat := [6, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_6628422 : Nat := 118140960795 + 6628422 * 2 ^ 59
def prefixEnd_6628422 : Nat := 4983230072969 + 3 ^ 40 * 6628422 * 2
def baseEnd_6628422 : Nat := 3403566466836370502141449

theorem tailTrace_6628422 : CollatzResearch.WordTrace tailWord_6628422 prefixEnd_6628422 3403566466836370502141449 := by
  unfold tailWord_6628422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7554950362261456662376735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161172274394911075464037013 7554950362261456662376735)
  ·
    refine ⟨11332425543392184993565103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7554950362261456662376735 11332425543392184993565103)
    ·
      refine ⟨16998638315088277490347655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11332425543392184993565103 16998638315088277490347655)
      ·
        refine ⟨25497957472632416235521483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16998638315088277490347655 25497957472632416235521483)
        ·
          refine ⟨38246936208948624353282225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25497957472632416235521483 38246936208948624353282225)
          ·
            refine ⟨28685202156711468264961669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38246936208948624353282225 28685202156711468264961669)
            ·
              refine ⟨5378475404383400299680313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28685202156711468264961669 5378475404383400299680313)
              ·
                refine ⟨4033856553287550224760235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5378475404383400299680313 4033856553287550224760235)
                ·
                  refine ⟨6050784829931325337140353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033856553287550224760235 6050784829931325337140353)
                  ·
                    refine ⟨4538088622448494002855265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6050784829931325337140353 4538088622448494002855265)
                    ·
                      refine ⟨3403566466836370502141449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538088622448494002855265 3403566466836370502141449)
                      ·
                        rfl

theorem cell23_6628422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_6628422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628422 prefixEnd_6628422 := by exact prefixLift 6628422
  have htrace : WordTrace (prefixWord ++ tailWord_6628422) baseStart_6628422 baseEnd_6628422 := by
    simpa [prefixWord, tailWord_6628422, baseEnd_6628422] using wordTrace_append hprefix tailTrace_6628422
  have hstable : (prefixWord ++ tailWord_6628422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628422).length < 2 ^ (prefixWord ++ tailWord_6628422).sum := by decide
  have hdescent : baseEnd_6628422 < baseStart_6628422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628438 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_6628438 : Nat := 118140960795 + 6628438 * 2 ^ 59
def prefixEnd_6628438 : Nat := 4983230072969 + 3 ^ 40 * 6628438 * 2
def baseEnd_6628438 : Nat := 3403574682526842439541375

theorem tailTrace_6628438 : CollatzResearch.WordTrace tailWord_6628438 prefixEnd_6628438 3403574682526842439541375 := by
  unfold tailWord_6628438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109937197519290495539873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161172663440205765285758645 15109937197519290495539873)
  ·
    refine ⟨11332452898139467871654905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15109937197519290495539873 11332452898139467871654905)
    ·
      refine ⟨8499339673604600903741179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11332452898139467871654905 8499339673604600903741179)
      ·
        refine ⟨12749009510406901355611769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499339673604600903741179 12749009510406901355611769)
        ·
          refine ⟨9561757132805176016708827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12749009510406901355611769 9561757132805176016708827)
          ·
            refine ⟨14342635699207764025063241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561757132805176016708827 14342635699207764025063241)
            ·
              refine ⟨10756976774405823018797431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14342635699207764025063241 10756976774405823018797431)
              ·
                refine ⟨16135465161608734528196147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756976774405823018797431 16135465161608734528196147)
                ·
                  refine ⟨24203197742413101792294221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16135465161608734528196147 24203197742413101792294221)
                  ·
                    refine ⟨9076199153404913172110333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24203197742413101792294221 9076199153404913172110333)
                    ·
                      refine ⟨3403574682526842439541375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076199153404913172110333 3403574682526842439541375)
                      ·
                        rfl

theorem cell23_6628438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_6628438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628438 prefixEnd_6628438 := by exact prefixLift 6628438
  have htrace : WordTrace (prefixWord ++ tailWord_6628438) baseStart_6628438 baseEnd_6628438 := by
    simpa [prefixWord, tailWord_6628438, baseEnd_6628438] using wordTrace_append hprefix tailTrace_6628438
  have hstable : (prefixWord ++ tailWord_6628438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628438).length < 2 ^ (prefixWord ++ tailWord_6628438).sum := by decide
  have hdescent : baseEnd_6628438 < baseStart_6628438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628477 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_6628477 : Nat := 118140960795 + 6628477 * 2 ^ 59
def prefixEnd_6628477 : Nat := 4983230072969 + 3 ^ 40 * 6628477 * 2
def baseEnd_6628477 : Nat := 3403594708272367786953695

theorem tailTrace_6628477 : CollatzResearch.WordTrace tailWord_6628477 prefixEnd_6628477 3403594708272367786953695 := by
  unfold tailWord_6628477
  simp only [CollatzResearch.WordTrace]
  refine ⟨241760417607167357589307685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161173611738111571726205123 241760417607167357589307685)
  ·
    refine ⟨45330078301343879547995191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241760417607167357589307685 45330078301343879547995191)
    ·
      refine ⟨67995117452015819321992787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45330078301343879547995191 67995117452015819321992787)
      ·
        refine ⟨101992676178023728982989181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67995117452015819321992787 101992676178023728982989181)
        ·
          refine ⟨38247253566758898368620943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101992676178023728982989181 38247253566758898368620943)
          ·
            refine ⟨57370880350138347552931415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38247253566758898368620943 57370880350138347552931415)
            ·
              refine ⟨86056320525207521329397123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57370880350138347552931415 86056320525207521329397123)
              ·
                refine ⟨129084480787811281994095685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86056320525207521329397123 129084480787811281994095685)
                ·
                  refine ⟨24203340147714615373892941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129084480787811281994095685 24203340147714615373892941)
                  ·
                    refine ⟨9076252555392980765209853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24203340147714615373892941 9076252555392980765209853)
                    ·
                      refine ⟨3403594708272367786953695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076252555392980765209853 3403594708272367786953695)
                      ·
                        rfl

theorem cell23_6628477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_6628477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628477 prefixEnd_6628477 := by exact prefixLift 6628477
  have htrace : WordTrace (prefixWord ++ tailWord_6628477) baseStart_6628477 baseEnd_6628477 := by
    simpa [prefixWord, tailWord_6628477, baseEnd_6628477] using wordTrace_append hprefix tailTrace_6628477
  have hstable : (prefixWord ++ tailWord_6628477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628477).length < 2 ^ (prefixWord ++ tailWord_6628477).sum := by decide
  have hdescent : baseEnd_6628477 < baseStart_6628477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628484 : List Nat := [2, 3, 2, 1, 2, 2, 2, 4, 5]
def baseStart_6628484 : Nat := 118140960795 + 6628484 * 2 ^ 59
def prefixEnd_6628484 : Nat := 4983230072969 + 3 ^ 40 * 6628484 * 2
def baseEnd_6628484 : Nat := 378177589181883251062907

theorem tailTrace_6628484 : CollatzResearch.WordTrace tailWord_6628484 prefixEnd_6628484 378177589181883251062907 := by
  unfold tailWord_6628484
  simp only [CollatzResearch.WordTrace]
  refine ⟨120880336459070998892406253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161173781945427998523208337 120880336459070998892406253)
  ·
    refine ⟨45330126172151624584652345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120880336459070998892406253 45330126172151624584652345)
    ·
      refine ⟨33997594629113718438489259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45330126172151624584652345 33997594629113718438489259)
      ·
        refine ⟨50996391943670577657733889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33997594629113718438489259 50996391943670577657733889)
        ·
          refine ⟨38247293957752933243300417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50996391943670577657733889 38247293957752933243300417)
          ·
            refine ⟨28685470468314699932475313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38247293957752933243300417 28685470468314699932475313)
            ·
              refine ⟨21514102851236024949356485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28685470468314699932475313 21514102851236024949356485)
              ·
                refine ⟨4033894284606754678004341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21514102851236024949356485 4033894284606754678004341)
                ·
                  refine ⟨378177589181883251062907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4033894284606754678004341 378177589181883251062907)
                  ·
                    rfl

theorem cell23_6628484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_6628484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628484 prefixEnd_6628484 := by exact prefixLift 6628484
  have htrace : WordTrace (prefixWord ++ tailWord_6628484) baseStart_6628484 baseEnd_6628484 := by
    simpa [prefixWord, tailWord_6628484, baseEnd_6628484] using wordTrace_append hprefix tailTrace_6628484
  have hstable : (prefixWord ++ tailWord_6628484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628484).length < 2 ^ (prefixWord ++ tailWord_6628484).sum := by decide
  have hdescent : baseEnd_6628484 < baseStart_6628484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628494 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6628494 : Nat := 118140960795 + 6628494 * 2 ^ 59
def prefixEnd_6628494 : Nat := 4983230072969 + 3 ^ 40 * 6628494 * 2
def baseEnd_6628494 : Nat := 3403603437443494220441117

theorem tailTrace_6628494 : CollatzResearch.WordTrace tailWord_6628494 prefixEnd_6628494 3403603437443494220441117 := by
  unfold tailWord_6628494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30220129706013221186584567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161174025098737179661784357 30220129706013221186584567)
  ·
    refine ⟨45330194559019831779876851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30220129706013221186584567 45330194559019831779876851)
    ·
      refine ⟨67995291838529747669815277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45330194559019831779876851 67995291838529747669815277)
      ·
        refine ⟨25498234439448655376180729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67995291838529747669815277 25498234439448655376180729)
        ·
          refine ⟨19123675829586491532135547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25498234439448655376180729 19123675829586491532135547)
          ·
            refine ⟨28685513744379737298203321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19123675829586491532135547 28685513744379737298203321)
            ·
              refine ⟨21514135308284802973652491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28685513744379737298203321 21514135308284802973652491)
              ·
                refine ⟨32271202962427204460478737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21514135308284802973652491 32271202962427204460478737)
                ·
                  refine ⟨24203402221820403345359053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32271202962427204460478737 24203402221820403345359053)
                  ·
                    refine ⟨9076275833182651254509645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24203402221820403345359053 9076275833182651254509645)
                    ·
                      refine ⟨3403603437443494220441117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076275833182651254509645 3403603437443494220441117)
                      ·
                        rfl

theorem cell23_6628494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6628494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628494 prefixEnd_6628494 := by exact prefixLift 6628494
  have htrace : WordTrace (prefixWord ++ tailWord_6628494) baseStart_6628494 baseEnd_6628494 := by
    simpa [prefixWord, tailWord_6628494, baseEnd_6628494] using wordTrace_append hprefix tailTrace_6628494
  have hstable : (prefixWord ++ tailWord_6628494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628494).length < 2 ^ (prefixWord ++ tailWord_6628494).sum := by decide
  have hdescent : baseEnd_6628494 < baseStart_6628494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628517 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_6628517 : Nat := 118140960795 + 6628517 * 2 ^ 59
def prefixEnd_6628517 : Nat := 4983230072969 + 3 ^ 40 * 6628517 * 2
def baseEnd_6628517 : Nat := 3403615247498547630453511

theorem tailTrace_6628517 : CollatzResearch.WordTrace tailWord_6628517 prefixEnd_6628517 3403615247498547630453511 := by
  unfold tailWord_6628517
  simp only [CollatzResearch.WordTrace]
  refine ⟨241761876527022444420763805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161174584351348296280509203 241761876527022444420763805)
  ·
    refine ⟨90660703697633416657786427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241761876527022444420763805 90660703697633416657786427)
    ·
      refine ⟨135991055546450124986679641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90660703697633416657786427 135991055546450124986679641)
      ·
        refine ⟨101993291659837593740009731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135991055546450124986679641 101993291659837593740009731)
        ·
          refine ⟨152989937489756390610014597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101993291659837593740009731 152989937489756390610014597)
          ·
            refine ⟨28685613279329323239377737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152989937489756390610014597 28685613279329323239377737)
            ·
              refine ⟨21514209959496992429533303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28685613279329323239377737 21514209959496992429533303)
              ·
                refine ⟨32271314939245488644299955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21514209959496992429533303 32271314939245488644299955)
                ·
                  refine ⟨48406972408868232966449933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32271314939245488644299955 48406972408868232966449933)
                  ·
                    refine ⟨18152614653325587362418725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48406972408868232966449933 18152614653325587362418725)
                    ·
                      refine ⟨3403615247498547630453511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18152614653325587362418725 3403615247498547630453511)
                      ·
                        rfl

theorem cell23_6628517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_6628517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628517 prefixEnd_6628517 := by exact prefixLift 6628517
  have htrace : WordTrace (prefixWord ++ tailWord_6628517) baseStart_6628517 baseEnd_6628517 := by
    simpa [prefixWord, tailWord_6628517, baseEnd_6628517] using wordTrace_append hprefix tailTrace_6628517
  have hstable : (prefixWord ++ tailWord_6628517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628517).length < 2 ^ (prefixWord ++ tailWord_6628517).sum := by decide
  have hdescent : baseEnd_6628517 < baseStart_6628517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628527 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 5, 4]
def baseStart_6628527 : Nat := 118140960795 + 6628527 * 2 ^ 59
def prefixEnd_6628527 : Nat := 4983230072969 + 3 ^ 40 * 6628527 * 2
def baseEnd_6628527 : Nat := 1134540127435030863776155

theorem tailTrace_6628527 : CollatzResearch.WordTrace tailWord_6628527 prefixEnd_6628527 1134540127435030863776155 := by
  unfold tailWord_6628527
  simp only [CollatzResearch.WordTrace]
  refine ⟨241762241256986216128627835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161174827504657477419085223 241762241256986216128627835)
  ·
    refine ⟨362643361885479324192941753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241762241256986216128627835 362643361885479324192941753)
    ·
      refine ⟨271982521414109493144706315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362643361885479324192941753 271982521414109493144706315)
      ·
        refine ⟨407973782121164239717059473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271982521414109493144706315 407973782121164239717059473)
        ·
          refine ⟨305980336590873179787794605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407973782121164239717059473 305980336590873179787794605)
          ·
            refine ⟨114742626221577442420422977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305980336590873179787794605 114742626221577442420422977)
            ·
              refine ⟨86056969666183081815317233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114742626221577442420422977 86056969666183081815317233)
              ·
                refine ⟨64542727249637311361487925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86056969666183081815317233 64542727249637311361487925)
                ·
                  refine ⟨6050880679653497940139493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64542727249637311361487925 6050880679653497940139493)
                  ·
                    refine ⟨1134540127435030863776155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6050880679653497940139493 1134540127435030863776155)
                    ·
                      rfl

theorem cell23_6628527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_6628527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628527 prefixEnd_6628527 := by exact prefixLift 6628527
  have htrace : WordTrace (prefixWord ++ tailWord_6628527) baseStart_6628527 baseEnd_6628527 := by
    simpa [prefixWord, tailWord_6628527, baseEnd_6628527] using wordTrace_append hprefix tailTrace_6628527
  have hstable : (prefixWord ++ tailWord_6628527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628527).length < 2 ^ (prefixWord ++ tailWord_6628527).sum := by decide
  have hdescent : baseEnd_6628527 < baseStart_6628527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628546 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_6628546 : Nat := 118140960795 + 6628546 * 2 ^ 59
def prefixEnd_6628546 : Nat := 4983230072969 + 3 ^ 40 * 6628546 * 2
def baseEnd_6628546 : Nat := 3403630138437528016990879

theorem tailTrace_6628546 : CollatzResearch.WordTrace tailWord_6628546 prefixEnd_6628546 3403630138437528016990879 := by
  unfold tailWord_6628546
  simp only [CollatzResearch.WordTrace]
  refine ⟨60440733560979345593392373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161175289495944921582379661 60440733560979345593392373)
  ·
    refine ⟨5666318771341813649380535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60440733560979345593392373 5666318771341813649380535)
    ·
      refine ⟨8499478157012720474070803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5666318771341813649380535 8499478157012720474070803)
      ·
        refine ⟨12749217235519080711106205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499478157012720474070803 12749217235519080711106205)
        ·
          refine ⟨4780956463319655266664827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12749217235519080711106205 4780956463319655266664827)
          ·
            refine ⟨7171434694979482899997241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780956463319655266664827 7171434694979482899997241)
            ·
              refine ⟨5378576021234612174997931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7171434694979482899997241 5378576021234612174997931)
              ·
                refine ⟨8067864031851918262496897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5378576021234612174997931 8067864031851918262496897)
                ·
                  refine ⟨6050898023888938696872673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8067864031851918262496897 6050898023888938696872673)
                  ·
                    refine ⟨4538173517916704022654505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6050898023888938696872673 4538173517916704022654505)
                    ·
                      refine ⟨3403630138437528016990879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538173517916704022654505 3403630138437528016990879)
                      ·
                        rfl

theorem cell23_6628546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_6628546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628546 prefixEnd_6628546 := by exact prefixLift 6628546
  have htrace : WordTrace (prefixWord ++ tailWord_6628546) baseStart_6628546 baseEnd_6628546 := by
    simpa [prefixWord, tailWord_6628546, baseEnd_6628546] using wordTrace_append hprefix tailTrace_6628546
  have hstable : (prefixWord ++ tailWord_6628546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628546).length < 2 ^ (prefixWord ++ tailWord_6628546).sum := by decide
  have hdescent : baseEnd_6628546 < baseStart_6628546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628567 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_6628567 : Nat := 118140960795 + 6628567 * 2 ^ 59
def prefixEnd_6628567 : Nat := 4983230072969 + 3 ^ 40 * 6628567 * 2
def baseEnd_6628567 : Nat := 3403640921531272434828281

theorem tailTrace_6628567 : CollatzResearch.WordTrace tailWord_6628567 prefixEnd_6628567 3403640921531272434828281 := by
  unfold tailWord_6628567
  simp only [CollatzResearch.WordTrace]
  refine ⟨241763700176841302960083955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161175800117894201973389303 241763700176841302960083955)
  ·
    refine ⟨362645550265261954440125933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241763700176841302960083955 362645550265261954440125933)
    ·
      refine ⟨135992081349473232915047225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362645550265261954440125933 135992081349473232915047225)
      ·
        refine ⟨101994061012104924686285419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135992081349473232915047225 101994061012104924686285419)
        ·
          refine ⟨152991091518157387029428129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101994061012104924686285419 152991091518157387029428129)
          ·
            refine ⟨114743318638618040272071097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152991091518157387029428129 114743318638618040272071097)
            ·
              refine ⟨86057488978963530204053323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114743318638618040272071097 86057488978963530204053323)
              ·
                refine ⟨129086233468445295306079985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86057488978963530204053323 129086233468445295306079985)
                ·
                  refine ⟨96814675101333971479559989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129086233468445295306079985 96814675101333971479559989)
                  ·
                    refine ⟨9076375790750059826208749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96814675101333971479559989 9076375790750059826208749)
                    ·
                      refine ⟨3403640921531272434828281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076375790750059826208749 3403640921531272434828281)
                      ·
                        rfl

theorem cell23_6628567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_6628567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628567 prefixEnd_6628567 := by exact prefixLift 6628567
  have htrace : WordTrace (prefixWord ++ tailWord_6628567) baseStart_6628567 baseEnd_6628567 := by
    simpa [prefixWord, tailWord_6628567, baseEnd_6628567] using wordTrace_append hprefix tailTrace_6628567
  have hstable : (prefixWord ++ tailWord_6628567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628567).length < 2 ^ (prefixWord ++ tailWord_6628567).sum := by decide
  have hdescent : baseEnd_6628567 < baseStart_6628567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628634 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 1, 6]
def baseStart_6628634 : Nat := 118140960795 + 6628634 * 2 ^ 59
def prefixEnd_6628634 : Nat := 4983230072969 + 3 ^ 40 * 6628634 * 2
def baseEnd_6628634 : Nat := 1134558441578374557563491

theorem tailTrace_6628634 : CollatzResearch.WordTrace tailWord_6628634 prefixEnd_6628634 1134558441578374557563491 := by
  unfold tailWord_6628634
  simp only [CollatzResearch.WordTrace]
  refine ⟨60441535966899643350693239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161177429245065715601848637 60441535966899643350693239)
  ·
    refine ⟨90662303950349465026039859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60441535966899643350693239 90662303950349465026039859)
    ·
      refine ⟨135993455925524197539059789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90662303950349465026039859 135993455925524197539059789)
      ·
        refine ⟨50997545972071574077147421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135993455925524197539059789 50997545972071574077147421)
        ·
          refine ⟨19124079739526840278930283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50997545972071574077147421 19124079739526840278930283)
          ·
            refine ⟨28686119609290260418395425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19124079739526840278930283 28686119609290260418395425)
            ·
              refine ⟨21514589706967695313796569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28686119609290260418395425 21514589706967695313796569)
              ·
                refine ⟨16135942280225771485347427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21514589706967695313796569 16135942280225771485347427)
                ·
                  refine ⟨24203913420338657228021141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16135942280225771485347427 24203913420338657228021141)
                  ·
                    refine ⟨1134558441578374557563491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24203913420338657228021141 1134558441578374557563491)
                    ·
                      rfl

theorem cell23_6628634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_6628634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628634 prefixEnd_6628634 := by exact prefixLift 6628634
  have htrace : WordTrace (prefixWord ++ tailWord_6628634) baseStart_6628634 baseEnd_6628634 := by
    simpa [prefixWord, tailWord_6628634, baseEnd_6628634] using wordTrace_append hprefix tailTrace_6628634
  have hstable : (prefixWord ++ tailWord_6628634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628634).length < 2 ^ (prefixWord ++ tailWord_6628634).sum := by decide
  have hdescent : baseEnd_6628634 < baseStart_6628634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628641 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_6628641 : Nat := 118140960795 + 6628641 * 2 ^ 59
def prefixEnd_6628641 : Nat := 4983230072969 + 3 ^ 40 * 6628641 * 2
def baseEnd_6628641 : Nat := 3403678919099705145302941

theorem tailTrace_6628641 : CollatzResearch.WordTrace tailWord_6628641 prefixEnd_6628641 3403678919099705145302941 := by
  unfold tailWord_6628641
  simp only [CollatzResearch.WordTrace]
  refine ⟨241766399178573213598277777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161177599452382142398851851 241766399178573213598277777)
  ·
    refine ⟨181324799383929910198708333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241766399178573213598277777 181324799383929910198708333)
    ·
      refine ⟨67996799768973716324515625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181324799383929910198708333 67996799768973716324515625)
      ·
        refine ⟨50997599826730287243386719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67996799768973716324515625 50997599826730287243386719)
        ·
          refine ⟨76496399740095430865080079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50997599826730287243386719 76496399740095430865080079)
          ·
            refine ⟨114744599610143146297620119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76496399740095430865080079 114744599610143146297620119)
            ·
              refine ⟨172116899415214719446430179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114744599610143146297620119 172116899415214719446430179)
              ·
                refine ⟨258175349122822079169645269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172116899415214719446430179 258175349122822079169645269)
                ·
                  refine ⟨6050984745066142480538561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 258175349122822079169645269 6050984745066142480538561)
                  ·
                    refine ⟨4538238558799606860403921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6050984745066142480538561 4538238558799606860403921)
                    ·
                      refine ⟨3403678919099705145302941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538238558799606860403921 3403678919099705145302941)
                      ·
                        rfl

theorem cell23_6628641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_6628641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628641 prefixEnd_6628641 := by exact prefixLift 6628641
  have htrace : WordTrace (prefixWord ++ tailWord_6628641) baseStart_6628641 baseEnd_6628641 := by
    simpa [prefixWord, tailWord_6628641, baseEnd_6628641] using wordTrace_append hprefix tailTrace_6628641
  have hstable : (prefixWord ++ tailWord_6628641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628641).length < 2 ^ (prefixWord ++ tailWord_6628641).sum := by decide
  have hdescent : baseEnd_6628641 < baseStart_6628641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628644 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6628644 : Nat := 118140960795 + 6628644 * 2 ^ 59
def prefixEnd_6628644 : Nat := 4983230072969 + 3 ^ 40 * 6628644 * 2
def baseEnd_6628644 : Nat := 3403680459541668633565427

theorem tailTrace_6628644 : CollatzResearch.WordTrace tailWord_6628644 prefixEnd_6628644 3403680459541668633565427 := by
  unfold tailWord_6628644
  simp only [CollatzResearch.WordTrace]
  refine ⟨120883254298781172555318493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161177672398374896740424657 120883254298781172555318493)
  ·
    refine ⟨45331220362042939708244435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120883254298781172555318493 45331220362042939708244435)
    ·
      refine ⟨67996830543064409562366653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45331220362042939708244435 67996830543064409562366653)
      ·
        refine ⟨25498811453649153585887495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67996830543064409562366653 25498811453649153585887495)
        ·
          refine ⟨38248217180473730378831243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25498811453649153585887495 38248217180473730378831243)
          ·
            refine ⟨57372325770710595568246865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38248217180473730378831243 57372325770710595568246865)
            ·
              refine ⟨43029244328032946676185149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57372325770710595568246865 43029244328032946676185149)
              ·
                refine ⟨16135966623012355003569431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43029244328032946676185149 16135966623012355003569431)
                ·
                  refine ⟨24203949934518532505354147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16135966623012355003569431 24203949934518532505354147)
                  ·
                    refine ⟨36305924901777798758031221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24203949934518532505354147 36305924901777798758031221)
                    ·
                      refine ⟨3403680459541668633565427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36305924901777798758031221 3403680459541668633565427)
                      ·
                        rfl

theorem cell23_6628644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6628644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628644 prefixEnd_6628644 := by exact prefixLift 6628644
  have htrace : WordTrace (prefixWord ++ tailWord_6628644) baseStart_6628644 baseEnd_6628644 := by
    simpa [prefixWord, tailWord_6628644, baseEnd_6628644] using wordTrace_append hprefix tailTrace_6628644
  have hstable : (prefixWord ++ tailWord_6628644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628644).length < 2 ^ (prefixWord ++ tailWord_6628644).sum := by decide
  have hdescent : baseEnd_6628644 < baseStart_6628644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628658 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_6628658 : Nat := 118140960795 + 6628658 * 2 ^ 59
def prefixEnd_6628658 : Nat := 4983230072969 + 3 ^ 40 * 6628658 * 2
def baseEnd_6628658 : Nat := 3403687648270831578790363

theorem tailTrace_6628658 : CollatzResearch.WordTrace tailWord_6628658 prefixEnd_6628658 3403687648270831578790363 := by
  unfold tailWord_6628658
  simp only [CollatzResearch.WordTrace]
  refine ⟨60441754804877906375411657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161178012813007750334431085 60441754804877906375411657)
  ·
    refine ⟨45331316103658429781558743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60441754804877906375411657 45331316103658429781558743)
    ·
      refine ⟨67996974155487644672338115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45331316103658429781558743 67996974155487644672338115)
      ·
        refine ⟨101995461233231467008507173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67996974155487644672338115 101995461233231467008507173)
        ·
          refine ⟨19124148981230900064095095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101995461233231467008507173 19124148981230900064095095)
          ·
            refine ⟨28686223471846350096142643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19124148981230900064095095 28686223471846350096142643)
            ·
              refine ⟨43029335207769525144213965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28686223471846350096142643 43029335207769525144213965)
              ·
                refine ⟨16136000702913571929080237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43029335207769525144213965 16136000702913571929080237)
                ·
                  refine ⟨6051000263592589473405089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16136000702913571929080237 6051000263592589473405089)
                  ·
                    refine ⟨4538250197694442105053817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6051000263592589473405089 4538250197694442105053817)
                    ·
                      refine ⟨3403687648270831578790363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538250197694442105053817 3403687648270831578790363)
                      ·
                        rfl

theorem cell23_6628658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_6628658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628658 prefixEnd_6628658 := by exact prefixLift 6628658
  have htrace : WordTrace (prefixWord ++ tailWord_6628658) baseStart_6628658 baseEnd_6628658 := by
    simpa [prefixWord, tailWord_6628658, baseEnd_6628658] using wordTrace_append hprefix tailTrace_6628658
  have hstable : (prefixWord ++ tailWord_6628658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628658).length < 2 ^ (prefixWord ++ tailWord_6628658).sum := by decide
  have hdescent : baseEnd_6628658 < baseStart_6628658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628668 : List Nat := [2, 2, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_6628668 : Nat := 118140960795 + 6628668 * 2 ^ 59
def prefixEnd_6628668 : Nat := 4983230072969 + 3 ^ 40 * 6628668 * 2
def baseEnd_6628668 : Nat := 1134564261025792179888439

theorem tailTrace_6628668 : CollatzResearch.WordTrace tailWord_6628668 prefixEnd_6628668 1134564261025792179888439 := by
  unfold tailWord_6628668
  simp only [CollatzResearch.WordTrace]
  refine ⟨120883691974737698604755329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161178255966316931473007105 120883691974737698604755329)
  ·
    refine ⟨90662768981053273953566497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120883691974737698604755329 90662768981053273953566497)
    ·
      refine ⟨67997076735789955465174873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90662768981053273953566497 67997076735789955465174873)
      ·
        refine ⟨50997807551842466598881155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67997076735789955465174873 50997807551842466598881155)
        ·
          refine ⟨76496711327763699898321733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50997807551842466598881155 76496711327763699898321733)
          ·
            refine ⟨14343133373955693730935325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76496711327763699898321733 14343133373955693730935325)
            ·
              refine ⟨5378675015233385149100747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14343133373955693730935325 5378675015233385149100747)
              ·
                refine ⟨8068012522850077723651121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5378675015233385149100747 8068012522850077723651121)
                ·
                  refine ⟨6051009392137558292738341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8068012522850077723651121 6051009392137558292738341)
                  ·
                    refine ⟨1134564261025792179888439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6051009392137558292738341 1134564261025792179888439)
                    ·
                      rfl

theorem cell23_6628668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_6628668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628668 prefixEnd_6628668 := by exact prefixLift 6628668
  have htrace : WordTrace (prefixWord ++ tailWord_6628668) baseStart_6628668 baseEnd_6628668 := by
    simpa [prefixWord, tailWord_6628668, baseEnd_6628668] using wordTrace_append hprefix tailTrace_6628668
  have hstable : (prefixWord ++ tailWord_6628668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628668).length < 2 ^ (prefixWord ++ tailWord_6628668).sum := by decide
  have hdescent : baseEnd_6628668 < baseStart_6628668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628671 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 4]
def baseStart_6628671 : Nat := 118140960795 + 6628671 * 2 ^ 59
def prefixEnd_6628671 : Nat := 4983230072969 + 3 ^ 40 * 6628671 * 2
def baseEnd_6628671 : Nat := 3403694323519340027927803

theorem tailTrace_6628671 : CollatzResearch.WordTrace tailWord_6628671 prefixEnd_6628671 3403694323519340027927803 := by
  unfold tailWord_6628671
  simp only [CollatzResearch.WordTrace]
  refine ⟨241767493368464528721869867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161178328912309685814579911 241767493368464528721869867)
  ·
    refine ⟨362651240052696793082804801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241767493368464528721869867 362651240052696793082804801)
    ·
      refine ⟨271988430039522594812103601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362651240052696793082804801 271988430039522594812103601)
      ·
        refine ⟨203991322529641946109077701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271988430039522594812103601 203991322529641946109077701)
        ·
          refine ⟨38248372974307864895452069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203991322529641946109077701 38248372974307864895452069)
          ·
            refine ⟨7171569932682724667897263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38248372974307864895452069 7171569932682724667897263)
            ·
              refine ⟨10757354899024087001845895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7171569932682724667897263 10757354899024087001845895)
              ·
                refine ⟨16136032348536130502768843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10757354899024087001845895 16136032348536130502768843)
                ·
                  refine ⟨24204048522804195754153265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16136032348536130502768843 24204048522804195754153265)
                  ·
                    refine ⟨18153036392103146815614949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24204048522804195754153265 18153036392103146815614949)
                    ·
                      refine ⟨3403694323519340027927803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18153036392103146815614949 3403694323519340027927803)
                      ·
                        rfl

theorem cell23_6628671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_6628671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628671 prefixEnd_6628671 := by exact prefixLift 6628671
  have htrace : WordTrace (prefixWord ++ tailWord_6628671) baseStart_6628671 baseEnd_6628671 := by
    simpa [prefixWord, tailWord_6628671, baseEnd_6628671] using wordTrace_append hprefix tailTrace_6628671
  have hstable : (prefixWord ++ tailWord_6628671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628671).length < 2 ^ (prefixWord ++ tailWord_6628671).sum := by decide
  have hdescent : baseEnd_6628671 < baseStart_6628671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628677 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_6628677 : Nat := 118140960795 + 6628677 * 2 ^ 59
def prefixEnd_6628677 : Nat := 4983230072969 + 3 ^ 40 * 6628677 * 2
def baseEnd_6628677 : Nat := 1134565801467755668150925

theorem tailTrace_6628677 : CollatzResearch.WordTrace tailWord_6628677 prefixEnd_6628677 1134565801467755668150925 := by
  unfold tailWord_6628677
  simp only [CollatzResearch.WordTrace]
  refine ⟨241767712206442791746588285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161178474804295194497725523 241767712206442791746588285)
  ·
    refine ⟨90662892077416046904970607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241767712206442791746588285 90662892077416046904970607)
    ·
      refine ⟨135994338116124070357455911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90662892077416046904970607 135994338116124070357455911)
      ·
        refine ⟨203991507174186105536183867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135994338116124070357455911 203991507174186105536183867)
        ·
          refine ⟨305987260761279158304275801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203991507174186105536183867 305987260761279158304275801)
          ·
            refine ⟨229490445570959368728206851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305987260761279158304275801 229490445570959368728206851)
            ·
              refine ⟨344235668356439053092310277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229490445570959368728206851 344235668356439053092310277)
              ·
                refine ⟨64544187816832322454808177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344235668356439053092310277 64544187816832322454808177)
                ·
                  refine ⟨48408140862624241841106133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64544187816832322454808177 48408140862624241841106133)
                  ·
                    refine ⟨1134565801467755668150925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48408140862624241841106133 1134565801467755668150925)
                    ·
                      rfl

theorem cell23_6628677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_6628677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628677 prefixEnd_6628677 := by exact prefixLift 6628677
  have htrace : WordTrace (prefixWord ++ tailWord_6628677) baseStart_6628677 baseEnd_6628677 := by
    simpa [prefixWord, tailWord_6628677, baseEnd_6628677] using wordTrace_append hprefix tailTrace_6628677
  have hstable : (prefixWord ++ tailWord_6628677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628677).length < 2 ^ (prefixWord ++ tailWord_6628677).sum := by decide
  have hdescent : baseEnd_6628677 < baseStart_6628677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628725 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6628725 : Nat := 118140960795 + 6628725 * 2 ^ 59
def prefixEnd_6628725 : Nat := 4983230072969 + 3 ^ 40 * 6628725 * 2
def baseEnd_6628725 : Nat := 3403722051474682816652555

theorem tailTrace_6628725 : CollatzResearch.WordTrace tailWord_6628725 prefixEnd_6628725 3403722051474682816652555 := by
  unfold tailWord_6628725
  simp only [CollatzResearch.WordTrace]
  refine ⟨241769462910268895944335629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161179641940179263962890419 241769462910268895944335629)
  ·
    refine ⟨90663548591350835979125861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241769462910268895944335629 90663548591350835979125861)
    ·
      refine ⟨16999415360878281746086099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90663548591350835979125861 16999415360878281746086099)
      ·
        refine ⟨25499123041317422619129149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16999415360878281746086099 25499123041317422619129149)
        ·
          refine ⟨9562171140494033482173431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25499123041317422619129149 9562171140494033482173431)
          ·
            refine ⟨14343256710741050223260147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9562171140494033482173431 14343256710741050223260147)
            ·
              refine ⟨21514885066111575334890221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14343256710741050223260147 21514885066111575334890221)
              ·
                refine ⟨8068081899791840750583833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21514885066111575334890221 8068081899791840750583833)
                ·
                  refine ⟨6051061424843880562937875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8068081899791840750583833 6051061424843880562937875)
                  ·
                    refine ⟨9076592137265820844406813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6051061424843880562937875 9076592137265820844406813)
                    ·
                      refine ⟨3403722051474682816652555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076592137265820844406813 3403722051474682816652555)
                      ·
                        rfl

theorem cell23_6628725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6628725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628725 prefixEnd_6628725 := by exact prefixLift 6628725
  have htrace : WordTrace (prefixWord ++ tailWord_6628725) baseStart_6628725 baseEnd_6628725 := by
    simpa [prefixWord, tailWord_6628725, baseEnd_6628725] using wordTrace_append hprefix tailTrace_6628725
  have hstable : (prefixWord ++ tailWord_6628725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628725).length < 2 ^ (prefixWord ++ tailWord_6628725).sum := by decide
  have hdescent : baseEnd_6628725 < baseStart_6628725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628731 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 1, 4, 2]
def baseStart_6628731 : Nat := 118140960795 + 6628731 * 2 ^ 59
def prefixEnd_6628731 : Nat := 4983230072969 + 3 ^ 40 * 6628731 * 2
def baseEnd_6628731 : Nat := 3403725132358609793177527

theorem tailTrace_6628731 : CollatzResearch.WordTrace tailWord_6628731 prefixEnd_6628731 3403725132358609793177527 := by
  unfold tailWord_6628731
  simp only [CollatzResearch.WordTrace]
  refine ⟨241769681748247158969054047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161179787832164772646036031 241769681748247158969054047)
  ·
    refine ⟨362654522622370738453581071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241769681748247158969054047 362654522622370738453581071)
    ·
      refine ⟨543981783933556107680371607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362654522622370738453581071 543981783933556107680371607)
      ·
        refine ⟨815972675900334161520557411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 543981783933556107680371607 815972675900334161520557411)
        ·
          refine ⟨1223959013850501242280836117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 815972675900334161520557411 1223959013850501242280836117)
          ·
            refine ⟨57373078774242245731914193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1223959013850501242280836117 57373078774242245731914193)
            ·
              refine ⟨43029809080681684298935645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57373078774242245731914193 43029809080681684298935645)
              ·
                refine ⟨16136178405255631612100867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43029809080681684298935645 16136178405255631612100867)
                ·
                  refine ⟨24204267607883447418151301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16136178405255631612100867 24204267607883447418151301)
                  ·
                    refine ⟨4538300176478146390903369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24204267607883447418151301 4538300176478146390903369)
                    ·
                      refine ⟨3403725132358609793177527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538300176478146390903369 3403725132358609793177527)
                      ·
                        rfl

theorem cell23_6628731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 4, 2].length) (baseStart_6628731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628731 prefixEnd_6628731 := by exact prefixLift 6628731
  have htrace : WordTrace (prefixWord ++ tailWord_6628731) baseStart_6628731 baseEnd_6628731 := by
    simpa [prefixWord, tailWord_6628731, baseEnd_6628731] using wordTrace_append hprefix tailTrace_6628731
  have hstable : (prefixWord ++ tailWord_6628731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628731).length < 2 ^ (prefixWord ++ tailWord_6628731).sum := by decide
  have hdescent : baseEnd_6628731 < baseStart_6628731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628765 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_6628765 : Nat := 118140960795 + 6628765 * 2 ^ 59
def prefixEnd_6628765 : Nat := 4983230072969 + 3 ^ 40 * 6628765 * 2
def baseEnd_6628765 : Nat := 3403742590700862660152371

theorem tailTrace_6628765 : CollatzResearch.WordTrace tailWord_6628765 prefixEnd_6628765 3403742590700862660152371 := by
  unfold tailWord_6628765
  simp only [CollatzResearch.WordTrace]
  refine ⟨241770921830123982775791749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161180614553415988517194499 241770921830123982775791749)
  ·
    refine ⟨45332047843148246770460953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241770921830123982775791749 45332047843148246770460953)
    ·
      refine ⟨33999035882361185077845715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45332047843148246770460953 33999035882361185077845715)
      ·
        refine ⟨50998553823541777616768573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33999035882361185077845715 50998553823541777616768573)
        ·
          refine ⟨19124457683828166606288215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50998553823541777616768573 19124457683828166606288215)
          ·
            refine ⟨28686686525742249909432323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19124457683828166606288215 28686686525742249909432323)
            ·
              refine ⟨43030029788613374864148485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28686686525742249909432323 43030029788613374864148485)
              ·
                refine ⟨8068130585365007787027841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43030029788613374864148485 8068130585365007787027841)
                ·
                  refine ⟨6051097939023755840270881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8068130585365007787027841 6051097939023755840270881)
                  ·
                    refine ⟨4538323454267816880203161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6051097939023755840270881 4538323454267816880203161)
                    ·
                      refine ⟨3403742590700862660152371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538323454267816880203161 3403742590700862660152371)
                      ·
                        rfl

theorem cell23_6628765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_6628765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628765 prefixEnd_6628765 := by exact prefixLift 6628765
  have htrace : WordTrace (prefixWord ++ tailWord_6628765) baseStart_6628765 baseEnd_6628765 := by
    simpa [prefixWord, tailWord_6628765, baseEnd_6628765] using wordTrace_append hprefix tailTrace_6628765
  have hstable : (prefixWord ++ tailWord_6628765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628765).length < 2 ^ (prefixWord ++ tailWord_6628765).sum := by decide
  have hdescent : baseEnd_6628765 < baseStart_6628765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628771 : List Nat := [1, 1, 1, 4, 1, 3, 3, 4, 5]
def baseStart_6628771 : Nat := 118140960795 + 6628771 * 2 ^ 59
def prefixEnd_6628771 : Nat := 4983230072969 + 3 ^ 40 * 6628771 * 2
def baseEnd_6628771 : Nat := 378193963509421070741927

theorem tailTrace_6628771 : CollatzResearch.WordTrace tailWord_6628771 prefixEnd_6628771 378193963509421070741927 := by
  unfold tailWord_6628771
  simp only [CollatzResearch.WordTrace]
  refine ⟨241771140668102245800510167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161180760445401497200340111 241771140668102245800510167)
  ·
    refine ⟨362656711002153368700765251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241771140668102245800510167 362656711002153368700765251)
    ·
      refine ⟨543985066503230053051147877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362656711002153368700765251 543985066503230053051147877)
      ·
        refine ⟨101997199969355634947090227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 543985066503230053051147877 101997199969355634947090227)
        ·
          refine ⟨152995799954033452420635341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101997199969355634947090227 152995799954033452420635341)
          ·
            refine ⟨57373424982762544657738253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152995799954033452420635341 57373424982762544657738253)
            ·
              refine ⟨21515034368535954246651845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57373424982762544657738253 21515034368535954246651845)
              ·
                refine ⟨4034068944100491421247221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21515034368535954246651845 4034068944100491421247221)
                ·
                  refine ⟨378193963509421070741927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4034068944100491421247221 378193963509421070741927)
                  ·
                    rfl

theorem cell23_6628771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 5].length) (baseStart_6628771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628771 prefixEnd_6628771 := by exact prefixLift 6628771
  have htrace : WordTrace (prefixWord ++ tailWord_6628771) baseStart_6628771 baseEnd_6628771 := by
    simpa [prefixWord, tailWord_6628771, baseEnd_6628771] using wordTrace_append hprefix tailTrace_6628771
  have hstable : (prefixWord ++ tailWord_6628771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628771).length < 2 ^ (prefixWord ++ tailWord_6628771).sum := by decide
  have hdescent : baseEnd_6628771 < baseStart_6628771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628791 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 2, 5, 2]
def baseStart_6628791 : Nat := 118140960795 + 6628791 * 2 ^ 59
def prefixEnd_6628791 : Nat := 4983230072969 + 3 ^ 40 * 6628791 * 2
def baseEnd_6628791 : Nat := 3403755941197879558427251

theorem tailTrace_6628791 : CollatzResearch.WordTrace tailWord_6628791 prefixEnd_6628791 3403755941197879558427251 := by
  unfold tailWord_6628791
  simp only [CollatzResearch.WordTrace]
  refine ⟨241771870128029789216238227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161181246752019859477492151 241771870128029789216238227)
  ·
    refine ⟨362657805192044683824357341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241771870128029789216238227 362657805192044683824357341)
    ·
      refine ⟨135996676947016756434134003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362657805192044683824357341 135996676947016756434134003)
      ·
        refine ⟨203995015420525134651201005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135996676947016756434134003 203995015420525134651201005)
        ·
          refine ⟨76498130782696925494200377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203995015420525134651201005 76498130782696925494200377)
          ·
            refine ⟨57373598087022694120650283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76498130782696925494200377 57373598087022694120650283)
            ·
              refine ⟨86060397130534041180975425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57373598087022694120650283 86060397130534041180975425)
              ·
                refine ⟨64545297847900530885731569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86060397130534041180975425 64545297847900530885731569)
                ·
                  refine ⟨48408973385925398164298677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64545297847900530885731569 48408973385925398164298677)
                  ·
                    refine ⟨4538341254930506077903001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48408973385925398164298677 4538341254930506077903001)
                    ·
                      refine ⟨3403755941197879558427251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538341254930506077903001 3403755941197879558427251)
                      ·
                        rfl

theorem cell23_6628791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_6628791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628791 prefixEnd_6628791 := by exact prefixLift 6628791
  have htrace : WordTrace (prefixWord ++ tailWord_6628791) baseStart_6628791 baseEnd_6628791 := by
    simpa [prefixWord, tailWord_6628791, baseEnd_6628791] using wordTrace_append hprefix tailTrace_6628791
  have hstable : (prefixWord ++ tailWord_6628791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628791).length < 2 ^ (prefixWord ++ tailWord_6628791).sum := by decide
  have hdescent : baseEnd_6628791 < baseStart_6628791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628821 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6628821 : Nat := 118140960795 + 6628821 * 2 ^ 59
def prefixEnd_6628821 : Nat := 4983230072969 + 3 ^ 40 * 6628821 * 2
def baseEnd_6628821 : Nat := 3403771345617514441052113

theorem tailTrace_6628821 : CollatzResearch.WordTrace tailWord_6628821 prefixEnd_6628821 3403771345617514441052113 := by
  unfold tailWord_6628821
  simp only [CollatzResearch.WordTrace]
  refine ⟨241772964317921104339830317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161181976211947402893220211 241772964317921104339830317)
  ·
    refine ⟨90664861619220414127436369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241772964317921104339830317 90664861619220414127436369)
    ·
      refine ⟨67998646214415310595577277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90664861619220414127436369 67998646214415310595577277)
      ·
        refine ⟨25499492330405741473341479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67998646214415310595577277 25499492330405741473341479)
        ·
          refine ⟨38249238495608612210012219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25499492330405741473341479 38249238495608612210012219)
          ·
            refine ⟨57373857743412918315018329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38249238495608612210012219 57373857743412918315018329)
            ·
              refine ⟨43030393307559688736263747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57373857743412918315018329 43030393307559688736263747)
              ·
                refine ⟨64545589961339533104395621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43030393307559688736263747 64545589961339533104395621)
                ·
                  refine ⟨12102298117751162457074179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64545589961339533104395621 12102298117751162457074179)
                  ·
                    refine ⟨18153447176626743685611269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12102298117751162457074179 18153447176626743685611269)
                    ·
                      refine ⟨3403771345617514441052113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18153447176626743685611269 3403771345617514441052113)
                      ·
                        rfl

theorem cell23_6628821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6628821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628821 prefixEnd_6628821 := by exact prefixLift 6628821
  have htrace : WordTrace (prefixWord ++ tailWord_6628821) baseStart_6628821 baseEnd_6628821 := by
    simpa [prefixWord, tailWord_6628821, baseEnd_6628821] using wordTrace_append hprefix tailTrace_6628821
  have hstable : (prefixWord ++ tailWord_6628821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628821).length < 2 ^ (prefixWord ++ tailWord_6628821).sum := by decide
  have hdescent : baseEnd_6628821 < baseStart_6628821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628824 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_6628824 : Nat := 118140960795 + 6628824 * 2 ^ 59
def prefixEnd_6628824 : Nat := 4983230072969 + 3 ^ 40 * 6628824 * 2
def baseEnd_6628824 : Nat := 3403772886059477929314599

theorem tailTrace_6628824 : CollatzResearch.WordTrace tailWord_6628824 prefixEnd_6628824 3403772886059477929314599 := by
  unfold tailWord_6628824
  simp only [CollatzResearch.WordTrace]
  refine ⟨120886536868455117926094763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161182049157940157234793017 120886536868455117926094763)
  ·
    refine ⟨181329805302682676889142145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120886536868455117926094763 181329805302682676889142145)
    ·
      refine ⟨135997353977012007666856609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181329805302682676889142145 135997353977012007666856609)
      ·
        refine ⟨101998015482759005750142457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135997353977012007666856609 101998015482759005750142457)
        ·
          refine ⟨76498511612069254312606843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101998015482759005750142457 76498511612069254312606843)
          ·
            refine ⟨114747767418103881468910265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76498511612069254312606843 114747767418103881468910265)
            ·
              refine ⟨86060825563577911101682699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114747767418103881468910265 86060825563577911101682699)
              ·
                refine ⟨129091238345366866652524049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86060825563577911101682699 129091238345366866652524049)
                ·
                  refine ⟨96818428759025149989393037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129091238345366866652524049 96818428759025149989393037)
                  ·
                    refine ⟨36306910784634431246022389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96818428759025149989393037 36306910784634431246022389)
                    ·
                      refine ⟨3403772886059477929314599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36306910784634431246022389 3403772886059477929314599)
                      ·
                        rfl

theorem cell23_6628824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_6628824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628824 prefixEnd_6628824 := by exact prefixLift 6628824
  have htrace : WordTrace (prefixWord ++ tailWord_6628824) baseStart_6628824 baseEnd_6628824 := by
    simpa [prefixWord, tailWord_6628824, baseEnd_6628824] using wordTrace_append hprefix tailTrace_6628824
  have hstable : (prefixWord ++ tailWord_6628824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628824).length < 2 ^ (prefixWord ++ tailWord_6628824).sum := by decide
  have hdescent : baseEnd_6628824 < baseStart_6628824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628898 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_6628898 : Nat := 118140960795 + 6628898 * 2 ^ 59
def prefixEnd_6628898 : Nat := 4983230072969 + 3 ^ 40 * 6628898 * 2
def baseEnd_6628898 : Nat := 3403810883627910639789259

theorem tailTrace_6628898 : CollatzResearch.WordTrace tailWord_6628898 prefixEnd_6628898 3403810883627910639789259 := by
  unfold tailWord_6628898
  simp only [CollatzResearch.WordTrace]
  refine ⟨60443943184660536622595837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161183848492428097660255565 60443943184660536622595837)
  ·
    refine ⟨22666478694247701233473439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60443943184660536622595837 22666478694247701233473439)
    ·
      refine ⟨33999718041371551850210159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22666478694247701233473439 33999718041371551850210159)
      ·
        refine ⟨50999577062057327775315239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33999718041371551850210159 50999577062057327775315239)
        ·
          refine ⟨76499365593085991662972859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50999577062057327775315239 76499365593085991662972859)
          ·
            refine ⟨114749048389628987494459289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76499365593085991662972859 114749048389628987494459289)
            ·
              refine ⟨86061786292221740620844467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114749048389628987494459289 86061786292221740620844467)
              ·
                refine ⟨129092679438332610931266701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86061786292221740620844467 129092679438332610931266701)
                ·
                  refine ⟨48409754789374729099225013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129092679438332610931266701 48409754789374729099225013)
                  ·
                    refine ⟨4538414511503880853052345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48409754789374729099225013 4538414511503880853052345)
                    ·
                      refine ⟨3403810883627910639789259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538414511503880853052345 3403810883627910639789259)
                      ·
                        rfl

theorem cell23_6628898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_6628898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628898 prefixEnd_6628898 := by exact prefixLift 6628898
  have htrace : WordTrace (prefixWord ++ tailWord_6628898) baseStart_6628898 baseEnd_6628898 := by
    simpa [prefixWord, tailWord_6628898, baseEnd_6628898] using wordTrace_append hprefix tailTrace_6628898
  have hstable : (prefixWord ++ tailWord_6628898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628898).length < 2 ^ (prefixWord ++ tailWord_6628898).sum := by decide
  have hdescent : baseEnd_6628898 < baseStart_6628898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628915 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 2, 3, 2]
def baseStart_6628915 : Nat := 118140960795 + 6628915 * 2 ^ 59
def prefixEnd_6628915 : Nat := 4983230072969 + 3 ^ 40 * 6628915 * 2
def baseEnd_6628915 : Nat := 3403819612799037073276681

theorem tailTrace_6628915 : CollatzResearch.WordTrace tailWord_6628915 prefixEnd_6628915 3403819612799037073276681 := by
  unfold tailWord_6628915
  simp only [CollatzResearch.WordTrace]
  refine ⟨241776392779580558393752199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161184261853053705595834799 241776392779580558393752199)
  ·
    refine ⟨362664589169370837590628299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241776392779580558393752199 362664589169370837590628299)
    ·
      refine ⟨543996883754056256385942449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362664589169370837590628299 543996883754056256385942449)
      ·
        refine ⟨407997662815542192289456837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543996883754056256385942449 407997662815542192289456837)
        ·
          refine ⟨76499561777914161054273157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407997662815542192289456837 76499561777914161054273157)
          ·
            refine ⟨14343667833358905197676217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76499561777914161054273157 14343667833358905197676217)
            ·
              refine ⟨10757750875019178898257163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14343667833358905197676217 10757750875019178898257163)
              ·
                refine ⟨16136626312528768347385745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10757750875019178898257163 16136626312528768347385745)
                ·
                  refine ⟨12102469734396576260539309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16136626312528768347385745 12102469734396576260539309)
                  ·
                    refine ⟨4538426150398716097702241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12102469734396576260539309 4538426150398716097702241)
                    ·
                      refine ⟨3403819612799037073276681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538426150398716097702241 3403819612799037073276681)
                      ·
                        rfl

theorem cell23_6628915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3, 2].length) (baseStart_6628915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628915 prefixEnd_6628915 := by exact prefixLift 6628915
  have htrace : WordTrace (prefixWord ++ tailWord_6628915) baseStart_6628915 baseEnd_6628915 := by
    simpa [prefixWord, tailWord_6628915, baseEnd_6628915] using wordTrace_append hprefix tailTrace_6628915
  have hstable : (prefixWord ++ tailWord_6628915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628915).length < 2 ^ (prefixWord ++ tailWord_6628915).sum := by decide
  have hdescent : baseEnd_6628915 < baseStart_6628915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628921 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 3, 6]
def baseStart_6628921 : Nat := 118140960795 + 6628921 * 2 ^ 59
def prefixEnd_6628921 : Nat := 4983230072969 + 3 ^ 40 * 6628921 * 2
def baseEnd_6628921 : Nat := 1134607564560988016600551

theorem tailTrace_6628921 : CollatzResearch.WordTrace tailWord_6628921 prefixEnd_6628921 1134607564560988016600551 := by
  unfold tailWord_6628921
  simp only [CollatzResearch.WordTrace]
  refine ⟨241776611617558821418470617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161184407745039214278980411 241776611617558821418470617)
  ·
    refine ⟨181332458713169116063852963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241776611617558821418470617 181332458713169116063852963)
    ·
      refine ⟨271998688069753674095779445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181332458713169116063852963 271998688069753674095779445)
      ·
        refine ⟨25499877006539406946479323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271998688069753674095779445 25499877006539406946479323)
        ·
          refine ⟨38249815509809110419718985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25499877006539406946479323 38249815509809110419718985)
          ·
            refine ⟨28687361632356832814789239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38249815509809110419718985 28687361632356832814789239)
            ·
              refine ⟨43031042448535249222183859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28687361632356832814789239 43031042448535249222183859)
              ·
                refine ⟨64546563672802873833275789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43031042448535249222183859 64546563672802873833275789)
                ·
                  refine ⟨24204961377301077687478421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64546563672802873833275789 24204961377301077687478421)
                  ·
                    refine ⟨1134607564560988016600551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24204961377301077687478421 1134607564560988016600551)
                    ·
                      rfl

theorem cell23_6628921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_6628921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628921 prefixEnd_6628921 := by exact prefixLift 6628921
  have htrace : WordTrace (prefixWord ++ tailWord_6628921) baseStart_6628921 baseEnd_6628921 := by
    simpa [prefixWord, tailWord_6628921, baseEnd_6628921] using wordTrace_append hprefix tailTrace_6628921
  have hstable : (prefixWord ++ tailWord_6628921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628921).length < 2 ^ (prefixWord ++ tailWord_6628921).sum := by decide
  have hdescent : baseEnd_6628921 < baseStart_6628921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628945 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 3, 2, 2]
def baseStart_6628945 : Nat := 118140960795 + 6628945 * 2 ^ 59
def prefixEnd_6628945 : Nat := 4983230072969 + 3 ^ 40 * 6628945 * 2
def baseEnd_6628945 : Nat := 3403835017218671955901543

theorem tailTrace_6628945 : CollatzResearch.WordTrace tailWord_6628945 prefixEnd_6628945 3403835017218671955901543 := by
  unfold tailWord_6628945
  simp only [CollatzResearch.WordTrace]
  refine ⟨241777486969471873517344289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161184991312981249011562859 241777486969471873517344289)
  ·
    refine ⟨181333115227103905138008217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241777486969471873517344289 181333115227103905138008217)
    ·
      refine ⟨135999836420327928853506163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181333115227103905138008217 135999836420327928853506163)
      ·
        refine ⟨203999754630491893280259245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135999836420327928853506163 203999754630491893280259245)
        ·
          refine ⟨76499907986434459980097217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203999754630491893280259245 76499907986434459980097217)
          ·
            refine ⟨57374930989825844985072913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76499907986434459980097217 57374930989825844985072913)
            ·
              refine ⟨43031198242369383738804685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57374930989825844985072913 43031198242369383738804685)
              ·
                refine ⟨16136699340888518902051757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43031198242369383738804685 16136699340888518902051757)
                ·
                  refine ⟨6051262252833194588269409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16136699340888518902051757 6051262252833194588269409)
                  ·
                    refine ⟨4538446689624895941202057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6051262252833194588269409 4538446689624895941202057)
                    ·
                      refine ⟨3403835017218671955901543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538446689624895941202057 3403835017218671955901543)
                      ·
                        rfl

theorem cell23_6628945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_6628945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628945 prefixEnd_6628945 := by exact prefixLift 6628945
  have htrace : WordTrace (prefixWord ++ tailWord_6628945) baseStart_6628945 baseEnd_6628945 := by
    simpa [prefixWord, tailWord_6628945, baseEnd_6628945] using wordTrace_append hprefix tailTrace_6628945
  have hstable : (prefixWord ++ tailWord_6628945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628945).length < 2 ^ (prefixWord ++ tailWord_6628945).sum := by decide
  have hdescent : baseEnd_6628945 < baseStart_6628945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628948 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_6628948 : Nat := 118140960795 + 6628948 * 2 ^ 59
def prefixEnd_6628948 : Nat := 4983230072969 + 3 ^ 40 * 6628948 * 2
def baseEnd_6628948 : Nat := 3403836557660635444164029

theorem tailTrace_6628948 : CollatzResearch.WordTrace tailWord_6628948 prefixEnd_6628948 3403836557660635444164029 := by
  unfold tailWord_6628948
  simp only [CollatzResearch.WordTrace]
  refine ⟨120888798194230502514851749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161185064258974003353135665 120888798194230502514851749)
  ·
    refine ⟨22666649661418219221534703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120888798194230502514851749 22666649661418219221534703)
    ·
      refine ⟨33999974492127328832302055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22666649661418219221534703 33999974492127328832302055)
      ·
        refine ⟨50999961738190993248453083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33999974492127328832302055 50999961738190993248453083)
        ·
          refine ⟨76499942607286489872679625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50999961738190993248453083 76499942607286489872679625)
          ·
            refine ⟨57374956955464867404509719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76499942607286489872679625 57374956955464867404509719)
            ·
              refine ⟨86062435433197301106764579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57374956955464867404509719 86062435433197301106764579)
              ·
                refine ⟨129093653149795951660146869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86062435433197301106764579 129093653149795951660146869)
                ·
                  refine ⟨12102529982793370468138769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129093653149795951660146869 12102529982793370468138769)
                  ·
                    refine ⟨9076897487095027851104077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12102529982793370468138769 9076897487095027851104077)
                    ·
                      refine ⟨3403836557660635444164029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076897487095027851104077 3403836557660635444164029)
                      ·
                        rfl

theorem cell23_6628948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_6628948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628948 prefixEnd_6628948 := by exact prefixLift 6628948
  have htrace : WordTrace (prefixWord ++ tailWord_6628948) baseStart_6628948 baseEnd_6628948 := by
    simpa [prefixWord, tailWord_6628948, baseEnd_6628948] using wordTrace_append hprefix tailTrace_6628948
  have hstable : (prefixWord ++ tailWord_6628948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628948).length < 2 ^ (prefixWord ++ tailWord_6628948).sum := by decide
  have hdescent : baseEnd_6628948 < baseStart_6628948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628951 : List Nat := [1, 1, 3, 2, 2, 3, 3, 8]
def baseStart_6628951 : Nat := 118140960795 + 6628951 * 2 ^ 59
def prefixEnd_6628951 : Nat := 4983230072969 + 3 ^ 40 * 6628951 * 2
def baseEnd_6628951 : Nat := 126068077707503664163945

theorem tailTrace_6628951 : CollatzResearch.WordTrace tailWord_6628951 prefixEnd_6628951 126068077707503664163945 := by
  unfold tailWord_6628951
  simp only [CollatzResearch.WordTrace]
  refine ⟨241777705807450136542062707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161185137204966757694708471 241777705807450136542062707)
  ·
    refine ⟨362666558711175204813094061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241777705807450136542062707 362666558711175204813094061)
    ·
      refine ⟨135999959516690701804910273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362666558711175204813094061 135999959516690701804910273)
      ·
        refine ⟨101999969637518026353682705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135999959516690701804910273 101999969637518026353682705)
        ·
          refine ⟨76499977228138519765262029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101999969637518026353682705 76499977228138519765262029)
          ·
            refine ⟨28687491460551944911973261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76499977228138519765262029 28687491460551944911973261)
            ·
              refine ⟨10757809297706979341989973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28687491460551944911973261 10757809297706979341989973)
              ·
                refine ⟨126068077707503664163945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10757809297706979341989973 126068077707503664163945)
                ·
                  rfl

theorem cell23_6628951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 8].length) (baseStart_6628951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628951 prefixEnd_6628951 := by exact prefixLift 6628951
  have htrace : WordTrace (prefixWord ++ tailWord_6628951) baseStart_6628951 baseEnd_6628951 := by
    simpa [prefixWord, tailWord_6628951, baseEnd_6628951] using wordTrace_append hprefix tailTrace_6628951
  have hstable : (prefixWord ++ tailWord_6628951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628951).length < 2 ^ (prefixWord ++ tailWord_6628951).sum := by decide
  have hdescent : baseEnd_6628951 < baseStart_6628951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6628982 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_6628982 : Nat := 118140960795 + 6628982 * 2 ^ 59
def prefixEnd_6628982 : Nat := 4983230072969 + 3 ^ 40 * 6628982 * 2
def baseEnd_6628982 : Nat := 3403854016002888311138873

theorem tailTrace_6628982 : CollatzResearch.WordTrace tailWord_6628982 prefixEnd_6628982 3403854016002888311138873 := by
  unfold tailWord_6628982
  simp only [CollatzResearch.WordTrace]
  refine ⟨15111177279396114302277575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161185890980225219224294133 15111177279396114302277575)
  ·
    refine ⟨22666765919094171453416363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15111177279396114302277575 22666765919094171453416363)
    ·
      refine ⟨34000148878641257180124545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22666765919094171453416363 34000148878641257180124545)
      ·
        refine ⟨25500111658980942885093409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34000148878641257180124545 25500111658980942885093409)
        ·
          refine ⟨19125083744235707163820057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25500111658980942885093409 19125083744235707163820057)
          ·
            refine ⟨14343812808176780372865043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19125083744235707163820057 14343812808176780372865043)
            ·
              refine ⟨21515719212265170559297565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14343812808176780372865043 21515719212265170559297565)
              ·
                refine ⟨8068394704599438959736587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21515719212265170559297565 8068394704599438959736587)
                ·
                  refine ⟨12102592056899158439604881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8068394704599438959736587 12102592056899158439604881)
                  ·
                    refine ⟨9076944042674368829703661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12102592056899158439604881 9076944042674368829703661)
                    ·
                      refine ⟨3403854016002888311138873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9076944042674368829703661 3403854016002888311138873)
                      ·
                        rfl

theorem cell23_6628982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_6628982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6628982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6628982 prefixEnd_6628982 := by exact prefixLift 6628982
  have htrace : WordTrace (prefixWord ++ tailWord_6628982) baseStart_6628982 baseEnd_6628982 := by
    simpa [prefixWord, tailWord_6628982, baseEnd_6628982] using wordTrace_append hprefix tailTrace_6628982
  have hstable : (prefixWord ++ tailWord_6628982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6628982).length < 2 ^ (prefixWord ++ tailWord_6628982).sum := by decide
  have hdescent : baseEnd_6628982 < baseStart_6628982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6628982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629001 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_6629001 : Nat := 118140960795 + 6629001 * 2 ^ 59
def prefixEnd_6629001 : Nat := 4983230072969 + 3 ^ 40 * 6629001 * 2
def baseEnd_6629001 : Nat := 3403863772135323736801285

theorem tailTrace_6629001 : CollatzResearch.WordTrace tailWord_6629001 prefixEnd_6629001 3403863772135323736801285 := by
  unfold tailWord_6629001
  simp only [CollatzResearch.WordTrace]
  refine ⟨241779529457268995081382857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161186352971512663387588571 241779529457268995081382857)
  ·
    refine ⟨181334647092951746311037143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241779529457268995081382857 181334647092951746311037143)
    ·
      refine ⟨272001970639427619466555715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181334647092951746311037143 272001970639427619466555715)
      ·
        refine ⟨408002955959141429199833573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272001970639427619466555715 408002955959141429199833573)
        ·
          refine ⟨76500554242339017974968795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 408002955959141429199833573 76500554242339017974968795)
          ·
            refine ⟨114750831363508526962453193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76500554242339017974968795 114750831363508526962453193)
            ·
              refine ⟨86063123522631395221839895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114750831363508526962453193 86063123522631395221839895)
              ·
                refine ⟨129094685283947092832759843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86063123522631395221839895 129094685283947092832759843)
                ·
                  refine ⟨193642027925920639249139765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129094685283947092832759843 193642027925920639249139765)
                  ·
                    refine ⟨18153940118055059929606853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193642027925920639249139765 18153940118055059929606853)
                    ·
                      refine ⟨3403863772135323736801285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18153940118055059929606853 3403863772135323736801285)
                      ·
                        rfl

theorem cell23_6629001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_6629001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629001 prefixEnd_6629001 := by exact prefixLift 6629001
  have htrace : WordTrace (prefixWord ++ tailWord_6629001) baseStart_6629001 baseEnd_6629001 := by
    simpa [prefixWord, tailWord_6629001, baseEnd_6629001] using wordTrace_append hprefix tailTrace_6629001
  have hstable : (prefixWord ++ tailWord_6629001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629001).length < 2 ^ (prefixWord ++ tailWord_6629001).sum := by decide
  have hdescent : baseEnd_6629001 < baseStart_6629001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629052 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 4, 2, 2]
def baseStart_6629052 : Nat := 118140960795 + 6629052 * 2 ^ 59
def prefixEnd_6629052 : Nat := 4983230072969 + 3 ^ 40 * 6629052 * 2
def baseEnd_6629052 : Nat := 3403889959648703037263551

theorem tailTrace_6629052 : CollatzResearch.WordTrace tailWord_6629052 prefixEnd_6629052 3403889959648703037263551 := by
  unfold tailWord_6629052
  simp only [CollatzResearch.WordTrace]
  refine ⟨120890694790042115395744705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161187593053389487194326273 120890694790042115395744705)
  ·
    refine ⟨90668021092531586546808529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120890694790042115395744705 90668021092531586546808529)
    ·
      refine ⟨68001015819398689910106397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90668021092531586546808529 68001015819398689910106397)
      ·
        refine ⟨25500380932274508716289899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68001015819398689910106397 25500380932274508716289899)
        ·
          refine ⟨38250571398411763074434849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25500380932274508716289899 38250571398411763074434849)
          ·
            refine ⟨28687928548808822305826137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38250571398411763074434849 28687928548808822305826137)
            ·
              refine ⟨21515946411606616729369603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28687928548808822305826137 21515946411606616729369603)
              ·
                refine ⟨32273919617409925094054405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21515946411606616729369603 32273919617409925094054405)
                ·
                  refine ⟨6051359928264360955135201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32273919617409925094054405 6051359928264360955135201)
                  ·
                    refine ⟨4538519946198270716351401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6051359928264360955135201 4538519946198270716351401)
                    ·
                      refine ⟨3403889959648703037263551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538519946198270716351401 3403889959648703037263551)
                      ·
                        rfl

theorem cell23_6629052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_6629052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629052 prefixEnd_6629052 := by exact prefixLift 6629052
  have htrace : WordTrace (prefixWord ++ tailWord_6629052) baseStart_6629052 baseEnd_6629052 := by
    simpa [prefixWord, tailWord_6629052, baseEnd_6629052] using wordTrace_append hprefix tailTrace_6629052
  have hstable : (prefixWord ++ tailWord_6629052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629052).length < 2 ^ (prefixWord ++ tailWord_6629052).sum := by decide
  have hdescent : baseEnd_6629052 < baseStart_6629052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629071 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 3, 7]
def baseStart_6629071 : Nat := 118140960795 + 6629071 * 2 ^ 59
def prefixEnd_6629071 : Nat := 4983230072969 + 3 ^ 40 * 6629071 * 2
def baseEnd_6629071 : Nat := 1134633238593712820975321

theorem tailTrace_6629071 : CollatzResearch.WordTrace tailWord_6629071 prefixEnd_6629071 1134633238593712820975321 := by
  unfold tailWord_6629071
  simp only [CollatzResearch.WordTrace]
  refine ⟨241782082567015397036431067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161188055044676931357620711 241782082567015397036431067)
  ·
    refine ⟨362673123850523095554646601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241782082567015397036431067 362673123850523095554646601)
    ·
      refine ⟨272004842887892321665984951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362673123850523095554646601 272004842887892321665984951)
      ·
        refine ⟨408007264331838482498977427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272004842887892321665984951 408007264331838482498977427)
        ·
          refine ⟨612010896497757723748466141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408007264331838482498977427 612010896497757723748466141)
          ·
            refine ⟨229504086186659146405674803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612010896497757723748466141 229504086186659146405674803)
            ·
              refine ⟨344256129279988719608512205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229504086186659146405674803 344256129279988719608512205)
              ·
                refine ⟨129096048479995769853192077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344256129279988719608512205 129096048479995769853192077)
                ·
                  refine ⟨48411018179998413694947029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129096048479995769853192077 48411018179998413694947029)
                  ·
                    refine ⟨1134633238593712820975321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48411018179998413694947029 1134633238593712820975321)
                    ·
                      rfl

theorem cell23_6629071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_6629071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629071 prefixEnd_6629071 := by exact prefixLift 6629071
  have htrace : WordTrace (prefixWord ++ tailWord_6629071) baseStart_6629071 baseEnd_6629071 := by
    simpa [prefixWord, tailWord_6629071, baseEnd_6629071] using wordTrace_append hprefix tailTrace_6629071
  have hstable : (prefixWord ++ tailWord_6629071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629071).length < 2 ^ (prefixWord ++ tailWord_6629071).sum := by decide
  have hdescent : baseEnd_6629071 < baseStart_6629071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629088 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 2, 5]
def baseStart_6629088 : Nat := 118140960795 + 6629088 * 2 ^ 59
def prefixEnd_6629088 : Nat := 4983230072969 + 3 ^ 40 * 6629088 * 2
def baseEnd_6629088 : Nat := 1134636148317421632137795

theorem tailTrace_6629088 : CollatzResearch.WordTrace tailWord_6629088 prefixEnd_6629088 1134636148317421632137795 := by
  unfold tailWord_6629088
  simp only [CollatzResearch.WordTrace]
  refine ⟨120891351303976904469899959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161188468405302539293199945 120891351303976904469899959)
  ·
    refine ⟨181337026955965356704849939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120891351303976904469899959 181337026955965356704849939)
    ·
      refine ⟨272005540433948035057274909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181337026955965356704849939 272005540433948035057274909)
      ·
        refine ⟨102002077662730513146478091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272005540433948035057274909 102002077662730513146478091)
        ·
          refine ⟨153003116494095769719717137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102002077662730513146478091 153003116494095769719717137)
          ·
            refine ⟨114752337370571827289787853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153003116494095769719717137 114752337370571827289787853)
            ·
              refine ⟨43032126513964435233670445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114752337370571827289787853 43032126513964435233670445)
              ·
                refine ⟨16137047442736663212626417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43032126513964435233670445 16137047442736663212626417)
                ·
                  refine ⟨12102785582052497409469813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16137047442736663212626417 12102785582052497409469813)
                  ·
                    refine ⟨1134636148317421632137795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12102785582052497409469813 1134636148317421632137795)
                    ·
                      rfl

theorem cell23_6629088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_6629088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629088 prefixEnd_6629088 := by exact prefixLift 6629088
  have htrace : WordTrace (prefixWord ++ tailWord_6629088) baseStart_6629088 baseEnd_6629088 := by
    simpa [prefixWord, tailWord_6629088, baseEnd_6629088] using wordTrace_append hprefix tailTrace_6629088
  have hstable : (prefixWord ++ tailWord_6629088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629088).length < 2 ^ (prefixWord ++ tailWord_6629088).sum := by decide
  have hdescent : baseEnd_6629088 < baseStart_6629088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629098 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_6629098 : Nat := 118140960795 + 6629098 * 2 ^ 59
def prefixEnd_6629098 : Nat := 4983230072969 + 3 ^ 40 * 6629098 * 2
def baseEnd_6629098 : Nat := 3403913579758809857288339

theorem tailTrace_6629098 : CollatzResearch.WordTrace tailWord_6629098 prefixEnd_6629098 3403913579758809857288339 := by
  unfold tailWord_6629098
  simp only [CollatzResearch.WordTrace]
  refine ⟨60445766834479395161915987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161188711558611720431775965 60445766834479395161915987)
  ·
    refine ⟨90668650251719092742873981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60445766834479395161915987 90668650251719092742873981)
    ·
      refine ⟨34000743844394659778577743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90668650251719092742873981 34000743844394659778577743)
      ·
        refine ⟨51001115766591989667866615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34000743844394659778577743 51001115766591989667866615)
        ·
          refine ⟨76501673649887984501799923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51001115766591989667866615 76501673649887984501799923)
          ·
            refine ⟨114752510474831976752699885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76501673649887984501799923 114752510474831976752699885)
            ·
              refine ⟨43032191428061991282262457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114752510474831976752699885 43032191428061991282262457)
              ·
                refine ⟨32274143571046493461696843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43032191428061991282262457 32274143571046493461696843)
                ·
                  refine ⟨48411215356569740192545265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32274143571046493461696843 48411215356569740192545265)
                  ·
                    refine ⟨36308411517427305144408949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48411215356569740192545265 36308411517427305144408949)
                    ·
                      refine ⟨3403913579758809857288339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36308411517427305144408949 3403913579758809857288339)
                      ·
                        rfl

theorem cell23_6629098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_6629098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629098 prefixEnd_6629098 := by exact prefixLift 6629098
  have htrace : WordTrace (prefixWord ++ tailWord_6629098) baseStart_6629098 baseEnd_6629098 := by
    simpa [prefixWord, tailWord_6629098, baseEnd_6629098] using wordTrace_append hprefix tailTrace_6629098
  have hstable : (prefixWord ++ tailWord_6629098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629098).length < 2 ^ (prefixWord ++ tailWord_6629098).sum := by decide
  have hdescent : baseEnd_6629098 < baseStart_6629098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629148 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 8]
def baseStart_6629148 : Nat := 118140960795 + 6629148 * 2 ^ 59
def prefixEnd_6629148 : Nat := 4983230072969 + 3 ^ 40 * 6629148 * 2
def baseEnd_6629148 : Nat := 378215472643503851295901

theorem tailTrace_6629148 : CollatzResearch.WordTrace tailWord_6629148 prefixEnd_6629148 378215472643503851295901 := by
  unfold tailWord_6629148
  simp only [CollatzResearch.WordTrace]
  refine ⟨120892445493868219593492049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161189927325157626124656065 120892445493868219593492049)
  ·
    refine ⟨90669334120401164695119037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120892445493868219593492049 90669334120401164695119037)
    ·
      refine ⟨34001000295150436760669639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90669334120401164695119037 34001000295150436760669639)
      ·
        refine ⟨51001500442725655141004459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34001000295150436760669639 51001500442725655141004459)
        ·
          refine ⟨76502250664088482711506689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51001500442725655141004459 76502250664088482711506689)
          ·
            refine ⟨57376687998066362033630017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76502250664088482711506689 57376687998066362033630017)
            ·
              refine ⟨43032515998549771525222513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57376687998066362033630017 43032515998549771525222513)
              ·
                refine ⟨32274386998912328643916885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43032515998549771525222513 32274386998912328643916885)
                ·
                  refine ⟨378215472643503851295901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32274386998912328643916885 378215472643503851295901)
                  ·
                    rfl

theorem cell23_6629148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_6629148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629148 prefixEnd_6629148 := by exact prefixLift 6629148
  have htrace : WordTrace (prefixWord ++ tailWord_6629148) baseStart_6629148 baseEnd_6629148 := by
    simpa [prefixWord, tailWord_6629148, baseEnd_6629148] using wordTrace_append hprefix tailTrace_6629148
  have hstable : (prefixWord ++ tailWord_6629148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629148).length < 2 ^ (prefixWord ++ tailWord_6629148).sum := by decide
  have hdescent : baseEnd_6629148 < baseStart_6629148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629192 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_6629192 : Nat := 118140960795 + 6629192 * 2 ^ 59
def prefixEnd_6629192 : Nat := 4983230072969 + 3 ^ 40 * 6629192 * 2
def baseEnd_6629192 : Nat := 3403961846940332489512907

theorem tailTrace_6629192 : CollatzResearch.WordTrace tailWord_6629192 prefixEnd_6629192 3403961846940332489512907 := by
  unfold tailWord_6629192
  simp only [CollatzResearch.WordTrace]
  refine ⟨120893247899788517350792915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161190997199718023134390553 120893247899788517350792915)
  ·
    refine ⟨181339871849682776026189373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120893247899788517350792915 181339871849682776026189373)
    ·
      refine ⟨68002451943631041009821015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181339871849682776026189373 68002451943631041009821015)
      ·
        refine ⟨102003677915446561514731523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68002451943631041009821015 102003677915446561514731523)
        ·
          refine ⟨153005516873169842272097285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102003677915446561514731523 153005516873169842272097285)
          ·
            refine ⟨28688534413719345426018241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153005516873169842272097285 28688534413719345426018241)
            ·
              refine ⟨21516400810289509069513681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28688534413719345426018241 21516400810289509069513681)
              ·
                refine ⟨16137300607717131802135261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21516400810289509069513681 16137300607717131802135261)
                ·
                  refine ⟨6051487727893924425800723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16137300607717131802135261 6051487727893924425800723)
                  ·
                    refine ⟨9077231591840886638701085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6051487727893924425800723 9077231591840886638701085)
                    ·
                      refine ⟨3403961846940332489512907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9077231591840886638701085 3403961846940332489512907)
                      ·
                        rfl

theorem cell23_6629192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_6629192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629192 prefixEnd_6629192 := by exact prefixLift 6629192
  have htrace : WordTrace (prefixWord ++ tailWord_6629192) baseStart_6629192 baseEnd_6629192 := by
    simpa [prefixWord, tailWord_6629192, baseEnd_6629192] using wordTrace_append hprefix tailTrace_6629192
  have hstable : (prefixWord ++ tailWord_6629192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629192).length < 2 ^ (prefixWord ++ tailWord_6629192).sum := by decide
  have hdescent : baseEnd_6629192 < baseStart_6629192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629202 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_6629202 : Nat := 118140960795 + 6629202 * 2 ^ 59
def prefixEnd_6629202 : Nat := 4983230072969 + 3 ^ 40 * 6629202 * 2
def baseEnd_6629202 : Nat := 3403966981746877450387861

theorem tailTrace_6629202 : CollatzResearch.WordTrace tailWord_6629202 prefixEnd_6629202 3403966981746877450387861 := by
  unfold tailWord_6629202
  simp only [CollatzResearch.WordTrace]
  refine ⟨60446715132385201602362465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161191240353027204272966573 60446715132385201602362465)
  ·
    refine ⟨45335036349288901201771849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60446715132385201602362465 45335036349288901201771849)
    ·
      refine ⟨34001277261966675901328887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45335036349288901201771849 34001277261966675901328887)
      ·
        refine ⟨51001915892950013851993331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34001277261966675901328887 51001915892950013851993331)
        ·
          refine ⟨76502873839425020777989997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51001915892950013851993331 76502873839425020777989997)
          ·
            refine ⟨28688577689784382791746249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76502873839425020777989997 28688577689784382791746249)
            ·
              refine ⟨21516433267338287093809687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28688577689784382791746249 21516433267338287093809687)
              ·
                refine ⟨32274649901007430640714531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21516433267338287093809687 32274649901007430640714531)
                ·
                  refine ⟨48411974851511145961071797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32274649901007430640714531 48411974851511145961071797)
                  ·
                    refine ⟨4538622642329169933850481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48411974851511145961071797 4538622642329169933850481)
                    ·
                      refine ⟨3403966981746877450387861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538622642329169933850481 3403966981746877450387861)
                      ·
                        rfl

theorem cell23_6629202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_6629202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629202 prefixEnd_6629202 := by exact prefixLift 6629202
  have htrace : WordTrace (prefixWord ++ tailWord_6629202) baseStart_6629202 baseEnd_6629202 := by
    simpa [prefixWord, tailWord_6629202, baseEnd_6629202] using wordTrace_append hprefix tailTrace_6629202
  have hstable : (prefixWord ++ tailWord_6629202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629202).length < 2 ^ (prefixWord ++ tailWord_6629202).sum := by decide
  have hdescent : baseEnd_6629202 < baseStart_6629202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629219 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 2, 3, 2]
def baseStart_6629219 : Nat := 118140960795 + 6629219 * 2 ^ 59
def prefixEnd_6629219 : Nat := 4983230072969 + 3 ^ 40 * 6629219 * 2
def baseEnd_6629219 : Nat := 3403975710918003883875283

theorem tailTrace_6629219 : CollatzResearch.WordTrace tailWord_6629219 prefixEnd_6629219 3403975710918003883875283 := by
  unfold tailWord_6629219
  simp only [CollatzResearch.WordTrace]
  refine ⟨241787480570479218312818711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161191653713652812208545807 241787480570479218312818711)
  ·
    refine ⟨362681220855718827469228067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241787480570479218312818711 362681220855718827469228067)
    ·
      refine ⟨544021831283578241203842101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362681220855718827469228067 544021831283578241203842101)
      ·
        refine ⟨51002046682835460112860197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 544021831283578241203842101 51002046682835460112860197)
        ·
          refine ⟨9562883753031648771161287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51002046682835460112860197 9562883753031648771161287)
          ·
            refine ⟨14344325629547473156741931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9562883753031648771161287 14344325629547473156741931)
            ·
              refine ⟨21516488444321209735112897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14344325629547473156741931 21516488444321209735112897)
              ·
                refine ⟨16137366333240907301334673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21516488444321209735112897 16137366333240907301334673)
                ·
                  refine ⟨12103024749930680476001005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16137366333240907301334673 12103024749930680476001005)
                  ·
                    refine ⟨4538634281224005178500377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12103024749930680476001005 4538634281224005178500377)
                    ·
                      refine ⟨3403975710918003883875283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538634281224005178500377 3403975710918003883875283)
                      ·
                        rfl

theorem cell23_6629219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_6629219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629219 prefixEnd_6629219 := by exact prefixLift 6629219
  have htrace : WordTrace (prefixWord ++ tailWord_6629219) baseStart_6629219 baseEnd_6629219 := by
    simpa [prefixWord, tailWord_6629219, baseEnd_6629219] using wordTrace_append hprefix tailTrace_6629219
  have hstable : (prefixWord ++ tailWord_6629219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629219).length < 2 ^ (prefixWord ++ tailWord_6629219).sum := by decide
  have hdescent : baseEnd_6629219 < baseStart_6629219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629235 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 3]
def baseStart_6629235 : Nat := 118140960795 + 6629235 * 2 ^ 59
def prefixEnd_6629235 : Nat := 4983230072969 + 3 ^ 40 * 6629235 * 2
def baseEnd_6629235 : Nat := 3403983926608475821275209

theorem tailTrace_6629235 : CollatzResearch.WordTrace tailWord_6629235 prefixEnd_6629235 3403983926608475821275209 := by
  unfold tailWord_6629235
  simp only [CollatzResearch.WordTrace]
  refine ⟨241788064138421253045401159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161192042758947502030267439 241788064138421253045401159)
  ·
    refine ⟨362682096207631879568101739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241788064138421253045401159 362682096207631879568101739)
    ·
      refine ⟨544023144311447819352152609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362682096207631879568101739 544023144311447819352152609)
      ·
        refine ⟨408017358233585864514114457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544023144311447819352152609 408017358233585864514114457)
        ·
          refine ⟨306013018675189398385585843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408017358233585864514114457 306013018675189398385585843)
          ·
            refine ⟨459019528012784097578378765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306013018675189398385585843 459019528012784097578378765)
            ·
              refine ⟨172132323004794036591892037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459019528012784097578378765 172132323004794036591892037)
              ·
                refine ⟨32274810563398881860979757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172132323004794036591892037 32274810563398881860979757)
                ·
                  refine ⟨12103053961274580697867409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32274810563398881860979757 12103053961274580697867409)
                  ·
                    refine ⟨9077290470955935523400557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12103053961274580697867409 9077290470955935523400557)
                    ·
                      refine ⟨3403983926608475821275209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9077290470955935523400557 3403983926608475821275209)
                      ·
                        rfl

theorem cell23_6629235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_6629235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629235 prefixEnd_6629235 := by exact prefixLift 6629235
  have htrace : WordTrace (prefixWord ++ tailWord_6629235) baseStart_6629235 baseEnd_6629235 := by
    simpa [prefixWord, tailWord_6629235, baseEnd_6629235] using wordTrace_append hprefix tailTrace_6629235
  have hstable : (prefixWord ++ tailWord_6629235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629235).length < 2 ^ (prefixWord ++ tailWord_6629235).sum := by decide
  have hdescent : baseEnd_6629235 < baseStart_6629235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629245 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_6629245 : Nat := 118140960795 + 6629245 * 2 ^ 59
def prefixEnd_6629245 : Nat := 4983230072969 + 3 ^ 40 * 6629245 * 2
def baseEnd_6629245 : Nat := 3403989061415020782150163

theorem tailTrace_6629245 : CollatzResearch.WordTrace tailWord_6629245 prefixEnd_6629245 3403989061415020782150163 := by
  unfold tailWord_6629245
  simp only [CollatzResearch.WordTrace]
  refine ⟨241788428868385024753265189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161192285912256683168843459 241788428868385024753265189)
  ·
    refine ⟨45335330412822192141237223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241788428868385024753265189 45335330412822192141237223)
    ·
      refine ⟨68002995619233288211855835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45335330412822192141237223 68002995619233288211855835)
      ·
        refine ⟨102004493428849932317783753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68002995619233288211855835 102004493428849932317783753)
        ·
          refine ⟨76503370071637449238337815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102004493428849932317783753 76503370071637449238337815)
          ·
            refine ⟨114755055107456173857506723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76503370071637449238337815 114755055107456173857506723)
            ·
              refine ⟨172132582661184260786260085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114755055107456173857506723 172132582661184260786260085)
              ·
                refine ⟨16137429624486024448711883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172132582661184260786260085 16137429624486024448711883)
                ·
                  refine ⟨24206144436729036673067825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16137429624486024448711883 24206144436729036673067825)
                  ·
                    refine ⟨18154608327546777504800869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24206144436729036673067825 18154608327546777504800869)
                    ·
                      refine ⟨3403989061415020782150163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18154608327546777504800869 3403989061415020782150163)
                      ·
                        rfl

theorem cell23_6629245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_6629245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629245 prefixEnd_6629245 := by exact prefixLift 6629245
  have htrace : WordTrace (prefixWord ++ tailWord_6629245) baseStart_6629245 baseEnd_6629245 := by
    simpa [prefixWord, tailWord_6629245, baseEnd_6629245] using wordTrace_append hprefix tailTrace_6629245
  have hstable : (prefixWord ++ tailWord_6629245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629245).length < 2 ^ (prefixWord ++ tailWord_6629245).sum := by decide
  have hdescent : baseEnd_6629245 < baseStart_6629245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629246 : List Nat := [4, 2, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6629246 : Nat := 118140960795 + 6629246 * 2 ^ 59
def prefixEnd_6629246 : Nat := 4983230072969 + 3 ^ 40 * 6629246 * 2
def baseEnd_6629246 : Nat := 1134663191631891759412553

theorem tailTrace_6629246 : CollatzResearch.WordTrace tailWord_6629246 prefixEnd_6629246 1134663191631891759412553 := by
  unfold tailWord_6629246
  simp only [CollatzResearch.WordTrace]
  refine ⟨30223558167672675240506449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161192310227587601282701061 30223558167672675240506449)
  ·
    refine ⟨22667668625754506430379837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30223558167672675240506449 22667668625754506430379837)
    ·
      refine ⟨8500375734657939911392439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22667668625754506430379837 8500375734657939911392439)
      ·
        refine ⟨12750563601986909867088659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8500375734657939911392439 12750563601986909867088659)
        ·
          refine ⟨19125845402980364800632989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12750563601986909867088659 19125845402980364800632989)
          ·
            refine ⟨7172192026117636800237371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19125845402980364800632989 7172192026117636800237371)
            ·
              refine ⟨10758288039176455200356057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172192026117636800237371 10758288039176455200356057)
              ·
                refine ⟨8068716029382341400267043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10758288039176455200356057 8068716029382341400267043)
                ·
                  refine ⟨12103074044073512100400565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8068716029382341400267043 12103074044073512100400565)
                  ·
                    refine ⟨1134663191631891759412553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12103074044073512100400565 1134663191631891759412553)
                    ·
                      rfl

theorem cell23_6629246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6629246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629246 prefixEnd_6629246 := by exact prefixLift 6629246
  have htrace : WordTrace (prefixWord ++ tailWord_6629246) baseStart_6629246 baseEnd_6629246 := by
    simpa [prefixWord, tailWord_6629246, baseEnd_6629246] using wordTrace_append hprefix tailTrace_6629246
  have hstable : (prefixWord ++ tailWord_6629246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629246).length < 2 ^ (prefixWord ++ tailWord_6629246).sum := by decide
  have hdescent : baseEnd_6629246 < baseStart_6629246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629249 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6629249 : Nat := 118140960795 + 6629249 * 2 ^ 59
def prefixEnd_6629249 : Nat := 4983230072969 + 3 ^ 40 * 6629249 * 2
def baseEnd_6629249 : Nat := 3403991115337638766500145

theorem tailTrace_6629249 : CollatzResearch.WordTrace tailWord_6629249 prefixEnd_6629249 3403991115337638766500145 := by
  unfold tailWord_6629249
  simp only [CollatzResearch.WordTrace]
  refine ⟨241788574760370533436410801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161192383173580355624273867 241788574760370533436410801)
  ·
    refine ⟨181341431070277900077308101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241788574760370533436410801 181341431070277900077308101)
    ·
      refine ⟨34001518325677106264495269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181341431070277900077308101 34001518325677106264495269)
      ·
        refine ⟨6375284686064457424592863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34001518325677106264495269 6375284686064457424592863)
        ·
          refine ⟨9562927029096686136889295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375284686064457424592863 9562927029096686136889295)
          ·
            refine ⟨14344390543645029205333943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9562927029096686136889295 14344390543645029205333943)
            ·
              refine ⟨21516585815467543808000915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14344390543645029205333943 21516585815467543808000915)
              ·
                refine ⟨32274878723201315712001373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21516585815467543808000915 32274878723201315712001373)
                ·
                  refine ⟨12103079521200493392000515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32274878723201315712001373 12103079521200493392000515)
                  ·
                    refine ⟨18154619281800740088000773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12103079521200493392000515 18154619281800740088000773)
                    ·
                      refine ⟨3403991115337638766500145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18154619281800740088000773 3403991115337638766500145)
                      ·
                        rfl

theorem cell23_6629249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6629249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629249 prefixEnd_6629249 := by exact prefixLift 6629249
  have htrace : WordTrace (prefixWord ++ tailWord_6629249) baseStart_6629249 baseEnd_6629249 := by
    simpa [prefixWord, tailWord_6629249, baseEnd_6629249] using wordTrace_append hprefix tailTrace_6629249
  have hstable : (prefixWord ++ tailWord_6629249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629249).length < 2 ^ (prefixWord ++ tailWord_6629249).sum := by decide
  have hdescent : baseEnd_6629249 < baseStart_6629249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629265 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_6629265 : Nat := 118140960795 + 6629265 * 2 ^ 59
def prefixEnd_6629265 : Nat := 4983230072969 + 3 ^ 40 * 6629265 * 2
def baseEnd_6629265 : Nat := 3403999331028110703900071

theorem tailTrace_6629265 : CollatzResearch.WordTrace tailWord_6629265 prefixEnd_6629265 3403999331028110703900071 := by
  unfold tailWord_6629265
  simp only [CollatzResearch.WordTrace]
  refine ⟨241789158328312568168993249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161192772218875045445995499 241789158328312568168993249)
  ·
    refine ⟨181341868746234426126744937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241789158328312568168993249 181341868746234426126744937)
    ·
      refine ⟨136006401559675819595058703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181341868746234426126744937 136006401559675819595058703)
      ·
        refine ⟨204009602339513729392588055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136006401559675819595058703 204009602339513729392588055)
        ·
          refine ⟨306014403509270594088882083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204009602339513729392588055 306014403509270594088882083)
          ·
            refine ⟨459021605263905891133323125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306014403509270594088882083 459021605263905891133323125)
            ·
              refine ⟨43033275493491177293749043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 459021605263905891133323125 43033275493491177293749043)
              ·
                refine ⟨64549913240236765940623565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43033275493491177293749043 64549913240236765940623565)
                ·
                  refine ⟨24206217465088787227733837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64549913240236765940623565 24206217465088787227733837)
                  ·
                    refine ⟨9077331549408295210400189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24206217465088787227733837 9077331549408295210400189)
                    ·
                      refine ⟨3403999331028110703900071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9077331549408295210400189 3403999331028110703900071)
                      ·
                        rfl

theorem cell23_6629265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_6629265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629265 prefixEnd_6629265 := by exact prefixLift 6629265
  have htrace : WordTrace (prefixWord ++ tailWord_6629265) baseStart_6629265 baseEnd_6629265 := by
    simpa [prefixWord, tailWord_6629265, baseEnd_6629265] using wordTrace_append hprefix tailTrace_6629265
  have hstable : (prefixWord ++ tailWord_6629265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629265).length < 2 ^ (prefixWord ++ tailWord_6629265).sum := by decide
  have hdescent : baseEnd_6629265 < baseStart_6629265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629266 : List Nat := [3, 2, 3, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6629266 : Nat := 118140960795 + 6629266 * 2 ^ 59
def prefixEnd_6629266 : Nat := 4983230072969 + 3 ^ 40 * 6629266 * 2
def baseEnd_6629266 : Nat := 3403999844508765199987567

theorem tailTrace_6629266 : CollatzResearch.WordTrace tailWord_6629266 prefixEnd_6629266 3403999844508765199987567 := by
  unfold tailWord_6629266
  simp only [CollatzResearch.WordTrace]
  refine ⟨60447298700327236334944913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161192796534205963559853101 60447298700327236334944913)
  ·
    refine ⟨45335474025245427251208685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60447298700327236334944913 45335474025245427251208685)
    ·
      refine ⟨17000802759467035219203257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45335474025245427251208685 17000802759467035219203257)
      ·
        refine ⟨12750602069600276414402443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17000802759467035219203257 12750602069600276414402443)
        ·
          refine ⟨19125903104400414621603665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12750602069600276414402443 19125903104400414621603665)
          ·
            refine ⟨14344427328300310966202749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19125903104400414621603665 14344427328300310966202749)
            ·
              refine ⟨5379160248112616612326031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14344427328300310966202749 5379160248112616612326031)
              ·
                refine ⟨8068740372168924918489047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379160248112616612326031 8068740372168924918489047)
                ·
                  refine ⟨12103110558253387377733571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8068740372168924918489047 12103110558253387377733571)
                  ·
                    refine ⟨18154665837380081066600357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12103110558253387377733571 18154665837380081066600357)
                    ·
                      refine ⟨3403999844508765199987567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18154665837380081066600357 3403999844508765199987567)
                      ·
                        rfl

theorem cell23_6629266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6629266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629266 prefixEnd_6629266 := by exact prefixLift 6629266
  have htrace : WordTrace (prefixWord ++ tailWord_6629266) baseStart_6629266 baseEnd_6629266 := by
    simpa [prefixWord, tailWord_6629266, baseEnd_6629266] using wordTrace_append hprefix tailTrace_6629266
  have hstable : (prefixWord ++ tailWord_6629266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629266).length < 2 ^ (prefixWord ++ tailWord_6629266).sum := by decide
  have hdescent : baseEnd_6629266 < baseStart_6629266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629269 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_6629269 : Nat := 118140960795 + 6629269 * 2 ^ 59
def prefixEnd_6629269 : Nat := 4983230072969 + 3 ^ 40 * 6629269 * 2
def baseEnd_6629269 : Nat := 3404001384950728688250053

theorem tailTrace_6629269 : CollatzResearch.WordTrace tailWord_6629269 prefixEnd_6629269 3404001384950728688250053 := by
  unfold tailWord_6629269
  simp only [CollatzResearch.WordTrace]
  refine ⟨241789304220298076852138861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161192869480198717901425907 241789304220298076852138861)
  ·
    refine ⟨90670989082611778819552073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241789304220298076852138861 90670989082611778819552073)
    ·
      refine ⟨68003241811958834114664055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90670989082611778819552073 68003241811958834114664055)
      ·
        refine ⟨102004862717938251171996083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68003241811958834114664055 102004862717938251171996083)
        ·
          refine ⟨153007294076907376757994125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102004862717938251171996083 153007294076907376757994125)
          ·
            refine ⟨57377735278840266284247797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153007294076907376757994125 57377735278840266284247797)
            ·
              refine ⟨5379162682391274964148231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57377735278840266284247797 5379162682391274964148231)
              ·
                refine ⟨8068744023586912446222347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379162682391274964148231 8068744023586912446222347)
                ·
                  refine ⟨12103116035380368669333521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8068744023586912446222347 12103116035380368669333521)
                  ·
                    refine ⟨9077337026535276502000141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12103116035380368669333521 9077337026535276502000141)
                    ·
                      refine ⟨3404001384950728688250053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9077337026535276502000141 3404001384950728688250053)
                      ·
                        rfl

theorem cell23_6629269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_6629269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629269 prefixEnd_6629269 := by exact prefixLift 6629269
  have htrace : WordTrace (prefixWord ++ tailWord_6629269) baseStart_6629269 baseEnd_6629269 := by
    simpa [prefixWord, tailWord_6629269, baseEnd_6629269] using wordTrace_append hprefix tailTrace_6629269
  have hstable : (prefixWord ++ tailWord_6629269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629269).length < 2 ^ (prefixWord ++ tailWord_6629269).sum := by decide
  have hdescent : baseEnd_6629269 < baseStart_6629269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629272 : List Nat := [2, 1, 2, 6, 2, 10]
def baseStart_6629272 : Nat := 118140960795 + 6629272 * 2 ^ 59
def prefixEnd_6629272 : Nat := 4983230072969 + 3 ^ 40 * 6629272 * 2
def baseEnd_6629272 : Nat := 14008242491327951343673

theorem tailTrace_6629272 : CollatzResearch.WordTrace tailWord_6629272 prefixEnd_6629272 14008242491327951343673 := by
  unfold tailWord_6629272
  simp only [CollatzResearch.WordTrace]
  refine ⟨120894706819643604182249035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161192942426191472242998713 120894706819643604182249035)
  ·
    refine ⟨181342060229465406273373553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120894706819643604182249035 181342060229465406273373553)
    ·
      refine ⟨136006545172099054705030165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181342060229465406273373553 136006545172099054705030165)
      ·
        refine ⟨6375306804942143189298289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 136006545172099054705030165 6375306804942143189298289)
        ·
          refine ⟨4781480103706607391973717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6375306804942143189298289 4781480103706607391973717)
          ·
            refine ⟨14008242491327951343673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4781480103706607391973717 14008242491327951343673)
            ·
              rfl

theorem cell23_6629272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 10].length) (baseStart_6629272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629272 prefixEnd_6629272 := by exact prefixLift 6629272
  have htrace : WordTrace (prefixWord ++ tailWord_6629272) baseStart_6629272 baseEnd_6629272 := by
    simpa [prefixWord, tailWord_6629272, baseEnd_6629272] using wordTrace_append hprefix tailTrace_6629272
  have hstable : (prefixWord ++ tailWord_6629272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629272).length < 2 ^ (prefixWord ++ tailWord_6629272).sum := by decide
  have hdescent : baseEnd_6629272 < baseStart_6629272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629305 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6629305 : Nat := 118140960795 + 6629305 * 2 ^ 59
def prefixEnd_6629305 : Nat := 4983230072969 + 3 ^ 40 * 6629305 * 2
def baseEnd_6629305 : Nat := 3404019870254290547399887

theorem tailTrace_6629305 : CollatzResearch.WordTrace tailWord_6629305 prefixEnd_6629305 3404019870254290547399887 := by
  unfold tailWord_6629305
  simp only [CollatzResearch.WordTrace]
  refine ⟨241790617248167655000449369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161193744832111770000299579 241790617248167655000449369)
  ·
    refine ⟨181342962936125741250337027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241790617248167655000449369 181342962936125741250337027)
    ·
      refine ⟨272014444404188611875505541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181342962936125741250337027 272014444404188611875505541)
      ·
        refine ⟨51002708325785364726657289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272014444404188611875505541 51002708325785364726657289)
        ·
          refine ⟨38252031244339023544992967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51002708325785364726657289 38252031244339023544992967)
          ·
            refine ⟨57378046866508535317489451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38252031244339023544992967 57378046866508535317489451)
            ·
              refine ⟨86067070299762802976234177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57378046866508535317489451 86067070299762802976234177)
              ·
                refine ⟨64550302724822102232175633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86067070299762802976234177 64550302724822102232175633)
                ·
                  refine ⟨48412727043616576674131725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64550302724822102232175633 48412727043616576674131725)
                  ·
                    refine ⟨18154772641356216252799397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48412727043616576674131725 18154772641356216252799397)
                    ·
                      refine ⟨3404019870254290547399887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18154772641356216252799397 3404019870254290547399887)
                      ·
                        rfl

theorem cell23_6629305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6629305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629305 prefixEnd_6629305 := by exact prefixLift 6629305
  have htrace : WordTrace (prefixWord ++ tailWord_6629305) baseStart_6629305 baseEnd_6629305 := by
    simpa [prefixWord, tailWord_6629305, baseEnd_6629305] using wordTrace_append hprefix tailTrace_6629305
  have hstable : (prefixWord ++ tailWord_6629305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629305).length < 2 ^ (prefixWord ++ tailWord_6629305).sum := by decide
  have hdescent : baseEnd_6629305 < baseStart_6629305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629309 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_6629309 : Nat := 118140960795 + 6629309 * 2 ^ 59
def prefixEnd_6629309 : Nat := 4983230072969 + 3 ^ 40 * 6629309 * 2
def baseEnd_6629309 : Nat := 3404021924176908531749869

theorem tailTrace_6629309 : CollatzResearch.WordTrace tailWord_6629309 prefixEnd_6629309 3404021924176908531749869 := by
  unfold tailWord_6629309
  simp only [CollatzResearch.WordTrace]
  refine ⟨241790763140153163683594981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161193842093435442455729987 241790763140153163683594981)
  ·
    refine ⟨45335768088778718190674059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241790763140153163683594981 45335768088778718190674059)
    ·
      refine ⟨68003652133168077286011089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45335768088778718190674059 68003652133168077286011089)
      ·
        refine ⟨51002739099876057964508317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68003652133168077286011089 51002739099876057964508317)
        ·
          refine ⟨19126027162453521736690619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51002739099876057964508317 19126027162453521736690619)
          ·
            refine ⟨28689040743680282605035929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19126027162453521736690619 28689040743680282605035929)
            ·
              refine ⟨21516780557760211953776947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28689040743680282605035929 21516780557760211953776947)
              ·
                refine ⟨32275170836640317930665421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21516780557760211953776947 32275170836640317930665421)
                ·
                  refine ⟨12103189063740119223999533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32275170836640317930665421 12103189063740119223999533)
                  ·
                    refine ⟨4538695898902544708999825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12103189063740119223999533 4538695898902544708999825)
                    ·
                      refine ⟨3404021924176908531749869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538695898902544708999825 3404021924176908531749869)
                      ·
                        rfl

theorem cell23_6629309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_6629309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629309 prefixEnd_6629309 := by exact prefixLift 6629309
  have htrace : WordTrace (prefixWord ++ tailWord_6629309) baseStart_6629309 baseEnd_6629309 := by
    simpa [prefixWord, tailWord_6629309, baseEnd_6629309] using wordTrace_append hprefix tailTrace_6629309
  have hstable : (prefixWord ++ tailWord_6629309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629309).length < 2 ^ (prefixWord ++ tailWord_6629309).sum := by decide
  have hdescent : baseEnd_6629309 < baseStart_6629309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629335 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_6629335 : Nat := 118140960795 + 6629335 * 2 ^ 59
def prefixEnd_6629335 : Nat := 4983230072969 + 3 ^ 40 * 6629335 * 2
def baseEnd_6629335 : Nat := 3404035274673925430024749

theorem tailTrace_6629335 : CollatzResearch.WordTrace tailWord_6629335 prefixEnd_6629335 3404035274673925430024749 := by
  unfold tailWord_6629335
  simp only [CollatzResearch.WordTrace]
  refine ⟨241791711438058970124041459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161194474292039313416027639 241791711438058970124041459)
  ·
    refine ⟨362687567157088455186062189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241791711438058970124041459 362687567157088455186062189)
    ·
      refine ⟨136007837683908170694773321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362687567157088455186062189 136007837683908170694773321)
      ·
        refine ⟨102005878262931128021079991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136007837683908170694773321 102005878262931128021079991)
        ·
          refine ⟨153008817394396692031619987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102005878262931128021079991 153008817394396692031619987)
          ·
            refine ⟨229513226091595038047429981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153008817394396692031619987 229513226091595038047429981)
            ·
              refine ⟨86067459784348139267786243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229513226091595038047429981 86067459784348139267786243)
              ·
                refine ⟨129101189676522208901679365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86067459784348139267786243 129101189676522208901679365)
                ·
                  refine ⟨24206473064347914169064881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129101189676522208901679365 24206473064347914169064881)
                  ·
                    refine ⟨18154854798260935626798661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24206473064347914169064881 18154854798260935626798661)
                    ·
                      refine ⟨3404035274673925430024749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18154854798260935626798661 3404035274673925430024749)
                      ·
                        rfl

theorem cell23_6629335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_6629335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629335 prefixEnd_6629335 := by exact prefixLift 6629335
  have htrace : WordTrace (prefixWord ++ tailWord_6629335) baseStart_6629335 baseEnd_6629335 := by
    simpa [prefixWord, tailWord_6629335, baseEnd_6629335] using wordTrace_append hprefix tailTrace_6629335
  have hstable : (prefixWord ++ tailWord_6629335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629335).length < 2 ^ (prefixWord ++ tailWord_6629335).sum := by decide
  have hdescent : baseEnd_6629335 < baseStart_6629335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629345 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 7]
def baseStart_6629345 : Nat := 118140960795 + 6629345 * 2 ^ 59
def prefixEnd_6629345 : Nat := 4983230072969 + 3 ^ 40 * 6629345 * 2
def baseEnd_6629345 : Nat := 378226712164496710099967

theorem tailTrace_6629345 : CollatzResearch.WordTrace tailWord_6629345 prefixEnd_6629345 378226712164496710099967 := by
  unfold tailWord_6629345
  simp only [CollatzResearch.WordTrace]
  refine ⟨241792076168022741831905489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161194717445348494554603659 241792076168022741831905489)
  ·
    refine ⟨181344057126017056373929117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241792076168022741831905489 181344057126017056373929117)
    ·
      refine ⟨68004021422256396140223419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181344057126017056373929117 68004021422256396140223419)
      ·
        refine ⟨102006032133384594210335129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68004021422256396140223419 102006032133384594210335129)
        ·
          refine ⟨76504524100038445657751347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102006032133384594210335129 76504524100038445657751347)
          ·
            refine ⟨114756786150057668486627021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76504524100038445657751347 114756786150057668486627021)
            ·
              refine ⟨43033794806271625682485133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114756786150057668486627021 43033794806271625682485133)
              ·
                refine ⟨16137673052351859630931925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43033794806271625682485133 16137673052351859630931925)
                ·
                  refine ⟨378226712164496710099967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16137673052351859630931925 378226712164496710099967)
                  ·
                    rfl

theorem cell23_6629345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 7].length) (baseStart_6629345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629345 prefixEnd_6629345 := by exact prefixLift 6629345
  have htrace : WordTrace (prefixWord ++ tailWord_6629345) baseStart_6629345 baseEnd_6629345 := by
    simpa [prefixWord, tailWord_6629345, baseEnd_6629345] using wordTrace_append hprefix tailTrace_6629345
  have hstable : (prefixWord ++ tailWord_6629345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629345).length < 2 ^ (prefixWord ++ tailWord_6629345).sum := by decide
  have hdescent : baseEnd_6629345 < baseStart_6629345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629375 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 6, 5]
def baseStart_6629375 : Nat := 118140960795 + 6629375 * 2 ^ 59
def prefixEnd_6629375 : Nat := 4983230072969 + 3 ^ 40 * 6629375 * 2
def baseEnd_6629375 : Nat := 1134685271300035091174855

theorem tailTrace_6629375 : CollatzResearch.WordTrace tailWord_6629375 prefixEnd_6629375 1134685271300035091174855 := by
  unfold tailWord_6629375
  simp only [CollatzResearch.WordTrace]
  refine ⟨241793170357914056955497579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161195446905276037970331719 241793170357914056955497579)
  ·
    refine ⟨362689755536871085433246369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241793170357914056955497579 362689755536871085433246369)
    ·
      refine ⟨272017316652653314074934777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362689755536871085433246369 272017316652653314074934777)
      ·
        refine ⟨204012987489489985556201083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272017316652653314074934777 204012987489489985556201083)
        ·
          refine ⟨306019481234234978334301625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204012987489489985556201083 306019481234234978334301625)
          ·
            refine ⟨229514610925676233750726219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306019481234234978334301625 229514610925676233750726219)
            ·
              refine ⟨344271916388514350626089329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229514610925676233750726219 344271916388514350626089329)
              ·
                refine ⟨258203937291385762969566997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344271916388514350626089329 258203937291385762969566997)
                ·
                  refine ⟨12103309560533707639198453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 258203937291385762969566997 12103309560533707639198453)
                  ·
                    refine ⟨1134685271300035091174855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12103309560533707639198453 1134685271300035091174855)
                    ·
                      rfl

theorem cell23_6629375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_6629375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629375 prefixEnd_6629375 := by exact prefixLift 6629375
  have htrace : WordTrace (prefixWord ++ tailWord_6629375) baseStart_6629375 baseEnd_6629375 := by
    simpa [prefixWord, tailWord_6629375, baseEnd_6629375] using wordTrace_append hprefix tailTrace_6629375
  have hstable : (prefixWord ++ tailWord_6629375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629375).length < 2 ^ (prefixWord ++ tailWord_6629375).sum := by decide
  have hdescent : baseEnd_6629375 < baseStart_6629375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629402 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5]
def baseStart_6629402 : Nat := 118140960795 + 6629402 * 2 ^ 59
def prefixEnd_6629402 : Nat := 4983230072969 + 3 ^ 40 * 6629402 * 2
def baseEnd_6629402 : Nat := 3404069677877776667886941

theorem tailTrace_6629402 : CollatzResearch.WordTrace tailWord_6629402 prefixEnd_6629402 3404069677877776667886941 := by
  unfold tailWord_6629402
  simp only [CollatzResearch.WordTrace]
  refine ⟨60448538782204060141682615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161196103419210827044486973 60448538782204060141682615)
  ·
    refine ⟨90672808173306090212523923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60448538782204060141682615 90672808173306090212523923)
    ·
      refine ⟨136009212259959135318785885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90672808173306090212523923 136009212259959135318785885)
      ·
        refine ⟨51003454597484675744544707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136009212259959135318785885 51003454597484675744544707)
        ·
          refine ⟨76505181896227013616817061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51003454597484675744544707 76505181896227013616817061)
          ·
            refine ⟨14344721605542565053153199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76505181896227013616817061 14344721605542565053153199)
            ·
              refine ⟨21517082408313847579729799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14344721605542565053153199 21517082408313847579729799)
              ·
                refine ⟨32275623612470771369594699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21517082408313847579729799 32275623612470771369594699)
                ·
                  refine ⟨48413435418706157054392049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32275623612470771369594699 48413435418706157054392049)
                  ·
                    refine ⟨36310076564029617790794037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48413435418706157054392049 36310076564029617790794037)
                    ·
                      refine ⟨3404069677877776667886941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36310076564029617790794037 3404069677877776667886941)
                      ·
                        rfl

theorem cell23_6629402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_6629402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629402 prefixEnd_6629402 := by exact prefixLift 6629402
  have htrace : WordTrace (prefixWord ++ tailWord_6629402) baseStart_6629402 baseEnd_6629402 := by
    simpa [prefixWord, tailWord_6629402, baseEnd_6629402] using wordTrace_append hprefix tailTrace_6629402
  have hstable : (prefixWord ++ tailWord_6629402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629402).length < 2 ^ (prefixWord ++ tailWord_6629402).sum := by decide
  have hdescent : baseEnd_6629402 < baseStart_6629402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629446 : List Nat := [6, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6629446 : Nat := 118140960795 + 6629446 * 2 ^ 59
def prefixEnd_6629446 : Nat := 4983230072969 + 3 ^ 40 * 6629446 * 2
def baseEnd_6629446 : Nat := 3404092271026574495736739

theorem tailTrace_6629446 : CollatzResearch.WordTrace tailWord_6629446 prefixEnd_6629446 3404092271026574495736739 := by
  unfold tailWord_6629446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7556117498145526127541631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161197173293771224054221461 7556117498145526127541631)
  ·
    refine ⟨11334176247218289191312447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7556117498145526127541631 11334176247218289191312447)
    ·
      refine ⟨17001264370827433786968671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11334176247218289191312447 17001264370827433786968671)
      ·
        refine ⟨25501896556241150680453007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17001264370827433786968671 25501896556241150680453007)
        ·
          refine ⟨38252844834361726020679511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25501896556241150680453007 38252844834361726020679511)
          ·
            refine ⟨57379267251542589031019267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38252844834361726020679511 57379267251542589031019267)
            ·
              refine ⟨86068900877313883546528901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57379267251542589031019267 86068900877313883546528901)
              ·
                refine ⟨16137918914496353164974169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86068900877313883546528901 16137918914496353164974169)
                ·
                  refine ⟨12103439185872264873730627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16137918914496353164974169 12103439185872264873730627)
                  ·
                    refine ⟨18155158778808397310595941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12103439185872264873730627 18155158778808397310595941)
                    ·
                      refine ⟨3404092271026574495736739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18155158778808397310595941 3404092271026574495736739)
                      ·
                        rfl

theorem cell23_6629446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6629446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629446 prefixEnd_6629446 := by exact prefixLift 6629446
  have htrace : WordTrace (prefixWord ++ tailWord_6629446) baseStart_6629446 baseEnd_6629446 := by
    simpa [prefixWord, tailWord_6629446, baseEnd_6629446] using wordTrace_append hprefix tailTrace_6629446
  have hstable : (prefixWord ++ tailWord_6629446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629446).length < 2 ^ (prefixWord ++ tailWord_6629446).sum := by decide
  have hdescent : baseEnd_6629446 < baseStart_6629446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629452 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 6]
def baseStart_6629452 : Nat := 118140960795 + 6629452 * 2 ^ 59
def prefixEnd_6629452 : Nat := 4983230072969 + 3 ^ 40 * 6629452 * 2
def baseEnd_6629452 : Nat := 378232816878944608029079

theorem tailTrace_6629452 : CollatzResearch.WordTrace tailWord_6629452 prefixEnd_6629452 378232816878944608029079 := by
  unfold tailWord_6629452
  simp only [CollatzResearch.WordTrace]
  refine ⟨120897989389317549553025305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161197319185756732737367073 120897989389317549553025305)
  ·
    refine ⟨90673492041988162164768979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120897989389317549553025305 90673492041988162164768979)
    ·
      refine ⟨136010238062982243247153469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90673492041988162164768979 136010238062982243247153469)
      ·
        refine ⟨51003839273618341217682551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136010238062982243247153469 51003839273618341217682551)
        ·
          refine ⟨76505758910427511826523827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51003839273618341217682551 76505758910427511826523827)
          ·
            refine ⟨114758638365641267739785741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76505758910427511826523827 114758638365641267739785741)
            ·
              refine ⟨43034489387115475402419653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114758638365641267739785741 43034489387115475402419653)
              ·
                refine ⟨8068966760084151637953685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43034489387115475402419653 8068966760084151637953685)
                ·
                  refine ⟨378232816878944608029079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8068966760084151637953685 378232816878944608029079)
                  ·
                    rfl

theorem cell23_6629452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_6629452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629452 prefixEnd_6629452 := by exact prefixLift 6629452
  have htrace : WordTrace (prefixWord ++ tailWord_6629452) baseStart_6629452 baseEnd_6629452 := by
    simpa [prefixWord, tailWord_6629452, baseEnd_6629452] using wordTrace_append hprefix tailTrace_6629452
  have hstable : (prefixWord ++ tailWord_6629452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629452).length < 2 ^ (prefixWord ++ tailWord_6629452).sum := by decide
  have hdescent : baseEnd_6629452 < baseStart_6629452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629455 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_6629455 : Nat := 118140960795 + 6629455 * 2 ^ 59
def prefixEnd_6629455 : Nat := 4983230072969 + 3 ^ 40 * 6629455 * 2
def baseEnd_6629455 : Nat := 3404096892352464960524197

theorem tailTrace_6629455 : CollatzResearch.WordTrace tailWord_6629455 prefixEnd_6629455 3404096892352464960524197 := by
  unfold tailWord_6629455
  simp only [CollatzResearch.WordTrace]
  refine ⟨241796088197624230618409819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161197392131749487078939879 241796088197624230618409819)
  ·
    refine ⟨362694132296436345927614729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241796088197624230618409819 362694132296436345927614729)
    ·
      refine ⟨272020599222327259445711047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362694132296436345927614729 272020599222327259445711047)
      ·
        refine ⟨408030898833490889168566571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272020599222327259445711047 408030898833490889168566571)
        ·
          refine ⟨612046348250236333752849857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408030898833490889168566571 612046348250236333752849857)
          ·
            refine ⟨459034761187677250314637393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612046348250236333752849857 459034761187677250314637393)
            ·
              refine ⟨344276070890757937735978045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459034761187677250314637393 344276070890757937735978045)
              ·
                refine ⟨129103526584034226650991767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344276070890757937735978045 129103526584034226650991767)
                ·
                  refine ⟨193655289876051339976487651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129103526584034226650991767 193655289876051339976487651)
                  ·
                    refine ⟨290482934814077009964731477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193655289876051339976487651 290482934814077009964731477)
                    ·
                      refine ⟨3404096892352464960524197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 290482934814077009964731477 3404096892352464960524197)
                      ·
                        rfl

theorem cell23_6629455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_6629455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629455 prefixEnd_6629455 := by exact prefixLift 6629455
  have htrace : WordTrace (prefixWord ++ tailWord_6629455) baseStart_6629455 baseEnd_6629455 := by
    simpa [prefixWord, tailWord_6629455, baseEnd_6629455] using wordTrace_append hprefix tailTrace_6629455
  have hstable : (prefixWord ++ tailWord_6629455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629455).length < 2 ^ (prefixWord ++ tailWord_6629455).sum := by decide
  have hdescent : baseEnd_6629455 < baseStart_6629455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629489 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 1, 5, 2]
def baseStart_6629489 : Nat := 118140960795 + 6629489 * 2 ^ 59
def prefixEnd_6629489 : Nat := 4983230072969 + 3 ^ 40 * 6629489 * 2
def baseEnd_6629489 : Nat := 3404114350694717827499041

theorem tailTrace_6629489 : CollatzResearch.WordTrace tailWord_6629489 prefixEnd_6629489 3404114350694717827499041 := by
  unfold tailWord_6629489
  simp only [CollatzResearch.WordTrace]
  refine ⟨241797328279501054425147521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161198218853000702950098347 241797328279501054425147521)
  ·
    refine ⟨181347996209625790818860641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241797328279501054425147521 181347996209625790818860641)
    ·
      refine ⟨136010997157219343114145481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181347996209625790818860641 136010997157219343114145481)
      ·
        refine ⟨102008247867914507335609111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136010997157219343114145481 102008247867914507335609111)
        ·
          refine ⟨153012371801871761003413667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102008247867914507335609111 153012371801871761003413667)
          ·
            refine ⟨229518557702807641505120501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153012371801871761003413667 229518557702807641505120501)
            ·
              refine ⟨21517364784638216391105047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229518557702807641505120501 21517364784638216391105047)
              ·
                refine ⟨32276047176957324586657571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21517364784638216391105047 32276047176957324586657571)
                ·
                  refine ⟨48414070765435986879986357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32276047176957324586657571 48414070765435986879986357)
                  ·
                    refine ⟨4538819134259623769998721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48414070765435986879986357 4538819134259623769998721)
                    ·
                      refine ⟨3404114350694717827499041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538819134259623769998721 3404114350694717827499041)
                      ·
                        rfl

theorem cell23_6629489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_6629489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629489 prefixEnd_6629489 := by exact prefixLift 6629489
  have htrace : WordTrace (prefixWord ++ tailWord_6629489) baseStart_6629489 baseEnd_6629489 := by
    simpa [prefixWord, tailWord_6629489, baseEnd_6629489] using wordTrace_append hprefix tailTrace_6629489
  have hstable : (prefixWord ++ tailWord_6629489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629489).length < 2 ^ (prefixWord ++ tailWord_6629489).sum := by decide
  have hdescent : baseEnd_6629489 < baseStart_6629489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629529 : List Nat := [1, 2, 1, 2, 1, 2, 1, 7, 2, 4]
def baseStart_6629529 : Nat := 118140960795 + 6629529 * 2 ^ 59
def prefixEnd_6629529 : Nat := 4983230072969 + 3 ^ 40 * 6629529 * 2
def baseEnd_6629529 : Nat := 1134711629973632556999619

theorem tailTrace_6629529 : CollatzResearch.WordTrace tailWord_6629529 prefixEnd_6629529 1134711629973632556999619 := by
  unfold tailWord_6629529
  simp only [CollatzResearch.WordTrace]
  refine ⟨241798787199356141256603641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161199191466237427504402427 241798787199356141256603641)
  ·
    refine ⟨181349090399517105942452731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241798787199356141256603641 181349090399517105942452731)
    ·
      refine ⟨272023635599275658913679097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181349090399517105942452731 272023635599275658913679097)
      ·
        refine ⟨204017726699456744185259323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272023635599275658913679097 204017726699456744185259323)
        ·
          refine ⟨306026590049185116277888985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204017726699456744185259323 306026590049185116277888985)
          ·
            refine ⟨229519942536888837208416739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306026590049185116277888985 229519942536888837208416739)
            ·
              refine ⟨344279913805333255812625109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229519942536888837208416739 344279913805333255812625109)
              ·
                refine ⟨8069060479812498183108401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 344279913805333255812625109 8069060479812498183108401)
                ·
                  refine ⟨6051795359859373637331301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8069060479812498183108401 6051795359859373637331301)
                  ·
                    refine ⟨1134711629973632556999619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6051795359859373637331301 1134711629973632556999619)
                    ·
                      rfl

theorem cell23_6629529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_6629529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629529 prefixEnd_6629529 := by exact prefixLift 6629529
  have htrace : WordTrace (prefixWord ++ tailWord_6629529) baseStart_6629529 baseEnd_6629529 := by
    simpa [prefixWord, tailWord_6629529, baseEnd_6629529] using wordTrace_append hprefix tailTrace_6629529
  have hstable : (prefixWord ++ tailWord_6629529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629529).length < 2 ^ (prefixWord ++ tailWord_6629529).sum := by decide
  have hdescent : baseEnd_6629529 < baseStart_6629529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629536 : List Nat := [2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4]
def baseStart_6629536 : Nat := 118140960795 + 6629536 * 2 ^ 59
def prefixEnd_6629536 : Nat := 4983230072969 + 3 ^ 40 * 6629536 * 2
def baseEnd_6629536 : Nat := 3404138484285479143611325

theorem tailTrace_6629536 : CollatzResearch.WordTrace tailWord_6629536 prefixEnd_6629536 3404138484285479143611325 := by
  unfold tailWord_6629536
  simp only [CollatzResearch.WordTrace]
  refine ⟨120899521255165390726054231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161199361673553854301405641 120899521255165390726054231)
  ·
    refine ⟨181349281882748086089081347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120899521255165390726054231 181349281882748086089081347)
    ·
      refine ⟨272023922824122129133622021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181349281882748086089081347 272023922824122129133622021)
      ·
        refine ⟨51004485529522899212554129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272023922824122129133622021 51004485529522899212554129)
        ·
          refine ⟨38253364147142174409415597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51004485529522899212554129 38253364147142174409415597)
          ·
            refine ⟨14345011555178315403530849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38253364147142174409415597 14345011555178315403530849)
            ·
              refine ⟨10758758666383736552648137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14345011555178315403530849 10758758666383736552648137)
              ·
                refine ⟨8069068999787802414486103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10758758666383736552648137 8069068999787802414486103)
                ·
                  refine ⟨12103603499681703621729155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8069068999787802414486103 12103603499681703621729155)
                  ·
                    refine ⟨18155405249522555432593733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12103603499681703621729155 18155405249522555432593733)
                    ·
                      refine ⟨3404138484285479143611325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18155405249522555432593733 3404138484285479143611325)
                      ·
                        rfl

theorem cell23_6629536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_6629536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629536 prefixEnd_6629536 := by exact prefixLift 6629536
  have htrace : WordTrace (prefixWord ++ tailWord_6629536) baseStart_6629536 baseEnd_6629536 := by
    simpa [prefixWord, tailWord_6629536, baseEnd_6629536] using wordTrace_append hprefix tailTrace_6629536
  have hstable : (prefixWord ++ tailWord_6629536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629536).length < 2 ^ (prefixWord ++ tailWord_6629536).sum := by decide
  have hdescent : baseEnd_6629536 < baseStart_6629536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629590 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_6629590 : Nat := 118140960795 + 6629590 * 2 ^ 59
def prefixEnd_6629590 : Nat := 4983230072969 + 3 ^ 40 * 6629590 * 2
def baseEnd_6629590 : Nat := 3404166212240821932336077

theorem tailTrace_6629590 : CollatzResearch.WordTrace tailWord_6629590 prefixEnd_6629590 3404166212240821932336077 := by
  unfold tailWord_6629590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15112563253258446792160889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161200674701423432449716149 15112563253258446792160889)
  ·
    refine ⟨11334422439943835094120667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15112563253258446792160889 11334422439943835094120667)
    ·
      refine ⟨17001633659915752641181001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11334422439943835094120667 17001633659915752641181001)
      ·
        refine ⟨12751225244936814480885751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17001633659915752641181001 12751225244936814480885751)
        ·
          refine ⟨19126837867405221721328627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12751225244936814480885751 19126837867405221721328627)
          ·
            refine ⟨28690256801107832581992941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19126837867405221721328627 28690256801107832581992941)
            ·
              refine ⟨10758846300415437218247353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28690256801107832581992941 10758846300415437218247353)
              ·
                refine ⟨8069134725311577913685515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10758846300415437218247353 8069134725311577913685515)
                ·
                  refine ⟨12103702087967366870528273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8069134725311577913685515 12103702087967366870528273)
                  ·
                    refine ⟨9077776565975525152896205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12103702087967366870528273 9077776565975525152896205)
                    ·
                      refine ⟨3404166212240821932336077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9077776565975525152896205 3404166212240821932336077)
                      ·
                        rfl

theorem cell23_6629590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_6629590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629590 prefixEnd_6629590 := by exact prefixLift 6629590
  have htrace : WordTrace (prefixWord ++ tailWord_6629590) baseStart_6629590 baseEnd_6629590 := by
    simpa [prefixWord, tailWord_6629590, baseEnd_6629590] using wordTrace_append hprefix tailTrace_6629590
  have hstable : (prefixWord ++ tailWord_6629590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629590).length < 2 ^ (prefixWord ++ tailWord_6629590).sum := by decide
  have hdescent : baseEnd_6629590 < baseStart_6629590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629603 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6629603 : Nat := 118140960795 + 6629603 * 2 ^ 59
def prefixEnd_6629603 : Nat := 4983230072969 + 3 ^ 40 * 6629603 * 2
def baseEnd_6629603 : Nat := 3404172887489330381473517

theorem tailTrace_6629603 : CollatzResearch.WordTrace tailWord_6629603 prefixEnd_6629603 3404172887489330381473517 := by
  unfold tailWord_6629603
  simp only [CollatzResearch.WordTrace]
  refine ⟨241801486201088051894797463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161200990800725367929864975 241801486201088051894797463)
  ·
    refine ⟨362702229301632077842196195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241801486201088051894797463 362702229301632077842196195)
    ·
      refine ⟨544053343952448116763294293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362702229301632077842196195 544053343952448116763294293)
      ·
        refine ⟨6375625124442751368319855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 544053343952448116763294293 6375625124442751368319855)
        ·
          refine ⟨9563437686664127052479783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375625124442751368319855 9563437686664127052479783)
          ·
            refine ⟨14345156529996190578719675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9563437686664127052479783 14345156529996190578719675)
            ·
              refine ⟨21517734794994285868079513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345156529996190578719675 21517734794994285868079513)
              ·
                refine ⟨16138301096245714401059635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21517734794994285868079513 16138301096245714401059635)
                ·
                  refine ⟨24207451644368571601589453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16138301096245714401059635 24207451644368571601589453)
                  ·
                    refine ⟨9077794366638214350596045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24207451644368571601589453 9077794366638214350596045)
                    ·
                      refine ⟨3404172887489330381473517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9077794366638214350596045 3404172887489330381473517)
                      ·
                        rfl

theorem cell23_6629603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6629603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629603 prefixEnd_6629603 := by exact prefixLift 6629603
  have htrace : WordTrace (prefixWord ++ tailWord_6629603) baseStart_6629603 baseEnd_6629603 := by
    simpa [prefixWord, tailWord_6629603, baseEnd_6629603] using wordTrace_append hprefix tailTrace_6629603
  have hstable : (prefixWord ++ tailWord_6629603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629603).length < 2 ^ (prefixWord ++ tailWord_6629603).sum := by decide
  have hdescent : baseEnd_6629603 < baseStart_6629603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629636 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_6629636 : Nat := 118140960795 + 6629636 * 2 ^ 59
def prefixEnd_6629636 : Nat := 4983230072969 + 3 ^ 40 * 6629636 * 2
def baseEnd_6629636 : Nat := 1134729944116976250786955

theorem tailTrace_6629636 : CollatzResearch.WordTrace tailWord_6629636 prefixEnd_6629636 1134729944116976250786955 := by
  unfold tailWord_6629636
  simp only [CollatzResearch.WordTrace]
  refine ⟨120901344904984249265374381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161201793206645665687165841 120901344904984249265374381)
  ·
    refine ⟨45338004339369093474515393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120901344904984249265374381 45338004339369093474515393)
    ·
      refine ⟨34003503254526820105886545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45338004339369093474515393 34003503254526820105886545)
      ·
        refine ⟨25502627440895115079414909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34003503254526820105886545 25502627440895115079414909)
        ·
          refine ⟨9563485290335668154780591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25502627440895115079414909 9563485290335668154780591)
          ·
            refine ⟨14345227935503502232170887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9563485290335668154780591 14345227935503502232170887)
            ·
              refine ⟨21517841903255253348256331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345227935503502232170887 21517841903255253348256331)
              ·
                refine ⟨32276762854882880022384497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21517841903255253348256331 32276762854882880022384497)
                ·
                  refine ⟨24207572141162160016788373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32276762854882880022384497 24207572141162160016788373)
                  ·
                    refine ⟨1134729944116976250786955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24207572141162160016788373 1134729944116976250786955)
                    ·
                      rfl

theorem cell23_6629636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_6629636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629636 prefixEnd_6629636 := by exact prefixLift 6629636
  have htrace : WordTrace (prefixWord ++ tailWord_6629636) baseStart_6629636 baseEnd_6629636 := by
    simpa [prefixWord, tailWord_6629636, baseEnd_6629636] using wordTrace_append hprefix tailTrace_6629636
  have hstable : (prefixWord ++ tailWord_6629636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629636).length < 2 ^ (prefixWord ++ tailWord_6629636).sum := by decide
  have hdescent : baseEnd_6629636 < baseStart_6629636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629643 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 2, 2, 2]
def baseStart_6629643 : Nat := 118140960795 + 6629643 * 2 ^ 59
def prefixEnd_6629643 : Nat := 4983230072969 + 3 ^ 40 * 6629643 * 2
def baseEnd_6629643 : Nat := 3404193426715510224973333

theorem tailTrace_6629643 : CollatzResearch.WordTrace tailWord_6629643 prefixEnd_6629643 3404193426715510224973333 := by
  unfold tailWord_6629643
  simp only [CollatzResearch.WordTrace]
  refine ⟨241802945120943138726253583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161201963413962092484169055 241802945120943138726253583)
  ·
    refine ⟨362704417681414708089380375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241802945120943138726253583 362704417681414708089380375)
    ·
      refine ⟨544056626522122062134070563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362704417681414708089380375 544056626522122062134070563)
      ·
        refine ⟨816084939783183093201105845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544056626522122062134070563 816084939783183093201105845)
        ·
          refine ⟨76507963104673414987603673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 816084939783183093201105845 76507963104673414987603673)
          ·
            refine ⟨57380972328505061240702755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76507963104673414987603673 57380972328505061240702755)
            ·
              refine ⟨86071458492757591861054133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57380972328505061240702755 86071458492757591861054133)
              ·
                refine ⟨8069199233696024236973825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86071458492757591861054133 8069199233696024236973825)
                ·
                  refine ⟨6051899425272018177730369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8069199233696024236973825 6051899425272018177730369)
                  ·
                    refine ⟨4538924568954013633297777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6051899425272018177730369 4538924568954013633297777)
                    ·
                      refine ⟨3404193426715510224973333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538924568954013633297777 3404193426715510224973333)
                      ·
                        rfl

theorem cell23_6629643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 2, 2].length) (baseStart_6629643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629643 prefixEnd_6629643 := by exact prefixLift 6629643
  have htrace : WordTrace (prefixWord ++ tailWord_6629643) baseStart_6629643 baseEnd_6629643 := by
    simpa [prefixWord, tailWord_6629643, baseEnd_6629643] using wordTrace_append hprefix tailTrace_6629643
  have hstable : (prefixWord ++ tailWord_6629643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629643).length < 2 ^ (prefixWord ++ tailWord_6629643).sum := by decide
  have hdescent : baseEnd_6629643 < baseStart_6629643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629649 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 7]
def baseStart_6629649 : Nat := 118140960795 + 6629649 * 2 ^ 59
def prefixEnd_6629649 : Nat := 4983230072969 + 3 ^ 40 * 6629649 * 2
def baseEnd_6629649 : Nat := 378244056399937466833145

theorem tailTrace_6629649 : CollatzResearch.WordTrace tailWord_6629649 prefixEnd_6629649 378244056399937466833145 := by
  unfold tailWord_6629649
  simp only [CollatzResearch.WordTrace]
  refine ⟨241803163958921401750972001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161202109305947601167314667 241803163958921401750972001)
  ·
    refine ⟨181352372969191051313229001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241803163958921401750972001 181352372969191051313229001)
    ·
      refine ⟨136014279726893288484921751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181352372969191051313229001 136014279726893288484921751)
      ·
        refine ⟨204021419590339932727382627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136014279726893288484921751 204021419590339932727382627)
        ·
          refine ⟨306032129385509899091073941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204021419590339932727382627 306032129385509899091073941)
          ·
            refine ⟨14345256064945776519894091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 306032129385509899091073941 14345256064945776519894091)
            ·
              refine ⟨21517884097418664779841137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345256064945776519894091 21517884097418664779841137)
              ·
                refine ⟨16138413073063998584880853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21517884097418664779841137 16138413073063998584880853)
                ·
                  refine ⟨378244056399937466833145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16138413073063998584880853 378244056399937466833145)
                  ·
                    rfl

theorem cell23_6629649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 7].length) (baseStart_6629649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629649 prefixEnd_6629649 := by exact prefixLift 6629649
  have htrace : WordTrace (prefixWord ++ tailWord_6629649) baseStart_6629649 baseEnd_6629649 := by
    simpa [prefixWord, tailWord_6629649, baseEnd_6629649] using wordTrace_append hprefix tailTrace_6629649
  have hstable : (prefixWord ++ tailWord_6629649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629649).length < 2 ^ (prefixWord ++ tailWord_6629649).sum := by decide
  have hdescent : baseEnd_6629649 < baseStart_6629649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629671 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_6629671 : Nat := 118140960795 + 6629671 * 2 ^ 59
def prefixEnd_6629671 : Nat := 4983230072969 + 3 ^ 40 * 6629671 * 2
def baseEnd_6629671 : Nat := 3404207804173836115423205

theorem tailTrace_6629671 : CollatzResearch.WordTrace tailWord_6629671 prefixEnd_6629671 3404207804173836115423205 := by
  unfold tailWord_6629671
  simp only [CollatzResearch.WordTrace]
  refine ⟨241803966364841699508272867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161202644243227799672181911 241803966364841699508272867)
  ·
    refine ⟨362705949547262549262409301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241803966364841699508272867 362705949547262549262409301)
    ·
      refine ⟨4250460346256982999168859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 362705949547262549262409301 4250460346256982999168859)
      ·
        refine ⟨6375690519385474498753289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4250460346256982999168859 6375690519385474498753289)
        ·
          refine ⟨4781767889539105874064967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6375690519385474498753289 4781767889539105874064967)
          ·
            refine ⟨7172651834308658811097451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781767889539105874064967 7172651834308658811097451)
            ·
              refine ⟨10758977751462988216646177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172651834308658811097451 10758977751462988216646177)
              ·
                refine ⟨8069233313597241162484633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10758977751462988216646177 8069233313597241162484633)
                ·
                  refine ⟨6051924985197930871863475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8069233313597241162484633 6051924985197930871863475)
                  ·
                    refine ⟨9077887477796896307795213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6051924985197930871863475 9077887477796896307795213)
                    ·
                      refine ⟨3404207804173836115423205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9077887477796896307795213 3404207804173836115423205)
                      ·
                        rfl

theorem cell23_6629671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_6629671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629671 prefixEnd_6629671 := by exact prefixLift 6629671
  have htrace : WordTrace (prefixWord ++ tailWord_6629671) baseStart_6629671 baseEnd_6629671 := by
    simpa [prefixWord, tailWord_6629671, baseEnd_6629671] using wordTrace_append hprefix tailTrace_6629671
  have hstable : (prefixWord ++ tailWord_6629671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629671).length < 2 ^ (prefixWord ++ tailWord_6629671).sum := by decide
  have hdescent : baseEnd_6629671 < baseStart_6629671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629677 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6629677 : Nat := 118140960795 + 6629677 * 2 ^ 59
def prefixEnd_6629677 : Nat := 4983230072969 + 3 ^ 40 * 6629677 * 2
def baseEnd_6629677 : Nat := 3404210885057763091948177

theorem tailTrace_6629677 : CollatzResearch.WordTrace tailWord_6629677 prefixEnd_6629677 3404210885057763091948177 := by
  unfold tailWord_6629677
  simp only [CollatzResearch.WordTrace]
  refine ⟨241804185202819962532991285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161202790135213308355327523 241804185202819962532991285)
  ·
    refine ⟨22669142362764371487467933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241804185202819962532991285 22669142362764371487467933)
    ·
      refine ⟨8500928386036639307800475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22669142362764371487467933 8500928386036639307800475)
      ·
        refine ⟨12751392579054958961700713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8500928386036639307800475 12751392579054958961700713)
        ·
          refine ⟨9563544434291219221275535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12751392579054958961700713 9563544434291219221275535)
          ·
            refine ⟨14345316651436828831913303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9563544434291219221275535 14345316651436828831913303)
            ·
              refine ⟨21517974977155243247869955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345316651436828831913303 21517974977155243247869955)
              ·
                refine ⟨32276962465732864871804933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21517974977155243247869955 32276962465732864871804933)
                ·
                  refine ⟨6051930462324912163463425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32276962465732864871804933 6051930462324912163463425)
                  ·
                    refine ⟨4538947846743684122597569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6051930462324912163463425 4538947846743684122597569)
                    ·
                      refine ⟨3404210885057763091948177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4538947846743684122597569 3404210885057763091948177)
                      ·
                        rfl

theorem cell23_6629677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6629677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629677 prefixEnd_6629677 := by exact prefixLift 6629677
  have htrace : WordTrace (prefixWord ++ tailWord_6629677) baseStart_6629677 baseEnd_6629677 := by
    simpa [prefixWord, tailWord_6629677, baseEnd_6629677] using wordTrace_append hprefix tailTrace_6629677
  have hstable : (prefixWord ++ tailWord_6629677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629677).length < 2 ^ (prefixWord ++ tailWord_6629677).sum := by decide
  have hdescent : baseEnd_6629677 < baseStart_6629677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629679 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 2, 5]
def baseStart_6629679 : Nat := 118140960795 + 6629679 * 2 ^ 59
def prefixEnd_6629679 : Nat := 4983230072969 + 3 ^ 40 * 6629679 * 2
def baseEnd_6629679 : Nat := 1134737304006357361374389

theorem tailTrace_6629679 : CollatzResearch.WordTrace tailWord_6629679 prefixEnd_6629679 1134737304006357361374389 := by
  unfold tailWord_6629679
  simp only [CollatzResearch.WordTrace]
  refine ⟨241804258148812716874564091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161202838765875144583042727 241804258148812716874564091)
  ·
    refine ⟨362706387223219075311846137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241804258148812716874564091 362706387223219075311846137)
    ·
      refine ⟨272029790417414306483884603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362706387223219075311846137 272029790417414306483884603)
      ·
        refine ⟨408044685626121459725826905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272029790417414306483884603 408044685626121459725826905)
        ·
          refine ⟨306033514219591094794370179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408044685626121459725826905 306033514219591094794370179)
          ·
            refine ⟨459050271329386642191555269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306033514219591094794370179 459050271329386642191555269)
            ·
              refine ⟨86071925874259995410916613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 459050271329386642191555269 86071925874259995410916613)
              ·
                refine ⟨16138486101423749139546865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86071925874259995410916613 16138486101423749139546865)
                ·
                  refine ⟨12103864576067811854660149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16138486101423749139546865 12103864576067811854660149)
                  ·
                    refine ⟨1134737304006357361374389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12103864576067811854660149 1134737304006357361374389)
                    ·
                      rfl

theorem cell23_6629679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_6629679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629679 prefixEnd_6629679 := by exact prefixLift 6629679
  have htrace : WordTrace (prefixWord ++ tailWord_6629679) baseStart_6629679 baseEnd_6629679 := by
    simpa [prefixWord, tailWord_6629679, baseEnd_6629679] using wordTrace_append hprefix tailTrace_6629679
  have hstable : (prefixWord ++ tailWord_6629679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629679).length < 2 ^ (prefixWord ++ tailWord_6629679).sum := by decide
  have hdescent : baseEnd_6629679 < baseStart_6629679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629699 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4]
def baseStart_6629699 : Nat := 118140960795 + 6629699 * 2 ^ 59
def prefixEnd_6629699 : Nat := 4983230072969 + 3 ^ 40 * 6629699 * 2
def baseEnd_6629699 : Nat := 3404222181632162005873075

theorem tailTrace_6629699 : CollatzResearch.WordTrace tailWord_6629699 prefixEnd_6629699 3404222181632162005873075 := by
  unfold tailWord_6629699
  simp only [CollatzResearch.WordTrace]
  refine ⟨241804987608740260290292151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161203325072493506860194767 241804987608740260290292151)
  ·
    refine ⟨362707481413110390435438227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241804987608740260290292151 362707481413110390435438227)
    ·
      refine ⟨544061222119665585653157341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362707481413110390435438227 544061222119665585653157341)
      ·
        refine ⟨204022958294874594619934003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544061222119665585653157341 204022958294874594619934003)
        ·
          refine ⟨306034437442311891929901005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204022958294874594619934003 306034437442311891929901005)
          ·
            refine ⟨114762914040866959473712877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306034437442311891929901005 114762914040866959473712877)
            ·
              refine ⟨43036092765325109802642329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114762914040866959473712877 43036092765325109802642329)
              ·
                refine ⟨32277069573993832351981747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43036092765325109802642329 32277069573993832351981747)
                ·
                  refine ⟨48415604360990748527972621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32277069573993832351981747 48415604360990748527972621)
                  ·
                    refine ⟨18155851635371530697989733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48415604360990748527972621 18155851635371530697989733)
                    ·
                      refine ⟨3404222181632162005873075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18155851635371530697989733 3404222181632162005873075)
                      ·
                        rfl

theorem cell23_6629699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_6629699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629699 prefixEnd_6629699 := by exact prefixLift 6629699
  have htrace : WordTrace (prefixWord ++ tailWord_6629699) baseStart_6629699 baseEnd_6629699 := by
    simpa [prefixWord, tailWord_6629699, baseEnd_6629699] using wordTrace_append hprefix tailTrace_6629699
  have hstable : (prefixWord ++ tailWord_6629699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629699).length < 2 ^ (prefixWord ++ tailWord_6629699).sum := by decide
  have hdescent : baseEnd_6629699 < baseStart_6629699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629716 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_6629716 : Nat := 118140960795 + 6629716 * 2 ^ 59
def prefixEnd_6629716 : Nat := 4983230072969 + 3 ^ 40 * 6629716 * 2
def baseEnd_6629716 : Nat := 3404230910803288439360497

theorem tailTrace_6629716 : CollatzResearch.WordTrace tailWord_6629716 prefixEnd_6629716 3404230910803288439360497 := by
  unfold tailWord_6629716
  simp only [CollatzResearch.WordTrace]
  refine ⟨120902803824839336096830501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161203738433119114795774001 120902803824839336096830501)
  ·
    refine ⟨22669275717157375518155719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120902803824839336096830501 22669275717157375518155719)
    ·
      refine ⟨34003913575736063277233579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22669275717157375518155719 34003913575736063277233579)
      ·
        refine ⟨51005870363604094915850369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34003913575736063277233579 51005870363604094915850369)
        ·
          refine ⟨38254402772703071186887777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51005870363604094915850369 38254402772703071186887777)
          ·
            refine ⟨28690802079527303390165833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38254402772703071186887777 28690802079527303390165833)
            ·
              refine ⟨21518101559645477542624375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28690802079527303390165833 21518101559645477542624375)
              ·
                refine ⟨32277152339468216313936563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21518101559645477542624375 32277152339468216313936563)
                ·
                  refine ⟨48415728509202324470904845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32277152339468216313936563 48415728509202324470904845)
                  ·
                    refine ⟨18155898190950871676589317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48415728509202324470904845 18155898190950871676589317)
                    ·
                      refine ⟨3404230910803288439360497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18155898190950871676589317 3404230910803288439360497)
                      ·
                        rfl

theorem cell23_6629716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_6629716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629716 prefixEnd_6629716 := by exact prefixLift 6629716
  have htrace : WordTrace (prefixWord ++ tailWord_6629716) baseStart_6629716 baseEnd_6629716 := by
    simpa [prefixWord, tailWord_6629716, baseEnd_6629716] using wordTrace_append hprefix tailTrace_6629716
  have hstable : (prefixWord ++ tailWord_6629716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629716).length < 2 ^ (prefixWord ++ tailWord_6629716).sum := by decide
  have hdescent : baseEnd_6629716 < baseStart_6629716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629790 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 6]
def baseStart_6629790 : Nat := 118140960795 + 6629790 * 2 ^ 59
def prefixEnd_6629790 : Nat := 4983230072969 + 3 ^ 40 * 6629790 * 2
def baseEnd_6629790 : Nat := 378252100930191238870573

theorem tailTrace_6629790 : CollatzResearch.WordTrace tailWord_6629790 prefixEnd_6629790 378252100930191238870573 := by
  unfold tailWord_6629790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30226038331426322853981853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161205537767607055221236549 30226038331426322853981853)
  ·
    refine ⟨11334764374284871070243195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30226038331426322853981853 11334764374284871070243195)
    ·
      refine ⟨17002146561427306605364793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11334764374284871070243195 17002146561427306605364793)
      ·
        refine ⟨12751609921070479954023595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17002146561427306605364793 12751609921070479954023595)
        ·
          refine ⟨19127414881605719931035393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12751609921070479954023595 19127414881605719931035393)
          ·
            refine ⟨14345561161204289948276545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19127414881605719931035393 14345561161204289948276545)
            ·
              refine ⟨10759170870903217461207409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14345561161204289948276545 10759170870903217461207409)
              ·
                refine ⟨8069378153177413095905557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10759170870903217461207409 8069378153177413095905557)
                ·
                  refine ⟨378252100930191238870573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8069378153177413095905557 378252100930191238870573)
                  ·
                    rfl

theorem cell23_6629790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_6629790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629790 prefixEnd_6629790 := by exact prefixLift 6629790
  have htrace : WordTrace (prefixWord ++ tailWord_6629790) baseStart_6629790 baseEnd_6629790 := by
    simpa [prefixWord, tailWord_6629790, baseEnd_6629790] using wordTrace_append hprefix tailTrace_6629790
  have hstable : (prefixWord ++ tailWord_6629790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629790).length < 2 ^ (prefixWord ++ tailWord_6629790).sum := by decide
  have hdescent : baseEnd_6629790 < baseStart_6629790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629816 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 6, 4]
def baseStart_6629816 : Nat := 118140960795 + 6629816 * 2 ^ 59
def prefixEnd_6629816 : Nat := 4983230072969 + 3 ^ 40 * 6629816 * 2
def baseEnd_6629816 : Nat := 1134760752956246016036679

theorem tailTrace_6629816 : CollatzResearch.WordTrace tailWord_6629816 prefixEnd_6629816 1134760752956246016036679 := by
  unfold tailWord_6629816
  simp only [CollatzResearch.WordTrace]
  refine ⟨120904627474658194636150651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161206169966210926181534201 120904627474658194636150651)
  ·
    refine ⟨181356941211987291954225977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120904627474658194636150651 181356941211987291954225977)
    ·
      refine ⟨136017705908990468965669483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181356941211987291954225977 136017705908990468965669483)
      ·
        refine ⟨204026558863485703448504225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136017705908990468965669483 204026558863485703448504225)
        ·
          refine ⟨153019919147614277586378169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204026558863485703448504225 153019919147614277586378169)
          ·
            refine ⟨114764939360710708189783627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153019919147614277586378169 114764939360710708189783627)
            ·
              refine ⟨172147409041066062284675441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114764939360710708189783627 172147409041066062284675441)
              ·
                refine ⟨129110556780799546713506581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172147409041066062284675441 129110556780799546713506581)
                ·
                  refine ⟨6052057349099978752195621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129110556780799546713506581 6052057349099978752195621)
                  ·
                    refine ⟨1134760752956246016036679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052057349099978752195621 1134760752956246016036679)
                    ·
                      rfl

theorem cell23_6629816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_6629816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629816 prefixEnd_6629816 := by exact prefixLift 6629816
  have htrace : WordTrace (prefixWord ++ tailWord_6629816) baseStart_6629816 baseEnd_6629816 := by
    simpa [prefixWord, tailWord_6629816, baseEnd_6629816] using wordTrace_append hprefix tailTrace_6629816
  have hstable : (prefixWord ++ tailWord_6629816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629816).length < 2 ^ (prefixWord ++ tailWord_6629816).sum := by decide
  have hdescent : baseEnd_6629816 < baseStart_6629816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629857 : List Nat := [1, 2, 3, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_6629857 : Nat := 118140960795 + 6629857 * 2 ^ 59
def prefixEnd_6629857 : Nat := 4983230072969 + 3 ^ 40 * 6629857 * 2
def baseEnd_6629857 : Nat := 3404303311575572387697349

theorem tailTrace_6629857 : CollatzResearch.WordTrace tailWord_6629857 prefixEnd_6629857 3404303311575572387697349 := by
  unfold tailWord_6629857
  simp only [CollatzResearch.WordTrace]
  refine ⟨241810750342167853274543825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161207166894778568849695883 241810750342167853274543825)
  ·
    refine ⟨181358062756625889955907869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241810750342167853274543825 181358062756625889955907869)
    ·
      refine ⟨68009273533734708733465451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181358062756625889955907869 68009273533734708733465451)
      ·
        refine ⟨102013910300602063100198177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68009273533734708733465451 102013910300602063100198177)
        ·
          refine ⟨76510432725451547325148633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102013910300602063100198177 76510432725451547325148633)
          ·
            refine ⟨57382824544088660493861475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76510432725451547325148633 57382824544088660493861475)
            ·
              refine ⟨86074236816132990740792213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57382824544088660493861475 86074236816132990740792213)
              ·
                refine ⟨4034729850756233940974635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86074236816132990740792213 4034729850756233940974635)
                ·
                  refine ⟨6052094776134350911461953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034729850756233940974635 6052094776134350911461953)
                  ·
                    refine ⟨4539071082100763183596465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6052094776134350911461953 4539071082100763183596465)
                    ·
                      refine ⟨3404303311575572387697349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539071082100763183596465 3404303311575572387697349)
                      ·
                        rfl

theorem cell23_6629857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_6629857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629857 prefixEnd_6629857 := by exact prefixLift 6629857
  have htrace : WordTrace (prefixWord ++ tailWord_6629857) baseStart_6629857 baseEnd_6629857 := by
    simpa [prefixWord, tailWord_6629857, baseEnd_6629857] using wordTrace_append hprefix tailTrace_6629857
  have hstable : (prefixWord ++ tailWord_6629857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629857).length < 2 ^ (prefixWord ++ tailWord_6629857).sum := by decide
  have hdescent : baseEnd_6629857 < baseStart_6629857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629870 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_6629870 : Nat := 118140960795 + 6629870 * 2 ^ 59
def prefixEnd_6629870 : Nat := 4983230072969 + 3 ^ 40 * 6629870 * 2
def baseEnd_6629870 : Nat := 3404309986824080836834789

theorem tailTrace_6629870 : CollatzResearch.WordTrace tailWord_6629870 prefixEnd_6629870 3404309986824080836834789 := by
  unfold tailWord_6629870
  simp only [CollatzResearch.WordTrace]
  refine ⟨30226403061390094561845883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161207482994080504329844709 30226403061390094561845883)
  ·
    refine ⟨45339604592085141842768825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30226403061390094561845883 45339604592085141842768825)
    ·
      refine ⟨34004703444063856382076619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45339604592085141842768825 34004703444063856382076619)
      ·
        refine ⟨51007055166095784573114929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34004703444063856382076619 51007055166095784573114929)
        ·
          refine ⟨38255291374571838429836197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51007055166095784573114929 38255291374571838429836197)
          ·
            refine ⟨7172867132732219705594287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38255291374571838429836197 7172867132732219705594287)
            ·
              refine ⟨10759300699098329558391431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172867132732219705594287 10759300699098329558391431)
              ·
                refine ⟨16138951048647494337587147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759300699098329558391431 16138951048647494337587147)
                ·
                  refine ⟨24208426572971241506380721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16138951048647494337587147 24208426572971241506380721)
                  ·
                    refine ⟨18156319929728431129785541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24208426572971241506380721 18156319929728431129785541)
                    ·
                      refine ⟨3404309986824080836834789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18156319929728431129785541 3404309986824080836834789)
                      ·
                        rfl

theorem cell23_6629870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_6629870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629870 prefixEnd_6629870 := by exact prefixLift 6629870
  have htrace : WordTrace (prefixWord ++ tailWord_6629870) baseStart_6629870 baseEnd_6629870 := by
    simpa [prefixWord, tailWord_6629870, baseEnd_6629870] using wordTrace_append hprefix tailTrace_6629870
  have hstable : (prefixWord ++ tailWord_6629870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629870).length < 2 ^ (prefixWord ++ tailWord_6629870).sum := by decide
  have hdescent : baseEnd_6629870 < baseStart_6629870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629894 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6629894 : Nat := 118140960795 + 6629894 * 2 ^ 59
def prefixEnd_6629894 : Nat := 4983230072969 + 3 ^ 40 * 6629894 * 2
def baseEnd_6629894 : Nat := 3404322310359788742934679

theorem tailTrace_6629894 : CollatzResearch.WordTrace tailWord_6629894 prefixEnd_6629894 3404322310359788742934679 := by
  unfold tailWord_6629894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7556628120094806518551273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161208066562022539062427157 7556628120094806518551273)
  ·
    refine ⟨5667471090071104888913455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7556628120094806518551273 5667471090071104888913455)
    ·
      refine ⟨8501206635106657333370183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5667471090071104888913455 8501206635106657333370183)
      ·
        refine ⟨12751809952659986000055275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501206635106657333370183 12751809952659986000055275)
        ·
          refine ⟨19127714928989979000082913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12751809952659986000055275 19127714928989979000082913)
          ·
            refine ⟨14345786196742484250062185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19127714928989979000082913 14345786196742484250062185)
            ·
              refine ⟨10759339647556863187546639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14345786196742484250062185 10759339647556863187546639)
              ·
                refine ⟨16139009471335294781319959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759339647556863187546639 16139009471335294781319959)
                ·
                  refine ⟨24208514207002942171979939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16139009471335294781319959 24208514207002942171979939)
                  ·
                    refine ⟨36312771310504413257969909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24208514207002942171979939 36312771310504413257969909)
                    ·
                      refine ⟨3404322310359788742934679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36312771310504413257969909 3404322310359788742934679)
                      ·
                        rfl

theorem cell23_6629894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6629894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629894 prefixEnd_6629894 := by exact prefixLift 6629894
  have htrace : WordTrace (prefixWord ++ tailWord_6629894) baseStart_6629894 baseEnd_6629894 := by
    simpa [prefixWord, tailWord_6629894, baseEnd_6629894] using wordTrace_append hprefix tailTrace_6629894
  have hstable : (prefixWord ++ tailWord_6629894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629894).length < 2 ^ (prefixWord ++ tailWord_6629894).sum := by decide
  have hdescent : baseEnd_6629894 < baseStart_6629894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629896 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_6629896 : Nat := 118140960795 + 6629896 * 2 ^ 59
def prefixEnd_6629896 : Nat := 4983230072969 + 3 ^ 40 * 6629896 * 2
def baseEnd_6629896 : Nat := 3404323337321097735109669

theorem tailTrace_6629896 : CollatzResearch.WordTrace tailWord_6629896 prefixEnd_6629896 3404323337321097735109669 := by
  unfold tailWord_6629896
  simp only [CollatzResearch.WordTrace]
  refine ⟨120906086394513281467606771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161208115192684375290142361 120906086394513281467606771)
  ·
    refine ⟨181359129591769922201410157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120906086394513281467606771 181359129591769922201410157)
    ·
      refine ⟨68009673596913720825528809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181359129591769922201410157 68009673596913720825528809)
      ·
        refine ⟨51007255197685290619146607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68009673596913720825528809 51007255197685290619146607)
        ·
          refine ⟨76510882796527935928719911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51007255197685290619146607 76510882796527935928719911)
          ·
            refine ⟨114766324194791903893079867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76510882796527935928719911 114766324194791903893079867)
            ·
              refine ⟨172149486292187855839619801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114766324194791903893079867 172149486292187855839619801)
              ·
                refine ⟨129112114719140891879714851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172149486292187855839619801 129112114719140891879714851)
                ·
                  refine ⟨193668172078711337819572277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129112114719140891879714851 193668172078711337819572277)
                  ·
                    refine ⟨18156391132379187920584901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193668172078711337819572277 18156391132379187920584901)
                    ·
                      refine ⟨3404323337321097735109669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18156391132379187920584901 3404323337321097735109669)
                      ·
                        rfl

theorem cell23_6629896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_6629896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629896 prefixEnd_6629896 := by exact prefixLift 6629896
  have htrace : WordTrace (prefixWord ++ tailWord_6629896) baseStart_6629896 baseEnd_6629896 := by
    simpa [prefixWord, tailWord_6629896, baseEnd_6629896] using wordTrace_append hprefix tailTrace_6629896
  have hstable : (prefixWord ++ tailWord_6629896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629896).length < 2 ^ (prefixWord ++ tailWord_6629896).sum := by decide
  have hdescent : baseEnd_6629896 < baseStart_6629896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629908 : List Nat := [2, 4, 3, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6629908 : Nat := 118140960795 + 6629908 * 2 ^ 59
def prefixEnd_6629908 : Nat := 4983230072969 + 3 ^ 40 * 6629908 * 2
def baseEnd_6629908 : Nat := 3404329499088951688159615

theorem tailTrace_6629908 : CollatzResearch.WordTrace tailWord_6629908 prefixEnd_6629908 3404329499088951688159615 := by
  unfold tailWord_6629908
  simp only [CollatzResearch.WordTrace]
  refine ⟨120906305232491544492325189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161208406976655392656433585 120906305232491544492325189)
  ·
    refine ⟨22669932231092164592310973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120906305232491544492325189 22669932231092164592310973)
    ·
      refine ⟨8501224586659561722116615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22669932231092164592310973 8501224586659561722116615)
      ·
        refine ⟨12751836879989342583174923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501224586659561722116615 12751836879989342583174923)
        ·
          refine ⟨19127755319984013874762385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12751836879989342583174923 19127755319984013874762385)
          ·
            refine ⟨14345816489988010406071789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19127755319984013874762385 14345816489988010406071789)
            ·
              refine ⟨5379681183745503902276921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14345816489988010406071789 5379681183745503902276921)
              ·
                refine ⟨4034760887809127926707691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5379681183745503902276921 4034760887809127926707691)
                ·
                  refine ⟨6052141331713691890061537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034760887809127926707691 6052141331713691890061537)
                  ·
                    refine ⟨4539105998785268917546153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6052141331713691890061537 4539105998785268917546153)
                    ·
                      refine ⟨3404329499088951688159615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539105998785268917546153 3404329499088951688159615)
                      ·
                        rfl

theorem cell23_6629908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6629908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629908 prefixEnd_6629908 := by exact prefixLift 6629908
  have htrace : WordTrace (prefixWord ++ tailWord_6629908) baseStart_6629908 baseEnd_6629908 := by
    simpa [prefixWord, tailWord_6629908, baseEnd_6629908] using wordTrace_append hprefix tailTrace_6629908
  have hstable : (prefixWord ++ tailWord_6629908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629908).length < 2 ^ (prefixWord ++ tailWord_6629908).sum := by decide
  have hdescent : baseEnd_6629908 < baseStart_6629908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629913 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 3, 4, 2]
def baseStart_6629913 : Nat := 118140960795 + 6629913 * 2 ^ 59
def prefixEnd_6629913 : Nat := 4983230072969 + 3 ^ 40 * 6629913 * 2
def baseEnd_6629913 : Nat := 3404332066492224168597091

theorem tailTrace_6629913 : CollatzResearch.WordTrace tailWord_6629913 prefixEnd_6629913 3404332066492224168597091 := by
  unfold tailWord_6629913
  simp only [CollatzResearch.WordTrace]
  refine ⟨241812792829964974838582393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161208528553309983225721595 241812792829964974838582393)
  ·
    refine ⟨181359594622473731128936795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241812792829964974838582393 181359594622473731128936795)
    ·
      refine ⟨272039391933710596693405193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181359594622473731128936795 272039391933710596693405193)
      ·
        refine ⟨204029543950282947520053895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272039391933710596693405193 204029543950282947520053895)
        ·
          refine ⟨306044315925424421280080843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204029543950282947520053895 306044315925424421280080843)
          ·
            refine ⟨459066473888136631920121265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306044315925424421280080843 459066473888136631920121265)
            ·
              refine ⟨344299855416102473940090949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459066473888136631920121265 344299855416102473940090949)
              ·
                refine ⟨64556222890519213863767053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344299855416102473940090949 64556222890519213863767053)
                ·
                  refine ⟨24208583583944705198912645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64556222890519213863767053 24208583583944705198912645)
                  ·
                    refine ⟨4539109421989632224796121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24208583583944705198912645 4539109421989632224796121)
                    ·
                      refine ⟨3404332066492224168597091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539109421989632224796121 3404332066492224168597091)
                      ·
                        rfl

theorem cell23_6629913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_6629913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629913 prefixEnd_6629913 := by exact prefixLift 6629913
  have htrace : WordTrace (prefixWord ++ tailWord_6629913) baseStart_6629913 baseEnd_6629913 := by
    simpa [prefixWord, tailWord_6629913, baseEnd_6629913] using wordTrace_append hprefix tailTrace_6629913
  have hstable : (prefixWord ++ tailWord_6629913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629913).length < 2 ^ (prefixWord ++ tailWord_6629913).sum := by decide
  have hdescent : baseEnd_6629913 < baseStart_6629913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629924 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6629924 : Nat := 118140960795 + 6629924 * 2 ^ 59
def prefixEnd_6629924 : Nat := 4983230072969 + 3 ^ 40 * 6629924 * 2
def baseEnd_6629924 : Nat := 3404337714779423625559541

theorem tailTrace_6629924 : CollatzResearch.WordTrace tailWord_6629924 prefixEnd_6629924 3404337714779423625559541 := by
  unfold tailWord_6629924
  simp only [CollatzResearch.WordTrace]
  refine ⟨120906597016462561858616413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161208796021950082478155217 120906597016462561858616413)
  ·
    refine ⟨45339973881173460696981155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120906597016462561858616413 45339973881173460696981155)
    ·
      refine ⟨68009960821760191045471733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45339973881173460696981155 68009960821760191045471733)
      ·
        refine ⟨6375933827040017910512975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68009960821760191045471733 6375933827040017910512975)
        ·
          refine ⟨9563900740560026865769463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375933827040017910512975 9563900740560026865769463)
          ·
            refine ⟨14345851110840040298654195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9563900740560026865769463 14345851110840040298654195)
            ·
              refine ⟨21518776666260060447981293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14345851110840040298654195 21518776666260060447981293)
              ·
                refine ⟨8069541249847522667992985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21518776666260060447981293 8069541249847522667992985)
                ·
                  refine ⟨6052155937385642000994739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8069541249847522667992985 6052155937385642000994739)
                  ·
                    refine ⟨9078233906078463001492109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6052155937385642000994739 9078233906078463001492109)
                    ·
                      refine ⟨3404337714779423625559541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9078233906078463001492109 3404337714779423625559541)
                      ·
                        rfl

theorem cell23_6629924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6629924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629924 prefixEnd_6629924 := by exact prefixLift 6629924
  have htrace : WordTrace (prefixWord ++ tailWord_6629924) baseStart_6629924 baseEnd_6629924 := by
    simpa [prefixWord, tailWord_6629924, baseEnd_6629924] using wordTrace_append hprefix tailTrace_6629924
  have hstable : (prefixWord ++ tailWord_6629924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629924).length < 2 ^ (prefixWord ++ tailWord_6629924).sum := by decide
  have hdescent : baseEnd_6629924 < baseStart_6629924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629936 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 7]
def baseStart_6629936 : Nat := 118140960795 + 6629936 * 2 ^ 59
def prefixEnd_6629936 : Nat := 4983230072969 + 3 ^ 40 * 6629936 * 2
def baseEnd_6629936 : Nat := 378260430727475286512165

theorem tailTrace_6629936 : CollatzResearch.WordTrace tailWord_6629936 prefixEnd_6629936 378260430727475286512165 := by
  unfold tailWord_6629936
  simp only [CollatzResearch.WordTrace]
  refine ⟨120906815854440824883334831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161209087805921099844446441 120906815854440824883334831)
  ·
    refine ⟨181360223781661237325002247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120906815854440824883334831 181360223781661237325002247)
    ·
      refine ⟨272040335672491855987503371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181360223781661237325002247 272040335672491855987503371)
      ·
        refine ⟨408060503508737783981255057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272040335672491855987503371 408060503508737783981255057)
        ·
          refine ⟨306045377631553337985941293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408060503508737783981255057 306045377631553337985941293)
          ·
            refine ⟨114767016611832501744727985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306045377631553337985941293 114767016611832501744727985)
            ·
              refine ⟨86075262458874376308545989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114767016611832501744727985 86075262458874376308545989)
              ·
                refine ⟨16139111711038945557852373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86075262458874376308545989 16139111711038945557852373)
                ·
                  refine ⟨378260430727475286512165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16139111711038945557852373 378260430727475286512165)
                  ·
                    rfl

theorem cell23_6629936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_6629936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629936 prefixEnd_6629936 := by exact prefixLift 6629936
  have htrace : WordTrace (prefixWord ++ tailWord_6629936) baseStart_6629936 baseEnd_6629936 := by
    simpa [prefixWord, tailWord_6629936, baseEnd_6629936] using wordTrace_append hprefix tailTrace_6629936
  have hstable : (prefixWord ++ tailWord_6629936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629936).length < 2 ^ (prefixWord ++ tailWord_6629936).sum := by decide
  have hdescent : baseEnd_6629936 < baseStart_6629936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6629970 : List Nat := [3, 2, 2, 1, 2, 1, 3, 4, 5]
def baseStart_6629970 : Nat := 118140960795 + 6629970 * 2 ^ 59
def prefixEnd_6629970 : Nat := 4983230072969 + 3 ^ 40 * 6629970 * 2
def baseEnd_6629970 : Nat := 378262370543281160620481

theorem tailTrace_6629970 : CollatzResearch.WordTrace tailWord_6629970 prefixEnd_6629970 378262370543281160620481 := by
  unfold tailWord_6629970
  simp only [CollatzResearch.WordTrace]
  refine ⟨60453717947689618393351841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161209914527172315715604909 60453717947689618393351841)
  ·
    refine ⟨45340288460767213795013881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60453717947689618393351841 45340288460767213795013881)
    ·
      refine ⟨34005216345575410346260411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45340288460767213795013881 34005216345575410346260411)
      ·
        refine ⟨51007824518363115519390617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34005216345575410346260411 51007824518363115519390617)
        ·
          refine ⟨38255868388772336639542963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51007824518363115519390617 38255868388772336639542963)
          ·
            refine ⟨57383802583158504959314445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38255868388772336639542963 57383802583158504959314445)
            ·
              refine ⟨21518925968684439359742917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57383802583158504959314445 21518925968684439359742917)
              ·
                refine ⟨4034798619128332379951797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21518925968684439359742917 4034798619128332379951797)
                ·
                  refine ⟨378262370543281160620481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4034798619128332379951797 378262370543281160620481)
                  ·
                    rfl

theorem cell23_6629970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 5].length) (baseStart_6629970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6629970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6629970 prefixEnd_6629970 := by exact prefixLift 6629970
  have htrace : WordTrace (prefixWord ++ tailWord_6629970) baseStart_6629970 baseEnd_6629970 := by
    simpa [prefixWord, tailWord_6629970, baseEnd_6629970] using wordTrace_append hprefix tailTrace_6629970
  have hstable : (prefixWord ++ tailWord_6629970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6629970).length < 2 ^ (prefixWord ++ tailWord_6629970).sum := by decide
  have hdescent : baseEnd_6629970 < baseStart_6629970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6629970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630003 : List Nat := [1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 4]
def baseStart_6630003 : Nat := 118140960795 + 6630003 * 2 ^ 59
def prefixEnd_6630003 : Nat := 4983230072969 + 3 ^ 40 * 6630003 * 2
def baseEnd_6630003 : Nat := 3404378279751128816471677

theorem tailTrace_6630003 : CollatzResearch.WordTrace tailWord_6630003 prefixEnd_6630003 3404378279751128816471677 := by
  unfold tailWord_6630003
  simp only [CollatzResearch.WordTrace]
  refine ⟨241816075399638920209358663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161210716933092613472905775 241816075399638920209358663)
  ·
    refine ⟨362724113099458380314037995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241816075399638920209358663 362724113099458380314037995)
    ·
      refine ⟨544086169649187570471056993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362724113099458380314037995 544086169649187570471056993)
      ·
        refine ⟨408064627236890677853292745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544086169649187570471056993 408064627236890677853292745)
        ·
          refine ⟨306048470427668008389969559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408064627236890677853292745 306048470427668008389969559)
          ·
            refine ⟨459072705641502012584954339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306048470427668008389969559 459072705641502012584954339)
            ·
              refine ⟨688609058462253018877431509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459072705641502012584954339 688609058462253018877431509)
              ·
                refine ⟨16139274807709055129939801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 688609058462253018877431509 16139274807709055129939801)
                ·
                  refine ⟨12104456105781791347454851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16139274807709055129939801 12104456105781791347454851)
                  ·
                    refine ⟨18156684158672687021182277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12104456105781791347454851 18156684158672687021182277)
                    ·
                      refine ⟨3404378279751128816471677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18156684158672687021182277 3404378279751128816471677)
                      ·
                        rfl

theorem cell23_6630003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_6630003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630003 prefixEnd_6630003 := by exact prefixLift 6630003
  have htrace : WordTrace (prefixWord ++ tailWord_6630003) baseStart_6630003 baseEnd_6630003 := by
    simpa [prefixWord, tailWord_6630003, baseEnd_6630003] using wordTrace_append hprefix tailTrace_6630003
  have hstable : (prefixWord ++ tailWord_6630003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630003).length < 2 ^ (prefixWord ++ tailWord_6630003).sum := by decide
  have hdescent : baseEnd_6630003 < baseStart_6630003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630053 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_6630053 : Nat := 118140960795 + 6630053 * 2 ^ 59
def prefixEnd_6630053 : Nat := 4983230072969 + 3 ^ 40 * 6630053 * 2
def baseEnd_6630053 : Nat := 3404403953783853620846447

theorem tailTrace_6630053 : CollatzResearch.WordTrace tailWord_6630053 prefixEnd_6630053 3404403953783853620846447 := by
  unfold tailWord_6630053
  simp only [CollatzResearch.WordTrace]
  refine ⟨241817899049457778748678813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161211932699638519165785875 241817899049457778748678813)
  ·
    refine ⟨90681712143546667030754555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241817899049457778748678813 90681712143546667030754555)
    ·
      refine ⟨136022568215320000546131833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90681712143546667030754555 136022568215320000546131833)
      ·
        refine ⟨102016926161490000409598875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136022568215320000546131833 102016926161490000409598875)
        ·
          refine ⟨153025389242235000614398313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102016926161490000409598875 153025389242235000614398313)
          ·
            refine ⟨114769041931676250460798735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153025389242235000614398313 114769041931676250460798735)
            ·
              refine ⟨172153562897514375691198103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114769041931676250460798735 172153562897514375691198103)
              ·
                refine ⟨258230344346271563536797155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172153562897514375691198103 258230344346271563536797155)
                ·
                  refine ⟨387345516519407345305195733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258230344346271563536797155 387345516519407345305195733)
                  ·
                    refine ⟨9078410543423609655590525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 387345516519407345305195733 9078410543423609655590525)
                    ·
                      refine ⟨3404403953783853620846447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9078410543423609655590525 3404403953783853620846447)
                      ·
                        rfl

theorem cell23_6630053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_6630053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630053 prefixEnd_6630053 := by exact prefixLift 6630053
  have htrace : WordTrace (prefixWord ++ tailWord_6630053) baseStart_6630053 baseEnd_6630053 := by
    simpa [prefixWord, tailWord_6630053, baseEnd_6630053] using wordTrace_append hprefix tailTrace_6630053
  have hstable : (prefixWord ++ tailWord_6630053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630053).length < 2 ^ (prefixWord ++ tailWord_6630053).sum := by decide
  have hdescent : baseEnd_6630053 < baseStart_6630053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630073 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 5, 5]
def baseStart_6630073 : Nat := 118140960795 + 6630073 * 2 ^ 59
def prefixEnd_6630073 : Nat := 4983230072969 + 3 ^ 40 * 6630073 * 2
def baseEnd_6630073 : Nat := 1134804741132314514198785

theorem tailTrace_6630073 : CollatzResearch.WordTrace tailWord_6630073 prefixEnd_6630073 1134804741132314514198785 := by
  unfold tailWord_6630073
  simp only [CollatzResearch.WordTrace]
  refine ⟨241818628509385322164406873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161212419006256881442937915 241818628509385322164406873)
  ·
    refine ⟨181363971382038991623305155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241818628509385322164406873 181363971382038991623305155)
    ·
      refine ⟨272045957073058487434957733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181363971382038991623305155 272045957073058487434957733)
      ·
        refine ⟨51008616951198466394054575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272045957073058487434957733 51008616951198466394054575)
        ·
          refine ⟨76512925426797699591081863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51008616951198466394054575 76512925426797699591081863)
          ·
            refine ⟨114769388140196549386622795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76512925426797699591081863 114769388140196549386622795)
            ·
              refine ⟨172154082210294824079934193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114769388140196549386622795 172154082210294824079934193)
              ·
                refine ⟨129115561657721118059950645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172154082210294824079934193 129115561657721118059950645)
                ·
                  refine ⟨12104583905411354818120373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129115561657721118059950645 12104583905411354818120373)
                  ·
                    refine ⟨1134804741132314514198785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12104583905411354818120373 1134804741132314514198785)
                    ·
                      rfl

theorem cell23_6630073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_6630073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630073 prefixEnd_6630073 := by exact prefixLift 6630073
  have htrace : WordTrace (prefixWord ++ tailWord_6630073) baseStart_6630073 baseEnd_6630073 := by
    simpa [prefixWord, tailWord_6630073, baseEnd_6630073] using wordTrace_append hprefix tailTrace_6630073
  have hstable : (prefixWord ++ tailWord_6630073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630073).length < 2 ^ (prefixWord ++ tailWord_6630073).sum := by decide
  have hdescent : baseEnd_6630073 < baseStart_6630073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630081 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6630081 : Nat := 118140960795 + 6630081 * 2 ^ 59
def prefixEnd_6630081 : Nat := 4983230072969 + 3 ^ 40 * 6630081 * 2
def baseEnd_6630081 : Nat := 1134806110414059837098773

theorem tailTrace_6630081 : CollatzResearch.WordTrace tailWord_6630081 prefixEnd_6630081 1134806110414059837098773 := by
  unfold tailWord_6630081
  simp only [CollatzResearch.WordTrace]
  refine ⟨241818920293356339530698097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161212613528904226353798731 241818920293356339530698097)
  ·
    refine ⟨181364190220017254648023573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241818920293356339530698097 181364190220017254648023573)
    ·
      refine ⟨8501446416563308811626105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181364190220017254648023573 8501446416563308811626105)
      ·
        refine ⟨6376084812422481608719579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8501446416563308811626105 6376084812422481608719579)
        ·
          refine ⟨9564127218633722413079369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376084812422481608719579 9564127218633722413079369)
          ·
            refine ⟨7173095413975291809809527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9564127218633722413079369 7173095413975291809809527)
            ·
              refine ⟨10759643120962937714714291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173095413975291809809527 10759643120962937714714291)
              ·
                refine ⟨16139464681444406572071437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759643120962937714714291 16139464681444406572071437)
                ·
                  refine ⟨6052299255541652464526789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16139464681444406572071437 6052299255541652464526789)
                  ·
                    refine ⟨1134806110414059837098773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052299255541652464526789 1134806110414059837098773)
                    ·
                      rfl

theorem cell23_6630081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6630081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630081 prefixEnd_6630081 := by exact prefixLift 6630081
  have htrace : WordTrace (prefixWord ++ tailWord_6630081) baseStart_6630081 baseEnd_6630081 := by
    simpa [prefixWord, tailWord_6630081, baseEnd_6630081] using wordTrace_append hprefix tailTrace_6630081
  have hstable : (prefixWord ++ tailWord_6630081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630081).length < 2 ^ (prefixWord ++ tailWord_6630081).sum := by decide
  have hdescent : baseEnd_6630081 < baseStart_6630081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630132 : List Nat := [2, 6, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6630132 : Nat := 118140960795 + 6630132 * 2 ^ 59
def prefixEnd_6630132 : Nat := 4983230072969 + 3 ^ 40 * 6630132 * 2
def baseEnd_6630132 : Nat := 1134814839585186270586195

theorem tailTrace_6630132 : CollatzResearch.WordTrace tailWord_6630132 prefixEnd_6630132 1134814839585186270586195 := by
  unfold tailWord_6630132
  simp only [CollatzResearch.WordTrace]
  refine ⟨120910390208085787620402325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161213853610781050160536433 120910390208085787620402325)
  ·
    refine ⟨5667674541004021294706359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120910390208085787620402325 5667674541004021294706359)
    ·
      refine ⟨8501511811506031942059539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5667674541004021294706359 8501511811506031942059539)
      ·
        refine ⟨12752267717259047913089309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501511811506031942059539 12752267717259047913089309)
        ·
          refine ⟨4782100393972142967408491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12752267717259047913089309 4782100393972142967408491)
          ·
            refine ⟨7173150590958214451112737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782100393972142967408491 7173150590958214451112737)
            ·
              refine ⟨5379862943218660838334553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173150590958214451112737 5379862943218660838334553)
              ·
                refine ⟨4034897207413995628750915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5379862943218660838334553 4034897207413995628750915)
                ·
                  refine ⟨6052345811120993443126373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034897207413995628750915 6052345811120993443126373)
                  ·
                    refine ⟨1134814839585186270586195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052345811120993443126373 1134814839585186270586195)
                    ·
                      rfl

theorem cell23_6630132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6630132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630132 prefixEnd_6630132 := by exact prefixLift 6630132
  have htrace : WordTrace (prefixWord ++ tailWord_6630132) baseStart_6630132 baseEnd_6630132 := by
    simpa [prefixWord, tailWord_6630132, baseEnd_6630132] using wordTrace_append hprefix tailTrace_6630132
  have hstable : (prefixWord ++ tailWord_6630132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630132).length < 2 ^ (prefixWord ++ tailWord_6630132).sum := by decide
  have hdescent : baseEnd_6630132 < baseStart_6630132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630153 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_6630153 : Nat := 118140960795 + 6630153 * 2 ^ 59
def prefixEnd_6630153 : Nat := 4983230072969 + 3 ^ 40 * 6630153 * 2
def baseEnd_6630153 : Nat := 3404455301849303229595987

theorem tailTrace_6630153 : CollatzResearch.WordTrace tailWord_6630153 prefixEnd_6630153 3404455301849303229595987 := by
  unfold tailWord_6630153
  simp only [CollatzResearch.WordTrace]
  refine ⟨241821546349095495827319113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161214364232730330551546075 241821546349095495827319113)
  ·
    refine ⟨181366159761821621870489335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241821546349095495827319113 181366159761821621870489335)
    ·
      refine ⟨272049239642732432805734003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181366159761821621870489335 272049239642732432805734003)
      ·
        refine ⟨408073859464098649208601005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272049239642732432805734003 408073859464098649208601005)
        ·
          refine ⟨153027697299036993453225377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408073859464098649208601005 153027697299036993453225377)
          ·
            refine ⟨114770772974277745089919033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153027697299036993453225377 114770772974277745089919033)
            ·
              refine ⟨86078079730708308817439275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114770772974277745089919033 86078079730708308817439275)
              ·
                refine ⟨129117119596062463226158913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86078079730708308817439275 129117119596062463226158913)
                ·
                  refine ⟨96837839697046847419619185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129117119596062463226158913 96837839697046847419619185)
                  ·
                    refine ⟨72628379772785135564714389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96837839697046847419619185 72628379772785135564714389)
                    ·
                      refine ⟨3404455301849303229595987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72628379772785135564714389 3404455301849303229595987)
                      ·
                        rfl

theorem cell23_6630153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_6630153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630153 prefixEnd_6630153 := by exact prefixLift 6630153
  have htrace : WordTrace (prefixWord ++ tailWord_6630153) baseStart_6630153 baseEnd_6630153 := by
    simpa [prefixWord, tailWord_6630153, baseEnd_6630153] using wordTrace_append hprefix tailTrace_6630153
  have hstable : (prefixWord ++ tailWord_6630153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630153).length < 2 ^ (prefixWord ++ tailWord_6630153).sum := by decide
  have hdescent : baseEnd_6630153 < baseStart_6630153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630163 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 2, 7]
def baseStart_6630163 : Nat := 118140960795 + 6630163 * 2 ^ 59
def prefixEnd_6630163 : Nat := 4983230072969 + 3 ^ 40 * 6630163 * 2
def baseEnd_6630163 : Nat := 1134820145551949396823647

theorem tailTrace_6630163 : CollatzResearch.WordTrace tailWord_6630163 prefixEnd_6630163 1134820145551949396823647 := by
  unfold tailWord_6630163
  simp only [CollatzResearch.WordTrace]
  refine ⟨241821911079059267535183143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161214607386039511690122095 241821911079059267535183143)
  ·
    refine ⟨362732866618588901302774715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241821911079059267535183143 362732866618588901302774715)
    ·
      refine ⟨544099299927883351954162073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362732866618588901302774715 544099299927883351954162073)
      ·
        refine ⟨408074474945912513965621555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544099299927883351954162073 408074474945912513965621555)
        ·
          refine ⟨612111712418868770948432333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408074474945912513965621555 612111712418868770948432333)
          ·
            refine ⟨229541892157075789105662125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612111712418868770948432333 229541892157075789105662125)
            ·
              refine ⟨86078209558903420914623297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229541892157075789105662125 86078209558903420914623297)
              ·
                refine ⟨64558657169177565685967473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86078209558903420914623297 64558657169177565685967473)
                ·
                  refine ⟨48418992876883174264475605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64558657169177565685967473 48418992876883174264475605)
                  ·
                    refine ⟨1134820145551949396823647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48418992876883174264475605 1134820145551949396823647)
                    ·
                      rfl

theorem cell23_6630163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 7].length) (baseStart_6630163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630163 prefixEnd_6630163 := by exact prefixLift 6630163
  have htrace : WordTrace (prefixWord ++ tailWord_6630163) baseStart_6630163 baseEnd_6630163 := by
    simpa [prefixWord, tailWord_6630163, baseEnd_6630163] using wordTrace_append hprefix tailTrace_6630163
  have hstable : (prefixWord ++ tailWord_6630163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630163).length < 2 ^ (prefixWord ++ tailWord_6630163).sum := by decide
  have hdescent : baseEnd_6630163 < baseStart_6630163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630167 : List Nat := [1, 1, 3, 4, 3, 1, 3, 7]
def baseStart_6630167 : Nat := 118140960795 + 6630167 * 2 ^ 59
def prefixEnd_6630167 : Nat := 4983230072969 + 3 ^ 40 * 6630167 * 2
def baseEnd_6630167 : Nat := 126091203354758006474849

theorem tailTrace_6630167 : CollatzResearch.WordTrace tailWord_6630167 prefixEnd_6630167 126091203354758006474849 := by
  unfold tailWord_6630167
  simp only [CollatzResearch.WordTrace]
  refine ⟨241822056971044776218328755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161214704647363184145552503 241822056971044776218328755)
  ·
    refine ⟨362733085456567164327493133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241822056971044776218328755 362733085456567164327493133)
    ·
      refine ⟨136024907046212686622809925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362733085456567164327493133 136024907046212686622809925)
      ·
        refine ⟨25504670071164878741776861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136024907046212686622809925 25504670071164878741776861)
        ·
          refine ⟨9564251276686829528166323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25504670071164878741776861 9564251276686829528166323)
          ·
            refine ⟨14346376915030244292249485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564251276686829528166323 14346376915030244292249485)
            ·
              refine ⟨5379891343136341609593557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14346376915030244292249485 5379891343136341609593557)
              ·
                refine ⟨126091203354758006474849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5379891343136341609593557 126091203354758006474849)
                ·
                  rfl

theorem cell23_6630167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 7].length) (baseStart_6630167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630167 prefixEnd_6630167 := by exact prefixLift 6630167
  have htrace : WordTrace (prefixWord ++ tailWord_6630167) baseStart_6630167 baseEnd_6630167 := by
    simpa [prefixWord, tailWord_6630167, baseEnd_6630167] using wordTrace_append hprefix tailTrace_6630167
  have hstable : (prefixWord ++ tailWord_6630167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630167).length < 2 ^ (prefixWord ++ tailWord_6630167).sum := by decide
  have hdescent : baseEnd_6630167 < baseStart_6630167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630177 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_6630177 : Nat := 118140960795 + 6630177 * 2 ^ 59
def prefixEnd_6630177 : Nat := 4983230072969 + 3 ^ 40 * 6630177 * 2
def baseEnd_6630177 : Nat := 3404467625385011135695877

theorem tailTrace_6630177 : CollatzResearch.WordTrace tailWord_6630177 prefixEnd_6630177 3404467625385011135695877 := by
  unfold tailWord_6630177
  simp only [CollatzResearch.WordTrace]
  refine ⟨241822421701008547926192785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161214947800672365284128523 241822421701008547926192785)
  ·
    refine ⟨181366816275756410944644589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241822421701008547926192785 181366816275756410944644589)
    ·
      refine ⟨68012556103408654104241721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181366816275756410944644589 68012556103408654104241721)
      ·
        refine ⟨51009417077556490578181291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68012556103408654104241721 51009417077556490578181291)
        ·
          refine ⟨76514125616334735867271937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51009417077556490578181291 76514125616334735867271937)
          ·
            refine ⟨57385594212251051900453953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76514125616334735867271937 57385594212251051900453953)
            ·
              refine ⟨43039195659188288925340465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57385594212251051900453953 43039195659188288925340465)
              ·
                refine ⟨32279396744391216694005349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43039195659188288925340465 32279396744391216694005349)
                ·
                  refine ⟨6052386889573353130126003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32279396744391216694005349 6052386889573353130126003)
                  ·
                    refine ⟨9078580334360029695189005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6052386889573353130126003 9078580334360029695189005)
                    ·
                      refine ⟨3404467625385011135695877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9078580334360029695189005 3404467625385011135695877)
                      ·
                        rfl

theorem cell23_6630177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_6630177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630177 prefixEnd_6630177 := by exact prefixLift 6630177
  have htrace : WordTrace (prefixWord ++ tailWord_6630177) baseStart_6630177 baseEnd_6630177 := by
    simpa [prefixWord, tailWord_6630177, baseEnd_6630177] using wordTrace_append hprefix tailTrace_6630177
  have hstable : (prefixWord ++ tailWord_6630177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630177).length < 2 ^ (prefixWord ++ tailWord_6630177).sum := by decide
  have hdescent : baseEnd_6630177 < baseStart_6630177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630178 : List Nat := [3, 3, 1, 1, 2, 3, 2, 3, 1, 2, 2]
def baseStart_6630178 : Nat := 118140960795 + 6630178 * 2 ^ 59
def prefixEnd_6630178 : Nat := 4983230072969 + 3 ^ 40 * 6630178 * 2
def baseEnd_6630178 : Nat := 3404468138865665631783373

theorem tailTrace_6630178 : CollatzResearch.WordTrace tailWord_6630178 prefixEnd_6630178 3404468138865665631783373 := by
  unfold tailWord_6630178
  simp only [CollatzResearch.WordTrace]
  refine ⟨60455614543501231274244797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161214972116003283397986125 60455614543501231274244797)
  ·
    refine ⟨22670855453812961727841799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60455614543501231274244797 22670855453812961727841799)
    ·
      refine ⟨34006283180719442591762699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22670855453812961727841799 34006283180719442591762699)
      ·
        refine ⟨51009424771079163887644049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34006283180719442591762699 51009424771079163887644049)
        ·
          refine ⟨38257068578309372915733037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51009424771079163887644049 38257068578309372915733037)
          ·
            refine ⟨14346400716866014843399889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38257068578309372915733037 14346400716866014843399889)
            ·
              refine ⟨10759800537649511132549917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14346400716866014843399889 10759800537649511132549917)
              ·
                refine ⟨4034925201618566674706219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10759800537649511132549917 4034925201618566674706219)
                ·
                  refine ⟨6052387802427850012059329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034925201618566674706219 6052387802427850012059329)
                  ·
                    refine ⟨4539290851820887509044497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6052387802427850012059329 4539290851820887509044497)
                    ·
                      refine ⟨3404468138865665631783373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539290851820887509044497 3404468138865665631783373)
                      ·
                        rfl

theorem cell23_6630178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_6630178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630178 prefixEnd_6630178 := by exact prefixLift 6630178
  have htrace : WordTrace (prefixWord ++ tailWord_6630178) baseStart_6630178 baseEnd_6630178 := by
    simpa [prefixWord, tailWord_6630178, baseEnd_6630178] using wordTrace_append hprefix tailTrace_6630178
  have hstable : (prefixWord ++ tailWord_6630178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630178).length < 2 ^ (prefixWord ++ tailWord_6630178).sum := by decide
  have hdescent : baseEnd_6630178 < baseStart_6630178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630234 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2]
def baseStart_6630234 : Nat := 118140960795 + 6630234 * 2 ^ 59
def prefixEnd_6630234 : Nat := 4983230072969 + 3 ^ 40 * 6630234 * 2
def baseEnd_6630234 : Nat := 3404496893782317412683115

theorem tailTrace_6630234 : CollatzResearch.WordTrace tailWord_6630234 prefixEnd_6630234 3404496893782317412683115 := by
  unfold tailWord_6630234
  simp only [CollatzResearch.WordTrace]
  refine ⟨60456125165450511665254439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161216333774534697774011837 60456125165450511665254439)
  ·
    refine ⟨90684187748175767497881659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60456125165450511665254439 90684187748175767497881659)
    ·
      refine ⟨136026281622263651246822489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90684187748175767497881659 136026281622263651246822489)
      ·
        refine ⟨102019711216697738435116867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136026281622263651246822489 102019711216697738435116867)
        ·
          refine ⟨153029566825046607652675301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102019711216697738435116867 153029566825046607652675301)
          ·
            refine ⟨28693043779696238934876619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153029566825046607652675301 28693043779696238934876619)
            ·
              refine ⟨43039565669544358402314929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28693043779696238934876619 43039565669544358402314929)
              ·
                refine ⟨32279674252158268801736197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43039565669544358402314929 32279674252158268801736197)
                ·
                  refine ⟨6052438922279675400325537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32279674252158268801736197 6052438922279675400325537)
                  ·
                    refine ⟨4539329191709756550244153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6052438922279675400325537 4539329191709756550244153)
                    ·
                      refine ⟨3404496893782317412683115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539329191709756550244153 3404496893782317412683115)
                      ·
                        rfl

theorem cell23_6630234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_6630234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630234 prefixEnd_6630234 := by exact prefixLift 6630234
  have htrace : WordTrace (prefixWord ++ tailWord_6630234) baseStart_6630234 baseEnd_6630234 := by
    simpa [prefixWord, tailWord_6630234, baseEnd_6630234] using wordTrace_append hprefix tailTrace_6630234
  have hstable : (prefixWord ++ tailWord_6630234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630234).length < 2 ^ (prefixWord ++ tailWord_6630234).sum := by decide
  have hdescent : baseEnd_6630234 < baseStart_6630234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630257 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 7]
def baseStart_6630257 : Nat := 118140960795 + 6630257 * 2 ^ 59
def prefixEnd_6630257 : Nat := 4983230072969 + 3 ^ 40 * 6630257 * 2
def baseEnd_6630257 : Nat := 378278744870818980299501

theorem tailTrace_6630257 : CollatzResearch.WordTrace tailWord_6630257 prefixEnd_6630257 378278744870818980299501 := by
  unfold tailWord_6630257
  simp only [CollatzResearch.WordTrace]
  refine ⟨241825339540718721589105025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161216893027145814392736683 241825339540718721589105025)
  ·
    refine ⟨181369004655539041191828769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241825339540718721589105025 181369004655539041191828769)
    ·
      refine ⟨136026753491654280893871577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181369004655539041191828769 136026753491654280893871577)
      ·
        refine ⟨102020065118740710670403683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136026753491654280893871577 102020065118740710670403683)
        ·
          refine ⟨153030097678111066005605525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102020065118740710670403683 153030097678111066005605525)
          ·
            refine ⟨7173285828661456219012759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153030097678111066005605525 7173285828661456219012759)
            ·
              refine ⟨10759928742992184328519139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173285828661456219012759 10759928742992184328519139)
              ·
                refine ⟨16139893114488276492778709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10759928742992184328519139 16139893114488276492778709)
                ·
                  refine ⟨378278744870818980299501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16139893114488276492778709 378278744870818980299501)
                  ·
                    rfl

theorem cell23_6630257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 7].length) (baseStart_6630257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630257 prefixEnd_6630257 := by exact prefixLift 6630257
  have htrace : WordTrace (prefixWord ++ tailWord_6630257) baseStart_6630257 baseEnd_6630257 := by
    simpa [prefixWord, tailWord_6630257, baseEnd_6630257] using wordTrace_append hprefix tailTrace_6630257
  have hstable : (prefixWord ++ tailWord_6630257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630257).length < 2 ^ (prefixWord ++ tailWord_6630257).sum := by decide
  have hdescent : baseEnd_6630257 < baseStart_6630257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630307 : List Nat := [1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 4]
def baseStart_6630307 : Nat := 118140960795 + 6630307 * 2 ^ 59
def prefixEnd_6630307 : Nat := 4983230072969 + 3 ^ 40 * 6630307 * 2
def baseEnd_6630307 : Nat := 3404534377870095627070279

theorem tailTrace_6630307 : CollatzResearch.WordTrace tailWord_6630307 prefixEnd_6630307 3404534377870095627070279 := by
  unfold tailWord_6630307
  simp only [CollatzResearch.WordTrace]
  refine ⟨241827163190537580128425175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161218108793691720085616783 241827163190537580128425175)
  ·
    refine ⟨362740744785806370192637763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241827163190537580128425175 362740744785806370192637763)
    ·
      refine ⟨544111117178709555288956645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362740744785806370192637763 544111117178709555288956645)
      ·
        refine ⟨102020834471008041616679371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 544111117178709555288956645 102020834471008041616679371)
        ·
          refine ⟨153031251706512062425019057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102020834471008041616679371 153031251706512062425019057)
          ·
            refine ⟨114773438779884046818764293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153031251706512062425019057 114773438779884046818764293)
            ·
              refine ⟨21520019771228258778518305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114773438779884046818764293 21520019771228258778518305)
              ·
                refine ⟨16140014828421194083888729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21520019771228258778518305 16140014828421194083888729)
                ·
                  refine ⟨12105011121315895562916547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16140014828421194083888729 12105011121315895562916547)
                  ·
                    refine ⟨18157516681973843344374821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12105011121315895562916547 18157516681973843344374821)
                    ·
                      refine ⟨3404534377870095627070279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18157516681973843344374821 3404534377870095627070279)
                      ·
                        rfl

theorem cell23_6630307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_6630307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630307 prefixEnd_6630307 := by exact prefixLift 6630307
  have htrace : WordTrace (prefixWord ++ tailWord_6630307) baseStart_6630307 baseEnd_6630307 := by
    simpa [prefixWord, tailWord_6630307, baseEnd_6630307] using wordTrace_append hprefix tailTrace_6630307
  have hstable : (prefixWord ++ tailWord_6630307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630307).length < 2 ^ (prefixWord ++ tailWord_6630307).sum := by decide
  have hdescent : baseEnd_6630307 < baseStart_6630307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630327 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_6630327 : Nat := 118140960795 + 6630327 * 2 ^ 59
def prefixEnd_6630327 : Nat := 4983230072969 + 3 ^ 40 * 6630327 * 2
def baseEnd_6630327 : Nat := 3404544647483185548820187

theorem tailTrace_6630327 : CollatzResearch.WordTrace tailWord_6630327 prefixEnd_6630327 3404544647483185548820187 := by
  unfold tailWord_6630327
  simp only [CollatzResearch.WordTrace]
  refine ⟨241827892650465123544153235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161218595100310082362768823 241827892650465123544153235)
  ·
    refine ⟨362741838975697685316229853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241827892650465123544153235 362741838975697685316229853)
    ·
      refine ⟨136028189615886631993586195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362741838975697685316229853 136028189615886631993586195)
      ·
        refine ⟨204042284423829947990379293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136028189615886631993586195 204042284423829947990379293)
        ·
          refine ⟨76515856658936230496392235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204042284423829947990379293 76515856658936230496392235)
          ·
            refine ⟨114773784988404345744588353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76515856658936230496392235 114773784988404345744588353)
            ·
              refine ⟨86080338741303259308441265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114773784988404345744588353 86080338741303259308441265)
              ·
                refine ⟨64560254055977444481330949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86080338741303259308441265 64560254055977444481330949)
                ·
                  refine ⟨12105047635495770840249553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64560254055977444481330949 12105047635495770840249553)
                  ·
                    refine ⟨9078785726621828130187165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12105047635495770840249553 9078785726621828130187165)
                    ·
                      refine ⟨3404544647483185548820187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9078785726621828130187165 3404544647483185548820187)
                      ·
                        rfl

theorem cell23_6630327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_6630327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630327 prefixEnd_6630327 := by exact prefixLift 6630327
  have htrace : WordTrace (prefixWord ++ tailWord_6630327) baseStart_6630327 baseEnd_6630327 := by
    simpa [prefixWord, tailWord_6630327, baseEnd_6630327] using wordTrace_append hprefix tailTrace_6630327
  have hstable : (prefixWord ++ tailWord_6630327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630327).length < 2 ^ (prefixWord ++ tailWord_6630327).sum := by decide
  have hdescent : baseEnd_6630327 < baseStart_6630327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630334 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_6630334 : Nat := 118140960795 + 6630334 * 2 ^ 59
def prefixEnd_6630334 : Nat := 4983230072969 + 3 ^ 40 * 6630334 * 2
def baseEnd_6630334 : Nat := 1134849413949255673810885

theorem tailTrace_6630334 : CollatzResearch.WordTrace tailWord_6630334 prefixEnd_6630334 1134849413949255673810885 := by
  unfold tailWord_6630334
  simp only [CollatzResearch.WordTrace]
  refine ⟨30228518495179970467457257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161218765307626509159772037 30228518495179970467457257)
  ·
    refine ⟨22671388871384977850592943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30228518495179970467457257 22671388871384977850592943)
    ·
      refine ⟨34007083307077466775889415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22671388871384977850592943 34007083307077466775889415)
      ·
        refine ⟨51010624960616200163834123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34007083307077466775889415 51010624960616200163834123)
        ·
          refine ⟨76515937440924300245751185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51010624960616200163834123 76515937440924300245751185)
          ·
            refine ⟨57386953080693225184313389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76515937440924300245751185 57386953080693225184313389)
            ·
              refine ⟨21520107405259959444117521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57386953080693225184313389 21520107405259959444117521)
              ·
                refine ⟨16140080553944969583088141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21520107405259959444117521 16140080553944969583088141)
                ·
                  refine ⟨6052530207729363593658053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16140080553944969583088141 6052530207729363593658053)
                  ·
                    refine ⟨1134849413949255673810885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052530207729363593658053 1134849413949255673810885)
                    ·
                      rfl

theorem cell23_6630334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_6630334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630334 prefixEnd_6630334 := by exact prefixLift 6630334
  have htrace : WordTrace (prefixWord ++ tailWord_6630334) baseStart_6630334 baseEnd_6630334 := by
    simpa [prefixWord, tailWord_6630334, baseEnd_6630334] using wordTrace_append hprefix tailTrace_6630334
  have hstable : (prefixWord ++ tailWord_6630334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630334).length < 2 ^ (prefixWord ++ tailWord_6630334).sum := by decide
  have hdescent : baseEnd_6630334 < baseStart_6630334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630342 : List Nat := [6, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_6630342 : Nat := 118140960795 + 6630342 * 2 ^ 59
def prefixEnd_6630342 : Nat := 4983230072969 + 3 ^ 40 * 6630342 * 2
def baseEnd_6630342 : Nat := 378283594410333665570291

theorem tailTrace_6630342 : CollatzResearch.WordTrace tailWord_6630342 prefixEnd_6630342 378283594410333665570291 := by
  unfold tailWord_6630342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557138742044086909560915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161218959830273854070632853 7557138742044086909560915)
  ·
    refine ⟨11335708113066130364341373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7557138742044086909560915 11335708113066130364341373)
    ·
      refine ⟨4250890542399798886628015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11335708113066130364341373 4250890542399798886628015)
      ·
        refine ⟨6376335813599698329942023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4250890542399798886628015 6376335813599698329942023)
        ·
          refine ⟨9564503720399547494913035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376335813599698329942023 9564503720399547494913035)
          ·
            refine ⟨14346755580599321242369553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564503720399547494913035 14346755580599321242369553)
            ·
              refine ⟨10760066685449490931777165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14346755580599321242369553 10760066685449490931777165)
              ·
                refine ⟨4035025007043559099416437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10760066685449490931777165 4035025007043559099416437)
                ·
                  refine ⟨378283594410333665570291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4035025007043559099416437 378283594410333665570291)
                  ·
                    rfl

theorem cell23_6630342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_6630342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630342 prefixEnd_6630342 := by exact prefixLift 6630342
  have htrace : WordTrace (prefixWord ++ tailWord_6630342) baseStart_6630342 baseEnd_6630342 := by
    simpa [prefixWord, tailWord_6630342, baseEnd_6630342] using wordTrace_append hprefix tailTrace_6630342
  have hstable : (prefixWord ++ tailWord_6630342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630342).length < 2 ^ (prefixWord ++ tailWord_6630342).sum := by decide
  have hdescent : baseEnd_6630342 < baseStart_6630342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630344 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_6630344 : Nat := 118140960795 + 6630344 * 2 ^ 59
def prefixEnd_6630344 : Nat := 4983230072969 + 3 ^ 40 * 6630344 * 2
def baseEnd_6630344 : Nat := 3404553376654311982307609

theorem tailTrace_6630344 : CollatzResearch.WordTrace tailWord_6630344 prefixEnd_6630344 3404553376654311982307609 := by
  unfold tailWord_6630344
  simp only [CollatzResearch.WordTrace]
  refine ⟨120914256345701767723761043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161219008460935690298348057 120914256345701767723761043)
  ·
    refine ⟨181371384518552651585641565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120914256345701767723761043 181371384518552651585641565)
    ·
      refine ⟨68014269194457244344615587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181371384518552651585641565 68014269194457244344615587)
      ·
        refine ⟨102021403791685866516923381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68014269194457244344615587 102021403791685866516923381)
        ·
          refine ⟨9564506605470549985961567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102021403791685866516923381 9564506605470549985961567)
          ·
            refine ⟨14346759908205824978942351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564506605470549985961567 14346759908205824978942351)
            ·
              refine ⟨21520139862308737468413527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14346759908205824978942351 21520139862308737468413527)
              ·
                refine ⟨32280209793463106202620291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21520139862308737468413527 32280209793463106202620291)
                ·
                  refine ⟨48420314690194659303930437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32280209793463106202620291 48420314690194659303930437)
                  ·
                    refine ⟨9078809004411498619486957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48420314690194659303930437 9078809004411498619486957)
                    ·
                      refine ⟨3404553376654311982307609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9078809004411498619486957 3404553376654311982307609)
                      ·
                        rfl

theorem cell23_6630344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_6630344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630344 prefixEnd_6630344 := by exact prefixLift 6630344
  have htrace : WordTrace (prefixWord ++ tailWord_6630344) baseStart_6630344 baseEnd_6630344 := by
    simpa [prefixWord, tailWord_6630344, baseEnd_6630344] using wordTrace_append hprefix tailTrace_6630344
  have hstable : (prefixWord ++ tailWord_6630344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630344).length < 2 ^ (prefixWord ++ tailWord_6630344).sum := by decide
  have hdescent : baseEnd_6630344 < baseStart_6630344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630351 : List Nat := [1, 1, 2, 1, 1, 7, 2, 3, 1, 4]
def baseStart_6630351 : Nat := 118140960795 + 6630351 * 2 ^ 59
def prefixEnd_6630351 : Nat := 4983230072969 + 3 ^ 40 * 6630351 * 2
def baseEnd_6630351 : Nat := 1134852323672964484973359

theorem tailTrace_6630351 : CollatzResearch.WordTrace tailWord_6630351 prefixEnd_6630351 1134852323672964484973359 := by
  unfold tailWord_6630351
  simp only [CollatzResearch.WordTrace]
  refine ⟨241828768002378175643026907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161219178668252117095351271 241828768002378175643026907)
  ·
    refine ⟨362743152003567263464540361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241828768002378175643026907 362743152003567263464540361)
    ·
      refine ⟨272057364002675447598405271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362743152003567263464540361 272057364002675447598405271)
      ·
        refine ⟨408086046004013171397607907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272057364002675447598405271 408086046004013171397607907)
        ·
          refine ⟨612129069006019757096411861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408086046004013171397607907 612129069006019757096411861)
          ·
            refine ⟨14346775054828588056947153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 612129069006019757096411861 14346775054828588056947153)
            ·
              refine ⟨10760081291121441042710365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14346775054828588056947153 10760081291121441042710365)
              ·
                refine ⟨4035030484170540391016387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10760081291121441042710365 4035030484170540391016387)
                ·
                  refine ⟨6052545726255810586524581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035030484170540391016387 6052545726255810586524581)
                  ·
                    refine ⟨1134852323672964484973359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052545726255810586524581 1134852323672964484973359)
                    ·
                      rfl

theorem cell23_6630351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 1, 4].length) (baseStart_6630351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630351 prefixEnd_6630351 := by exact prefixLift 6630351
  have htrace : WordTrace (prefixWord ++ tailWord_6630351) baseStart_6630351 baseEnd_6630351 := by
    simpa [prefixWord, tailWord_6630351, baseEnd_6630351] using wordTrace_append hprefix tailTrace_6630351
  have hstable : (prefixWord ++ tailWord_6630351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630351).length < 2 ^ (prefixWord ++ tailWord_6630351).sum := by decide
  have hdescent : baseEnd_6630351 < baseStart_6630351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630402 : List Nat := [3, 4, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_6630402 : Nat := 118140960795 + 6630402 * 2 ^ 59
def prefixEnd_6630402 : Nat := 4983230072969 + 3 ^ 40 * 6630402 * 2
def baseEnd_6630402 : Nat := 1134861052844090918460781

theorem tailTrace_6630402 : CollatzResearch.WordTrace tailWord_6630402 prefixEnd_6630402 1134861052844090918460781 := by
  unfold tailWord_6630402
  simp only [CollatzResearch.WordTrace]
  refine ⟨60457657031298352838283365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161220418750128940902088973 60457657031298352838283365)
  ·
    refine ⟨11335810693368441157178131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60457657031298352838283365 11335810693368441157178131)
    ·
      refine ⟨17003716040052661735767197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11335810693368441157178131 17003716040052661735767197)
      ·
        refine ⟨6376393515019748150912699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17003716040052661735767197 6376393515019748150912699)
        ·
          refine ⟨9564590272529622226369049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376393515019748150912699 9564590272529622226369049)
          ·
            refine ⟨7173442704397216669776787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9564590272529622226369049 7173442704397216669776787)
            ·
              refine ⟨10760164056595825004665181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173442704397216669776787 10760164056595825004665181)
              ·
                refine ⟨4035061521223434376749443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10760164056595825004665181 4035061521223434376749443)
                ·
                  refine ⟨6052592281835151565124165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035061521223434376749443 6052592281835151565124165)
                  ·
                    refine ⟨1134861052844090918460781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052592281835151565124165 1134861052844090918460781)
                    ·
                      rfl

theorem cell23_6630402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_6630402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630402 prefixEnd_6630402 := by exact prefixLift 6630402
  have htrace : WordTrace (prefixWord ++ tailWord_6630402) baseStart_6630402 baseEnd_6630402 := by
    simpa [prefixWord, tailWord_6630402, baseEnd_6630402] using wordTrace_append hprefix tailTrace_6630402
  have hstable : (prefixWord ++ tailWord_6630402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630402).length < 2 ^ (prefixWord ++ tailWord_6630402).sum := by decide
  have hdescent : baseEnd_6630402 < baseStart_6630402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630407 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 3, 6]
def baseStart_6630407 : Nat := 118140960795 + 6630407 * 2 ^ 59
def prefixEnd_6630407 : Nat := 4983230072969 + 3 ^ 40 * 6630407 * 2
def baseEnd_6630407 : Nat := 1134861908645181745273273

theorem tailTrace_6630407 : CollatzResearch.WordTrace tailWord_6630407 prefixEnd_6630407 1134861908645181745273273 := by
  unfold tailWord_6630407
  simp only [CollatzResearch.WordTrace]
  refine ⟨241830810490175297207065475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161220540326783531471376983 241830810490175297207065475)
  ·
    refine ⟨362746215735262945810598213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241830810490175297207065475 362746215735262945810598213)
    ·
      refine ⟨68014915450361802339487165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362746215735262945810598213 68014915450361802339487165)
      ·
        refine ⟨25505593293885675877307687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68014915450361802339487165 25505593293885675877307687)
        ·
          refine ⟨38258389940828513815961531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25505593293885675877307687 38258389940828513815961531)
          ·
            refine ⟨57387584911242770723942297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38258389940828513815961531 57387584911242770723942297)
            ·
              refine ⟨43040688683432078042956723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57387584911242770723942297 43040688683432078042956723)
              ·
                refine ⟨64561033025148117064435085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43040688683432078042956723 64561033025148117064435085)
                ·
                  refine ⟨24210387384430543899163157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64561033025148117064435085 24210387384430543899163157)
                  ·
                    refine ⟨1134861908645181745273273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24210387384430543899163157 1134861908645181745273273)
                    ·
                      rfl

theorem cell23_6630407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_6630407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630407 prefixEnd_6630407 := by exact prefixLift 6630407
  have htrace : WordTrace (prefixWord ++ tailWord_6630407) baseStart_6630407 baseEnd_6630407 := by
    simpa [prefixWord, tailWord_6630407, baseEnd_6630407] using wordTrace_append hprefix tailTrace_6630407
  have hstable : (prefixWord ++ tailWord_6630407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630407).length < 2 ^ (prefixWord ++ tailWord_6630407).sum := by decide
  have hdescent : baseEnd_6630407 < baseStart_6630407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630408 : List Nat := [2, 1, 3, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_6630408 : Nat := 118140960795 + 6630408 * 2 ^ 59
def prefixEnd_6630408 : Nat := 4983230072969 + 3 ^ 40 * 6630408 * 2
def baseEnd_6630408 : Nat := 3404586239416199731907315

theorem tailTrace_6630408 : CollatzResearch.WordTrace tailWord_6630408 prefixEnd_6630408 3404586239416199731907315 := by
  unfold tailWord_6630408
  simp only [CollatzResearch.WordTrace]
  refine ⟨120915423481585837188925939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161220564642114449585234585 120915423481585837188925939)
  ·
    refine ⟨181373135222378755783388909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120915423481585837188925939 181373135222378755783388909)
    ·
      refine ⟨68014925708392033418770841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181373135222378755783388909 68014925708392033418770841)
      ·
        refine ⟨51011194281294025064078131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68014925708392033418770841 51011194281294025064078131)
        ·
          refine ⟨76516791421941037596117197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51011194281294025064078131 76516791421941037596117197)
          ·
            refine ⟨28693796783227889098543949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76516791421941037596117197 28693796783227889098543949)
            ·
              refine ⟨10760173793710458411953981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28693796783227889098543949 10760173793710458411953981)
              ·
                refine ⟨4035065172641421904482743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10760173793710458411953981 4035065172641421904482743)
                ·
                  refine ⟨6052597758962132856724115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035065172641421904482743 6052597758962132856724115)
                  ·
                    refine ⟨9078896638443199285086173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6052597758962132856724115 9078896638443199285086173)
                    ·
                      refine ⟨3404586239416199731907315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9078896638443199285086173 3404586239416199731907315)
                      ·
                        rfl

theorem cell23_6630408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_6630408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630408 prefixEnd_6630408 := by exact prefixLift 6630408
  have htrace : WordTrace (prefixWord ++ tailWord_6630408) baseStart_6630408 baseEnd_6630408 := by
    simpa [prefixWord, tailWord_6630408, baseEnd_6630408] using wordTrace_append hprefix tailTrace_6630408
  have hstable : (prefixWord ++ tailWord_6630408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630408).length < 2 ^ (prefixWord ++ tailWord_6630408).sum := by decide
  have hdescent : baseEnd_6630408 < baseStart_6630408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630424 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 4, 4]
def baseStart_6630424 : Nat := 118140960795 + 6630424 * 2 ^ 59
def prefixEnd_6630424 : Nat := 4983230072969 + 3 ^ 40 * 6630424 * 2
def baseEnd_6630424 : Nat := 1134864818368890556435747

theorem tailTrace_6630424 : CollatzResearch.WordTrace tailWord_6630424 prefixEnd_6630424 1134864818368890556435747 := by
  unfold tailWord_6630424
  simp only [CollatzResearch.WordTrace]
  refine ⟨120915715265556854555217163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161220953687409139406956217 120915715265556854555217163)
  ·
    refine ⟨181373572898335281832825745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120915715265556854555217163 181373572898335281832825745)
    ·
      refine ⟨136030179673751461374619309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181373572898335281832825745 136030179673751461374619309)
      ·
        refine ⟨51011317377656798015482241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136030179673751461374619309 51011317377656798015482241)
        ·
          refine ⟨38258488033242598511611681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51011317377656798015482241 38258488033242598511611681)
          ·
            refine ⟨28693866024931948883708761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38258488033242598511611681 28693866024931948883708761)
            ·
              refine ⟨21520399518698961662781571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28693866024931948883708761 21520399518698961662781571)
              ·
                refine ⟨32280599278048442494172357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21520399518698961662781571 32280599278048442494172357)
                ·
                  refine ⟨6052612364634082967657317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32280599278048442494172357 6052612364634082967657317)
                  ·
                    refine ⟨1134864818368890556435747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052612364634082967657317 1134864818368890556435747)
                    ·
                      rfl

theorem cell23_6630424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_6630424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630424 prefixEnd_6630424 := by exact prefixLift 6630424
  have htrace : WordTrace (prefixWord ++ tailWord_6630424) baseStart_6630424 baseEnd_6630424 := by
    simpa [prefixWord, tailWord_6630424, baseEnd_6630424] using wordTrace_append hprefix tailTrace_6630424
  have hstable : (prefixWord ++ tailWord_6630424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630424).length < 2 ^ (prefixWord ++ tailWord_6630424).sum := by decide
  have hdescent : baseEnd_6630424 < baseStart_6630424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630434 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_6630434 : Nat := 118140960795 + 6630434 * 2 ^ 59
def prefixEnd_6630434 : Nat := 4983230072969 + 3 ^ 40 * 6630434 * 2
def baseEnd_6630434 : Nat := 3404599589913216630182195

theorem tailTrace_6630434 : CollatzResearch.WordTrace tailWord_6630434 prefixEnd_6630434 3404599589913216630182195 := by
  unfold tailWord_6630434
  simp only [CollatzResearch.WordTrace]
  refine ⟨60457948815269370204574589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161221196840718320545532237 60457948815269370204574589)
  ·
    refine ⟨22671730805726013826715471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60457948815269370204574589 22671730805726013826715471)
    ·
      refine ⟨34007596208589020740073207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22671730805726013826715471 34007596208589020740073207)
      ·
        refine ⟨51011394312883531110109811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34007596208589020740073207 51011394312883531110109811)
        ·
          refine ⟨76517091469325296665164717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51011394312883531110109811 76517091469325296665164717)
          ·
            refine ⟨28693909300996986249436769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76517091469325296665164717 28693909300996986249436769)
            ·
              refine ⟨21520431975747739687077577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28693909300996986249436769 21520431975747739687077577)
              ·
                refine ⟨16140323981810804765308183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21520431975747739687077577 16140323981810804765308183)
                ·
                  refine ⟨24210485972716207147962275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16140323981810804765308183 24210485972716207147962275)
                  ·
                    refine ⟨36315728959074310721943413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24210485972716207147962275 36315728959074310721943413)
                    ·
                      refine ⟨3404599589913216630182195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36315728959074310721943413 3404599589913216630182195)
                      ·
                        rfl

theorem cell23_6630434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_6630434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630434 prefixEnd_6630434 := by exact prefixLift 6630434
  have htrace : WordTrace (prefixWord ++ tailWord_6630434) baseStart_6630434 baseEnd_6630434 := by
    simpa [prefixWord, tailWord_6630434, baseEnd_6630434] using wordTrace_append hprefix tailTrace_6630434
  have hstable : (prefixWord ++ tailWord_6630434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630434).length < 2 ^ (prefixWord ++ tailWord_6630434).sum := by decide
  have hdescent : baseEnd_6630434 < baseStart_6630434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630437 : List Nat := [1, 3, 1, 2, 2, 2, 4, 8]
def baseStart_6630437 : Nat := 118140960795 + 6630437 * 2 ^ 59
def prefixEnd_6630437 : Nat := 4983230072969 + 3 ^ 40 * 6630437 * 2
def baseEnd_6630437 : Nat := 126096338161302967349803

theorem tailTrace_6630437 : CollatzResearch.WordTrace tailWord_6630437 prefixEnd_6630437 126096338161302967349803 := by
  unfold tailWord_6630437
  simp only [CollatzResearch.WordTrace]
  refine ⟨241831904680066612330657565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161221269786711074887105043 241831904680066612330657565)
  ·
    refine ⟨90686964255024979623996587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241831904680066612330657565 90686964255024979623996587)
    ·
      refine ⟨136030446382537469435994881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90686964255024979623996587 136030446382537469435994881)
      ·
        refine ⟨102022834786903102076996161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136030446382537469435994881 102022834786903102076996161)
        ·
          refine ⟨76517126090177326557747121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102022834786903102076996161 76517126090177326557747121)
          ·
            refine ⟨57387844567632994918310341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76517126090177326557747121 57387844567632994918310341)
            ·
              refine ⟨10760220856431186547183189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57387844567632994918310341 10760220856431186547183189)
              ·
                refine ⟨126096338161302967349803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10760220856431186547183189 126096338161302967349803)
                ·
                  rfl

theorem cell23_6630437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 8].length) (baseStart_6630437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630437 prefixEnd_6630437 := by exact prefixLift 6630437
  have htrace : WordTrace (prefixWord ++ tailWord_6630437) baseStart_6630437 baseEnd_6630437 := by
    simpa [prefixWord, tailWord_6630437, baseEnd_6630437] using wordTrace_append hprefix tailTrace_6630437
  have hstable : (prefixWord ++ tailWord_6630437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630437).length < 2 ^ (prefixWord ++ tailWord_6630437).sum := by decide
  have hdescent : baseEnd_6630437 < baseStart_6630437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630454 : List Nat := [5, 1, 2, 1, 1, 2, 2, 9]
def baseStart_6630454 : Nat := 118140960795 + 6630454 * 2 ^ 59
def prefixEnd_6630454 : Nat := 4983230072969 + 3 ^ 40 * 6630454 * 2
def baseEnd_6630454 : Nat := 126096661463937279701189

theorem tailTrace_6630454 : CollatzResearch.WordTrace tailWord_6630454 prefixEnd_6630454 126096661463937279701189 := by
  unfold tailWord_6630454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114532795062814014626651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161221683147336682822684277 15114532795062814014626651)
  ·
    refine ⟨22671799192594221021939977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15114532795062814014626651 22671799192594221021939977)
    ·
      refine ⟨17003849394445665766454983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22671799192594221021939977 17003849394445665766454983)
      ·
        refine ⟨25505774091668498649682475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17003849394445665766454983 25505774091668498649682475)
        ·
          refine ⟨38258661137502747974523713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25505774091668498649682475 38258661137502747974523713)
          ·
            refine ⟨28693995853127060980892785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38258661137502747974523713 28693995853127060980892785)
            ·
              refine ⟨21520496889845295735669589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28693995853127060980892785 21520496889845295735669589)
              ·
                refine ⟨126096661463937279701189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21520496889845295735669589 126096661463937279701189)
                ·
                  rfl

theorem cell23_6630454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_6630454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630454 prefixEnd_6630454 := by exact prefixLift 6630454
  have htrace : WordTrace (prefixWord ++ tailWord_6630454) baseStart_6630454 baseEnd_6630454 := by
    simpa [prefixWord, tailWord_6630454, baseEnd_6630454] using wordTrace_append hprefix tailTrace_6630454
  have hstable : (prefixWord ++ tailWord_6630454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630454).length < 2 ^ (prefixWord ++ tailWord_6630454).sum := by decide
  have hdescent : baseEnd_6630454 < baseStart_6630454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630464 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3]
def baseStart_6630464 : Nat := 118140960795 + 6630464 * 2 ^ 59
def prefixEnd_6630464 : Nat := 4983230072969 + 3 ^ 40 * 6630464 * 2
def baseEnd_6630464 : Nat := 3404614994332851512807057

theorem tailTrace_6630464 : CollatzResearch.WordTrace tailWord_6630464 prefixEnd_6630464 3404614994332851512807057 := by
  unfold tailWord_6630464
  simp only [CollatzResearch.WordTrace]
  refine ⟨120916444725484397970945223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161221926300645863961260297 120916444725484397970945223)
  ·
    refine ⟨181374667088226596956417835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120916444725484397970945223 181374667088226596956417835)
    ·
      refine ⟨272062000632339895434626753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181374667088226596956417835 272062000632339895434626753)
      ·
        refine ⟨204046500474254921575970065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272062000632339895434626753 204046500474254921575970065)
        ·
          refine ⟨153034875355691191181977549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204046500474254921575970065 153034875355691191181977549)
          ·
            refine ⟨57388078258384196693241581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153034875355691191181977549 57388078258384196693241581)
            ·
              refine ⟨21520529346894073759965593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57388078258384196693241581 21520529346894073759965593)
              ·
                refine ⟨16140397010170555319974195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21520529346894073759965593 16140397010170555319974195)
                ·
                  refine ⟨24210595515255832979961293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16140397010170555319974195 24210595515255832979961293)
                  ·
                    refine ⟨9078973318220937367485485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24210595515255832979961293 9078973318220937367485485)
                    ·
                      refine ⟨3404614994332851512807057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9078973318220937367485485 3404614994332851512807057)
                      ·
                        rfl

theorem cell23_6630464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_6630464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630464 prefixEnd_6630464 := by exact prefixLift 6630464
  have htrace : WordTrace (prefixWord ++ tailWord_6630464) baseStart_6630464 baseEnd_6630464 := by
    simpa [prefixWord, tailWord_6630464, baseEnd_6630464] using wordTrace_append hprefix tailTrace_6630464
  have hstable : (prefixWord ++ tailWord_6630464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630464).length < 2 ^ (prefixWord ++ tailWord_6630464).sum := by decide
  have hdescent : baseEnd_6630464 < baseStart_6630464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630481 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_6630481 : Nat := 118140960795 + 6630481 * 2 ^ 59
def prefixEnd_6630481 : Nat := 4983230072969 + 3 ^ 40 * 6630481 * 2
def baseEnd_6630481 : Nat := 3404623723503977946294479

theorem tailTrace_6630481 : CollatzResearch.WordTrace tailWord_6630481 prefixEnd_6630481 3404623723503977946294479 := by
  unfold tailWord_6630481
  simp only [CollatzResearch.WordTrace]
  refine ⟨241833509491907207845259297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161222339661271471896839531 241833509491907207845259297)
  ·
    refine ⟨181375132118930405883944473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241833509491907207845259297 181375132118930405883944473)
    ·
      refine ⟨136031349089197804412958355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181375132118930405883944473 136031349089197804412958355)
      ·
        refine ⟨204047023633796706619437533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136031349089197804412958355 204047023633796706619437533)
        ·
          refine ⟨76517633862673764982289075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204047023633796706619437533 76517633862673764982289075)
          ·
            refine ⟨114776450794010647473433613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76517633862673764982289075 114776450794010647473433613)
            ·
              refine ⟨43041169047753992802537605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114776450794010647473433613 43041169047753992802537605)
              ·
                refine ⟨8070219196453873650475801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43041169047753992802537605 8070219196453873650475801)
                ·
                  refine ⟨6052664397340405237856851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8070219196453873650475801 6052664397340405237856851)
                  ·
                    refine ⟨9078996596010607856785277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6052664397340405237856851 9078996596010607856785277)
                    ·
                      refine ⟨3404623723503977946294479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9078996596010607856785277 3404623723503977946294479)
                      ·
                        rfl

theorem cell23_6630481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_6630481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630481 prefixEnd_6630481 := by exact prefixLift 6630481
  have htrace : WordTrace (prefixWord ++ tailWord_6630481) baseStart_6630481 baseEnd_6630481 := by
    simpa [prefixWord, tailWord_6630481, baseEnd_6630481] using wordTrace_append hprefix tailTrace_6630481
  have hstable : (prefixWord ++ tailWord_6630481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630481).length < 2 ^ (prefixWord ++ tailWord_6630481).sum := by decide
  have hdescent : baseEnd_6630481 < baseStart_6630481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630482 : List Nat := [3, 2, 2, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_6630482 : Nat := 118140960795 + 6630482 * 2 ^ 59
def prefixEnd_6630482 : Nat := 4983230072969 + 3 ^ 40 * 6630482 * 2
def baseEnd_6630482 : Nat := 3404624236984632442381975

theorem tailTrace_6630482 : CollatzResearch.WordTrace tailWord_6630482 prefixEnd_6630482 3404624236984632442381975 := by
  unfold tailWord_6630482
  simp only [CollatzResearch.WordTrace]
  refine ⟨60458386491225896254011425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161222363976602390010697133 60458386491225896254011425)
  ·
    refine ⟨45343789868419422190508569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60458386491225896254011425 45343789868419422190508569)
    ·
      refine ⟨34007842401314566642881427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45343789868419422190508569 34007842401314566642881427)
      ·
        refine ⟨51011763601971849964322141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34007842401314566642881427 51011763601971849964322141)
        ·
          refine ⟨19129411350739443736620803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51011763601971849964322141 19129411350739443736620803)
          ·
            refine ⟨28694117026109165604931205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19129411350739443736620803 28694117026109165604931205)
            ·
              refine ⟨5380146942395468550924601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28694117026109165604931205 5380146942395468550924601)
              ·
                refine ⟨4035110206796601413193451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380146942395468550924601 4035110206796601413193451)
                ·
                  refine ⟨6052665310194902119790177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035110206796601413193451 6052665310194902119790177)
                  ·
                    refine ⟨4539498982646176589842633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6052665310194902119790177 4539498982646176589842633)
                    ·
                      refine ⟨3404624236984632442381975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539498982646176589842633 3404624236984632442381975)
                      ·
                        rfl

theorem cell23_6630482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_6630482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630482 prefixEnd_6630482 := by exact prefixLift 6630482
  have htrace : WordTrace (prefixWord ++ tailWord_6630482) baseStart_6630482 baseEnd_6630482 := by
    simpa [prefixWord, tailWord_6630482, baseEnd_6630482] using wordTrace_append hprefix tailTrace_6630482
  have hstable : (prefixWord ++ tailWord_6630482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630482).length < 2 ^ (prefixWord ++ tailWord_6630482).sum := by decide
  have hdescent : baseEnd_6630482 < baseStart_6630482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630497 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 1, 8]
def baseStart_6630497 : Nat := 118140960795 + 6630497 * 2 ^ 59
def prefixEnd_6630497 : Nat := 4983230072969 + 3 ^ 40 * 6630497 * 2
def baseEnd_6630497 : Nat := 1134877313064816627898135

theorem tailTrace_6630497 : CollatzResearch.WordTrace tailWord_6630497 prefixEnd_6630497 1134877313064816627898135 := by
  unfold tailWord_6630497
  simp only [CollatzResearch.WordTrace]
  refine ⟨241834093059849242577841745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161222728706566161718561163 241834093059849242577841745)
  ·
    refine ⟨181375569794886931933381309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241834093059849242577841745 181375569794886931933381309)
    ·
      refine ⟨68015838673082599475017991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181375569794886931933381309 68015838673082599475017991)
      ·
        refine ⟨102023758009623899212526987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68015838673082599475017991 102023758009623899212526987)
        ·
          refine ⟨153035637014435848818790481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102023758009623899212526987 153035637014435848818790481)
          ·
            refine ⟨114776727760826886614092861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153035637014435848818790481 114776727760826886614092861)
            ·
              refine ⟨43041272910310082480284823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114776727760826886614092861 43041272910310082480284823)
              ·
                refine ⟨64561909365465123720427235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43041272910310082480284823 64561909365465123720427235)
                ·
                  refine ⟨96842864048197685580640853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64561909365465123720427235 96842864048197685580640853)
                  ·
                    refine ⟨1134877313064816627898135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96842864048197685580640853 1134877313064816627898135)
                    ·
                      rfl

theorem cell23_6630497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_6630497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630497 prefixEnd_6630497 := by exact prefixLift 6630497
  have htrace : WordTrace (prefixWord ++ tailWord_6630497) baseStart_6630497 baseEnd_6630497 := by
    simpa [prefixWord, tailWord_6630497, baseEnd_6630497] using wordTrace_append hprefix tailTrace_6630497
  have hstable : (prefixWord ++ tailWord_6630497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630497).length < 2 ^ (prefixWord ++ tailWord_6630497).sum := by decide
  have hdescent : baseEnd_6630497 < baseStart_6630497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630498 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6630498 : Nat := 118140960795 + 6630498 * 2 ^ 59
def prefixEnd_6630498 : Nat := 4983230072969 + 3 ^ 40 * 6630498 * 2
def baseEnd_6630498 : Nat := 3404632452675104379781901

theorem tailTrace_6630498 : CollatzResearch.WordTrace tailWord_6630498 prefixEnd_6630498 3404632452675104379781901 := by
  unfold tailWord_6630498
  simp only [CollatzResearch.WordTrace]
  refine ⟨60458532383211404937157037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161222753021897079832418765 60458532383211404937157037)
  ·
    refine ⟨22671949643704276851433889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60458532383211404937157037 22671949643704276851433889)
    ·
      refine ⟨17003962232778207638575417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22671949643704276851433889 17003962232778207638575417)
      ·
        refine ⟨12752971674583655728931563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17003962232778207638575417 12752971674583655728931563)
        ·
          refine ⟨19129457511875483593397345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12752971674583655728931563 19129457511875483593397345)
          ·
            refine ⟨14347093133906612695048009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19129457511875483593397345 14347093133906612695048009)
            ·
              refine ⟨10760319850429959521286007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14347093133906612695048009 10760319850429959521286007)
              ·
                refine ⟨16140479775644939281929011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10760319850429959521286007 16140479775644939281929011)
                ·
                  refine ⟨24210719663467408922893517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16140479775644939281929011 24210719663467408922893517)
                  ·
                    refine ⟨9079019873800278346085069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24210719663467408922893517 9079019873800278346085069)
                    ·
                      refine ⟨3404632452675104379781901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9079019873800278346085069 3404632452675104379781901)
                      ·
                        rfl

theorem cell23_6630498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6630498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630498 prefixEnd_6630498 := by exact prefixLift 6630498
  have htrace : WordTrace (prefixWord ++ tailWord_6630498) baseStart_6630498 baseEnd_6630498 := by
    simpa [prefixWord, tailWord_6630498, baseEnd_6630498] using wordTrace_append hprefix tailTrace_6630498
  have hstable : (prefixWord ++ tailWord_6630498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630498).length < 2 ^ (prefixWord ++ tailWord_6630498).sum := by decide
  have hdescent : baseEnd_6630498 < baseStart_6630498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630538 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_6630538 : Nat := 118140960795 + 6630538 * 2 ^ 59
def prefixEnd_6630538 : Nat := 4983230072969 + 3 ^ 40 * 6630538 * 2
def baseEnd_6630538 : Nat := 3404652991901284223281717

theorem tailTrace_6630538 : CollatzResearch.WordTrace tailWord_6630538 prefixEnd_6630538 3404652991901284223281717 := by
  unfold tailWord_6630538
  simp only [CollatzResearch.WordTrace]
  refine ⟨60458897113175176645021067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161223725635133804386722845 60458897113175176645021067)
  ·
    refine ⟨90688345669762764967531601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60458897113175176645021067 90688345669762764967531601)
    ·
      refine ⟨68016259252322073725648701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90688345669762764967531601 68016259252322073725648701)
      ·
        refine ⟨25506097219620777647118263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68016259252322073725648701 25506097219620777647118263)
        ·
          refine ⟨38259145829431166470677395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25506097219620777647118263 38259145829431166470677395)
          ·
            refine ⟨57388718744146749706016093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38259145829431166470677395 57388718744146749706016093)
            ·
              refine ⟨21520769529055031139756035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57388718744146749706016093 21520769529055031139756035)
              ·
                refine ⟨32281154293582546709634053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21520769529055031139756035 32281154293582546709634053)
                ·
                  refine ⟨6052716430046727508056385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32281154293582546709634053 6052716430046727508056385)
                  ·
                    refine ⟨4539537322535045631042289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6052716430046727508056385 4539537322535045631042289)
                    ·
                      refine ⟨3404652991901284223281717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539537322535045631042289 3404652991901284223281717)
                      ·
                        rfl

theorem cell23_6630538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_6630538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630538 prefixEnd_6630538 := by exact prefixLift 6630538
  have htrace : WordTrace (prefixWord ++ tailWord_6630538) baseStart_6630538 baseEnd_6630538 := by
    simpa [prefixWord, tailWord_6630538, baseEnd_6630538] using wordTrace_append hprefix tailTrace_6630538
  have hstable : (prefixWord ++ tailWord_6630538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630538).length < 2 ^ (prefixWord ++ tailWord_6630538).sum := by decide
  have hdescent : baseEnd_6630538 < baseStart_6630538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630578 : List Nat := [3, 2, 1, 1, 1, 6, 1, 3, 5]
def baseStart_6630578 : Nat := 118140960795 + 6630578 * 2 ^ 59
def prefixEnd_6630578 : Nat := 4983230072969 + 3 ^ 40 * 6630578 * 2
def baseEnd_6630578 : Nat := 378297059014162674086837

theorem tailTrace_6630578 : CollatzResearch.WordTrace tailWord_6630578 prefixEnd_6630578 378297059014162674086837 := by
  unfold tailWord_6630578
  simp only [CollatzResearch.WordTrace]
  refine ⟨60459261843138948352885097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161224698248370528941026925 60459261843138948352885097)
  ·
    refine ⟨45344446382354211264663823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60459261843138948352885097 45344446382354211264663823)
    ·
      refine ⟨68016669573531316896995735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45344446382354211264663823 68016669573531316896995735)
      ·
        refine ⟨102025004360296975345493603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68016669573531316896995735 102025004360296975345493603)
        ·
          refine ⟨153037506540445463018240405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102025004360296975345493603 153037506540445463018240405)
          ·
            refine ⟨7173633119083381078980019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153037506540445463018240405 7173633119083381078980019)
            ·
              refine ⟨10760449678625071618470029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173633119083381078980019 10760449678625071618470029)
              ·
                refine ⟨4035168629484401856926261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10760449678625071618470029 4035168629484401856926261)
                ·
                  refine ⟨378297059014162674086837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4035168629484401856926261 378297059014162674086837)
                  ·
                    rfl

theorem cell23_6630578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_6630578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630578 prefixEnd_6630578 := by exact prefixLift 6630578
  have htrace : WordTrace (prefixWord ++ tailWord_6630578) baseStart_6630578 baseEnd_6630578 := by
    simpa [prefixWord, tailWord_6630578, baseEnd_6630578] using wordTrace_append hprefix tailTrace_6630578
  have hstable : (prefixWord ++ tailWord_6630578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630578).length < 2 ^ (prefixWord ++ tailWord_6630578).sum := by decide
  have hdescent : baseEnd_6630578 < baseStart_6630578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630655 : List Nat := [1, 1, 2, 2, 1, 5, 4, 2, 1, 4]
def baseStart_6630655 : Nat := 118140960795 + 6630655 * 2 ^ 59
def prefixEnd_6630655 : Nat := 4983230072969 + 3 ^ 40 * 6630655 * 2
def baseEnd_6630655 : Nat := 1134904356379286755172893

theorem tailTrace_6630655 : CollatzResearch.WordTrace tailWord_6630655 prefixEnd_6630655 1134904356379286755172893 := by
  unfold tailWord_6630655
  simp only [CollatzResearch.WordTrace]
  refine ⟨241839855793276835562093419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161226570528851223708062279 241839855793276835562093419)
  ·
    refine ⟨362759783689915253343140129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241839855793276835562093419 362759783689915253343140129)
    ·
      refine ⟨272069837767436440007355097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362759783689915253343140129 272069837767436440007355097)
      ·
        refine ⟨204052378325577330005516323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272069837767436440007355097 204052378325577330005516323)
        ·
          refine ⟨306078567488365995008274485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204052378325577330005516323 306078567488365995008274485)
          ·
            refine ⟨28694865702034312032025733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 306078567488365995008274485 28694865702034312032025733)
            ·
              refine ⟨5380287319131433506004825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28694865702034312032025733 5380287319131433506004825)
              ·
                refine ⟨4035215489348575129503619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380287319131433506004825 4035215489348575129503619)
                ·
                  refine ⟨6052823234022862694255429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035215489348575129503619 6052823234022862694255429)
                  ·
                    refine ⟨1134904356379286755172893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052823234022862694255429 1134904356379286755172893)
                    ·
                      rfl

theorem cell23_6630655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 4].length) (baseStart_6630655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630655 prefixEnd_6630655 := by exact prefixLift 6630655
  have htrace : WordTrace (prefixWord ++ tailWord_6630655) baseStart_6630655 baseEnd_6630655 := by
    simpa [prefixWord, tailWord_6630655, baseEnd_6630655] using wordTrace_append hprefix tailTrace_6630655
  have hstable : (prefixWord ++ tailWord_6630655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630655).length < 2 ^ (prefixWord ++ tailWord_6630655).sum := by decide
  have hdescent : baseEnd_6630655 < baseStart_6630655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630741 : List Nat := [1, 3, 2, 2, 3, 2, 1, 9]
def baseStart_6630741 : Nat := 118140960795 + 6630741 * 2 ^ 59
def prefixEnd_6630741 : Nat := 4983230072969 + 3 ^ 40 * 6630741 * 2
def baseEnd_6630741 : Nat := 126102119573116552927529

theorem tailTrace_6630741 : CollatzResearch.WordTrace tailWord_6630741 prefixEnd_6630741 126102119573116552927529 := by
  unfold tailWord_6630741
  simp only [CollatzResearch.WordTrace]
  refine ⟨241842992470965272249724077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161228661647310181499816051 241842992470965272249724077)
  ·
    refine ⟨90691122176611977093646529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241842992470965272249724077 90691122176611977093646529)
    ·
      refine ⟨68018341632458982820234897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90691122176611977093646529 68018341632458982820234897)
      ·
        refine ⟨51013756224344237115176173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68018341632458982820234897 51013756224344237115176173)
        ·
          refine ⟨19130158584129088918191065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51013756224344237115176173 19130158584129088918191065)
          ·
            refine ⟨14347618938096816688643299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19130158584129088918191065 14347618938096816688643299)
            ·
              refine ⟨21521428407145225032964949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347618938096816688643299 21521428407145225032964949)
              ·
                refine ⟨126102119573116552927529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21521428407145225032964949 126102119573116552927529)
                ·
                  rfl

theorem cell23_6630741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 9].length) (baseStart_6630741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630741 prefixEnd_6630741 := by exact prefixLift 6630741
  have htrace : WordTrace (prefixWord ++ tailWord_6630741) baseStart_6630741 baseEnd_6630741 := by
    simpa [prefixWord, tailWord_6630741, baseEnd_6630741] using wordTrace_append hprefix tailTrace_6630741
  have hstable : (prefixWord ++ tailWord_6630741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630741).length < 2 ^ (prefixWord ++ tailWord_6630741).sum := by decide
  have hdescent : baseEnd_6630741 < baseStart_6630741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630751 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 3]
def baseStart_6630751 : Nat := 118140960795 + 6630751 * 2 ^ 59
def prefixEnd_6630751 : Nat := 4983230072969 + 3 ^ 40 * 6630751 * 2
def baseEnd_6630751 : Nat := 3404762363280691889918237

theorem tailTrace_6630751 : CollatzResearch.WordTrace tailWord_6630751 prefixEnd_6630751 3404762363280691889918237 := by
  unfold tailWord_6630751
  simp only [CollatzResearch.WordTrace]
  refine ⟨241843357200929043957588107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161228904800619362638392071 241843357200929043957588107)
  ·
    refine ⟨362765035801393565936382161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241843357200929043957588107 362765035801393565936382161)
    ·
      refine ⟨272073776851045174452286621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362765035801393565936382161 272073776851045174452286621)
      ·
        refine ⟨102027666319141940419607483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272073776851045174452286621 102027666319141940419607483)
        ·
          refine ⟨153041499478712910629411225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102027666319141940419607483 153041499478712910629411225)
          ·
            refine ⟨114781124609034682972058419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153041499478712910629411225 114781124609034682972058419)
            ·
              refine ⟨172171686913552024458087629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114781124609034682972058419 172171686913552024458087629)
              ·
                refine ⟨64564382592582009171782861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172171686913552024458087629 64564382592582009171782861)
                ·
                  refine ⟨24211643472218253439418573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64564382592582009171782861 24211643472218253439418573)
                  ·
                    refine ⟨9079366302081845039781965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24211643472218253439418573 9079366302081845039781965)
                    ·
                      refine ⟨3404762363280691889918237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9079366302081845039781965 3404762363280691889918237)
                      ·
                        rfl

theorem cell23_6630751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_6630751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630751 prefixEnd_6630751 := by exact prefixLift 6630751
  have htrace : WordTrace (prefixWord ++ tailWord_6630751) baseStart_6630751 baseEnd_6630751 := by
    simpa [prefixWord, tailWord_6630751, baseEnd_6630751] using wordTrace_append hprefix tailTrace_6630751
  have hstable : (prefixWord ++ tailWord_6630751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630751).length < 2 ^ (prefixWord ++ tailWord_6630751).sum := by decide
  have hdescent : baseEnd_6630751 < baseStart_6630751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630768 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 4, 1, 3]
def baseStart_6630768 : Nat := 118140960795 + 6630768 * 2 ^ 59
def prefixEnd_6630768 : Nat := 4983230072969 + 3 ^ 40 * 6630768 * 2
def baseEnd_6630768 : Nat := 3404771092451818323405659

theorem tailTrace_6630768 : CollatzResearch.WordTrace tailWord_6630768 prefixEnd_6630768 3404771092451818323405659 := by
  unfold tailWord_6630768
  simp only [CollatzResearch.WordTrace]
  refine ⟨120921988620933727930478479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161229318161244970573971305 120921988620933727930478479)
  ·
    refine ⟨181382982931400591895717719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120921988620933727930478479 181382982931400591895717719)
    ·
      refine ⟨272074474397100887843576579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181382982931400591895717719 272074474397100887843576579)
      ·
        refine ⟨408111711595651331765364869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272074474397100887843576579 408111711595651331765364869)
        ·
          refine ⟨76520945924184624706005913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 408111711595651331765364869 76520945924184624706005913)
          ·
            refine ⟨57390709443138468529504435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76520945924184624706005913 57390709443138468529504435)
            ·
              refine ⟨86086064164707702794256653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57390709443138468529504435 86086064164707702794256653)
              ·
                refine ⟨32282274061765388547846245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86086064164707702794256653 32282274061765388547846245)
                ·
                  refine ⟨6052926386581010352721171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32282274061765388547846245 6052926386581010352721171)
                  ·
                    refine ⟨9079389579871515529081757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6052926386581010352721171 9079389579871515529081757)
                    ·
                      refine ⟨3404771092451818323405659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9079389579871515529081757 3404771092451818323405659)
                      ·
                        rfl

theorem cell23_6630768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 4, 1, 3].length) (baseStart_6630768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630768 prefixEnd_6630768 := by exact prefixLift 6630768
  have htrace : WordTrace (prefixWord ++ tailWord_6630768) baseStart_6630768 baseEnd_6630768 := by
    simpa [prefixWord, tailWord_6630768, baseEnd_6630768] using wordTrace_append hprefix tailTrace_6630768
  have hstable : (prefixWord ++ tailWord_6630768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630768).length < 2 ^ (prefixWord ++ tailWord_6630768).sum := by decide
  have hdescent : baseEnd_6630768 < baseStart_6630768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630778 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2]
def baseStart_6630778 : Nat := 118140960795 + 6630778 * 2 ^ 59
def prefixEnd_6630778 : Nat := 4983230072969 + 3 ^ 40 * 6630778 * 2
def baseEnd_6630778 : Nat := 3404776227258363284280613

theorem tailTrace_6630778 : CollatzResearch.WordTrace tailWord_6630778 prefixEnd_6630778 3404776227258363284280613 := by
  unfold tailWord_6630778
  simp only [CollatzResearch.WordTrace]
  refine ⟨60461085492957806892205247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161229561314554151712547325 60461085492957806892205247)
  ·
    refine ⟨90691628239436710338307871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60461085492957806892205247 90691628239436710338307871)
    ·
      refine ⟨136037442359155065507461807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90691628239436710338307871 136037442359155065507461807)
      ·
        refine ⟨204056163538732598261192711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136037442359155065507461807 204056163538732598261192711)
        ·
          refine ⟨306084245308098897391789067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204056163538732598261192711 306084245308098897391789067)
          ·
            refine ⟨459126367962148346087683601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306084245308098897391789067 459126367962148346087683601)
            ·
              refine ⟨344344775971611259565762701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459126367962148346087683601 344344775971611259565762701)
              ·
                refine ⟨129129290989354222337161013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344344775971611259565762701 129129290989354222337161013)
                ·
                  refine ⟨12105871030251958344108845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129129290989354222337161013 12105871030251958344108845)
                  ·
                    refine ⟨4539701636344484379040817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12105871030251958344108845 4539701636344484379040817)
                    ·
                      refine ⟨3404776227258363284280613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539701636344484379040817 3404776227258363284280613)
                      ·
                        rfl

theorem cell23_6630778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_6630778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630778 prefixEnd_6630778 := by exact prefixLift 6630778
  have htrace : WordTrace (prefixWord ++ tailWord_6630778) baseStart_6630778 baseEnd_6630778 := by
    simpa [prefixWord, tailWord_6630778, baseEnd_6630778] using wordTrace_append hprefix tailTrace_6630778
  have hstable : (prefixWord ++ tailWord_6630778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630778).length < 2 ^ (prefixWord ++ tailWord_6630778).sum := by decide
  have hdescent : baseEnd_6630778 < baseStart_6630778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630802 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6630802 : Nat := 118140960795 + 6630802 * 2 ^ 59
def prefixEnd_6630802 : Nat := 4983230072969 + 3 ^ 40 * 6630802 * 2
def baseEnd_6630802 : Nat := 3404788550794071190380503

theorem tailTrace_6630802 : CollatzResearch.WordTrace tailWord_6630802 prefixEnd_6630802 3404788550794071190380503 := by
  unfold tailWord_6630802
  simp only [CollatzResearch.WordTrace]
  refine ⟨60461304330936069916923665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161230144882496186445129773 60461304330936069916923665)
  ·
    refine ⟨45345978248202052437692749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60461304330936069916923665 45345978248202052437692749)
    ·
      refine ⟨17004741843075769664134781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45345978248202052437692749 17004741843075769664134781)
      ·
        refine ⟨6376778191153413624050543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17004741843075769664134781 6376778191153413624050543)
        ·
          refine ⟨9565167286730120436075815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376778191153413624050543 9565167286730120436075815)
          ·
            refine ⟨14347750930095180654113723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9565167286730120436075815 14347750930095180654113723)
            ·
              refine ⟨21521626395142770981170585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347750930095180654113723 21521626395142770981170585)
              ·
                refine ⟨16141219796357078235877939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21521626395142770981170585 16141219796357078235877939)
                ·
                  refine ⟨24211829694535617353816909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16141219796357078235877939 24211829694535617353816909)
                  ·
                    refine ⟨9079436135450856507681341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24211829694535617353816909 9079436135450856507681341)
                    ·
                      refine ⟨3404788550794071190380503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9079436135450856507681341 3404788550794071190380503)
                      ·
                        rfl

theorem cell23_6630802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6630802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630802 prefixEnd_6630802 := by exact prefixLift 6630802
  have htrace : WordTrace (prefixWord ++ tailWord_6630802) baseStart_6630802 baseEnd_6630802 := by
    simpa [prefixWord, tailWord_6630802, baseEnd_6630802] using wordTrace_append hprefix tailTrace_6630802
  have hstable : (prefixWord ++ tailWord_6630802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630802).length < 2 ^ (prefixWord ++ tailWord_6630802).sum := by decide
  have hdescent : baseEnd_6630802 < baseStart_6630802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630871 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_6630871 : Nat := 118140960795 + 6630871 * 2 ^ 59
def prefixEnd_6630871 : Nat := 4983230072969 + 3 ^ 40 * 6630871 * 2
def baseEnd_6630871 : Nat := 3404823980959231420417685

theorem tailTrace_6630871 : CollatzResearch.WordTrace tailWord_6630871 prefixEnd_6630871 3404823980959231420417685 := by
  unfold tailWord_6630871
  simp only [CollatzResearch.WordTrace]
  refine ⟨241847733960494304451956467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161231822640329536301304311 241847733960494304451956467)
  ·
    refine ⟨362771600940741456677934701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241847733960494304451956467 362771600940741456677934701)
    ·
      refine ⟨136039350352778046254225513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362771600940741456677934701 136039350352778046254225513)
      ·
        refine ⟨102029512764583534690669135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136039350352778046254225513 102029512764583534690669135)
        ·
          refine ⟨153044269146875302036003703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102029512764583534690669135 153044269146875302036003703)
          ·
            refine ⟨229566403720312953054005555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153044269146875302036003703 229566403720312953054005555)
            ·
              refine ⟨344349605580469429581008333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229566403720312953054005555 344349605580469429581008333)
              ·
                refine ⟨129131102092676036092878125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344349605580469429581008333 129131102092676036092878125)
                ·
                  refine ⟨48424163284753513534829297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129131102092676036092878125 48424163284753513534829297)
                  ·
                    refine ⟨36318122463565135151121973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48424163284753513534829297 36318122463565135151121973)
                    ·
                      refine ⟨3404823980959231420417685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36318122463565135151121973 3404823980959231420417685)
                      ·
                        rfl

theorem cell23_6630871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_6630871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630871 prefixEnd_6630871 := by exact prefixLift 6630871
  have htrace : WordTrace (prefixWord ++ tailWord_6630871) baseStart_6630871 baseEnd_6630871 := by
    simpa [prefixWord, tailWord_6630871, baseEnd_6630871] using wordTrace_append hprefix tailTrace_6630871
  have hstable : (prefixWord ++ tailWord_6630871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630871).length < 2 ^ (prefixWord ++ tailWord_6630871).sum := by decide
  have hdescent : baseEnd_6630871 < baseStart_6630871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630911 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_6630911 : Nat := 118140960795 + 6630911 * 2 ^ 59
def prefixEnd_6630911 : Nat := 4983230072969 + 3 ^ 40 * 6630911 * 2
def baseEnd_6630911 : Nat := 3404844520185411263917501

theorem tailTrace_6630911 : CollatzResearch.WordTrace tailWord_6630911 prefixEnd_6630911 3404844520185411263917501 := by
  unfold tailWord_6630911
  simp only [CollatzResearch.WordTrace]
  refine ⟨241849192880349391283412587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161232795253566260855608391 241849192880349391283412587)
  ·
    refine ⟨362773789320524086925118881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241849192880349391283412587 362773789320524086925118881)
    ·
      refine ⟨272080341990393065193839161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362773789320524086925118881 272080341990393065193839161)
      ·
        refine ⟨204060256492794798895379371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272080341990393065193839161 204060256492794798895379371)
        ·
          refine ⟨306090384739192198343069057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204060256492794798895379371 306090384739192198343069057)
          ·
            refine ⟨229567788554394148757301793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306090384739192198343069057 229567788554394148757301793)
            ·
              refine ⟨172175841415795611567976345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229567788554394148757301793 172175841415795611567976345)
              ·
                refine ⟨129131881061846708675982259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172175841415795611567976345 129131881061846708675982259)
                ·
                  refine ⟨193697821592770063013973389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129131881061846708675982259 193697821592770063013973389)
                  ·
                    refine ⟨72636683097288773630240021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193697821592770063013973389 72636683097288773630240021)
                    ·
                      refine ⟨3404844520185411263917501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72636683097288773630240021 3404844520185411263917501)
                      ·
                        rfl

theorem cell23_6630911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_6630911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630911 prefixEnd_6630911 := by exact prefixLift 6630911
  have htrace : WordTrace (prefixWord ++ tailWord_6630911) baseStart_6630911 baseEnd_6630911 := by
    simpa [prefixWord, tailWord_6630911, baseEnd_6630911] using wordTrace_append hprefix tailTrace_6630911
  have hstable : (prefixWord ++ tailWord_6630911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630911).length < 2 ^ (prefixWord ++ tailWord_6630911).sum := by decide
  have hdescent : baseEnd_6630911 < baseStart_6630911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630921 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 10]
def baseStart_6630921 : Nat := 118140960795 + 6630921 * 2 ^ 59
def prefixEnd_6630921 : Nat := 4983230072969 + 3 ^ 40 * 6630921 * 2
def baseEnd_6630921 : Nat := 378316628332439580532495

theorem tailTrace_6630921 : CollatzResearch.WordTrace tailWord_6630921 prefixEnd_6630921 378316628332439580532495 := by
  unfold tailWord_6630921
  simp only [CollatzResearch.WordTrace]
  refine ⟨241849557610313162991276617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161233038406875441994184411 241849557610313162991276617)
  ·
    refine ⟨181387168207734872243457463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241849557610313162991276617 181387168207734872243457463)
    ·
      refine ⟨272080752311602308365186195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181387168207734872243457463 272080752311602308365186195)
      ·
        refine ⟨408121128467403462547779293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272080752311602308365186195 408121128467403462547779293)
        ·
          refine ⟨153045423175276298455417235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408121128467403462547779293 153045423175276298455417235)
          ·
            refine ⟨229568134762914447683125853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153045423175276298455417235 229568134762914447683125853)
            ·
              refine ⟨86088050536092917881172195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229568134762914447683125853 86088050536092917881172195)
              ·
                refine ⟨129132075804139376821758293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86088050536092917881172195 129132075804139376821758293)
                ·
                  refine ⟨378316628332439580532495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 129132075804139376821758293 378316628332439580532495)
                  ·
                    rfl

theorem cell23_6630921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_6630921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630921 prefixEnd_6630921 := by exact prefixLift 6630921
  have htrace : WordTrace (prefixWord ++ tailWord_6630921) baseStart_6630921 baseEnd_6630921 := by
    simpa [prefixWord, tailWord_6630921, baseEnd_6630921] using wordTrace_append hprefix tailTrace_6630921
  have hstable : (prefixWord ++ tailWord_6630921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630921).length < 2 ^ (prefixWord ++ tailWord_6630921).sum := by decide
  have hdescent : baseEnd_6630921 < baseStart_6630921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630938 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 6]
def baseStart_6630938 : Nat := 118140960795 + 6630938 * 2 ^ 59
def prefixEnd_6630938 : Nat := 4983230072969 + 3 ^ 40 * 6630938 * 2
def baseEnd_6630938 : Nat := 378317598240342517586653

theorem tailTrace_6630938 : CollatzResearch.WordTrace tailWord_6630938 prefixEnd_6630938 378317598240342517586653 := by
  unfold tailWord_6630938
  simp only [CollatzResearch.WordTrace]
  refine ⟨60462544412812893723661367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161233451767501049929763645 60462544412812893723661367)
  ·
    refine ⟨90693816619219340585492051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60462544412812893723661367 90693816619219340585492051)
    ·
      refine ⟨136040724928829010878238077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90693816619219340585492051 136040724928829010878238077)
      ·
        refine ⟨51015271848310879079339279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136040724928829010878238077 51015271848310879079339279)
        ·
          refine ⟨76522907772466318619008919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51015271848310879079339279 76522907772466318619008919)
          ·
            refine ⟨114784361658699477928513379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76522907772466318619008919 114784361658699477928513379)
            ·
              refine ⟨172176542488049216892770069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114784361658699477928513379 172176542488049216892770069)
              ·
                refine ⟨8070775429127307041848597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172176542488049216892770069 8070775429127307041848597)
                ·
                  refine ⟨378317598240342517586653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8070775429127307041848597 378317598240342517586653)
                  ·
                    rfl

theorem cell23_6630938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_6630938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630938 prefixEnd_6630938 := by exact prefixLift 6630938
  have htrace : WordTrace (prefixWord ++ tailWord_6630938) baseStart_6630938 baseEnd_6630938 := by
    simpa [prefixWord, tailWord_6630938, baseEnd_6630938] using wordTrace_append hprefix tailTrace_6630938
  have hstable : (prefixWord ++ tailWord_6630938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630938).length < 2 ^ (prefixWord ++ tailWord_6630938).sum := by decide
  have hdescent : baseEnd_6630938 < baseStart_6630938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6630999 : List Nat := [1, 1, 3, 2, 2, 4, 1, 4, 1, 1, 3]
def baseStart_6630999 : Nat := 118140960795 + 6630999 * 2 ^ 59
def prefixEnd_6630999 : Nat := 4983230072969 + 3 ^ 40 * 6630999 * 2
def baseEnd_6630999 : Nat := 3404889706483006919617097

theorem tailTrace_6630999 : CollatzResearch.WordTrace tailWord_6630999 prefixEnd_6630999 3404889706483006919617097 := by
  unfold tailWord_6630999
  simp only [CollatzResearch.WordTrace]
  refine ⟨241852402504030582312616051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161234935002687054875077367 241852402504030582312616051)
  ·
    refine ⟨362778603756045873468924077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241852402504030582312616051 362778603756045873468924077)
    ·
      refine ⟨136041976408517202550846529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362778603756045873468924077 136041976408517202550846529)
      ·
        refine ⟨102031482306387901913134897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136041976408517202550846529 102031482306387901913134897)
        ·
          refine ⟨76523611729790926434851173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102031482306387901913134897 76523611729790926434851173)
          ·
            refine ⟨14348177199335798706534595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76523611729790926434851173 14348177199335798706534595)
            ·
              refine ⟨21522265799003698059801893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14348177199335798706534595 21522265799003698059801893)
              ·
                refine ⟨4035424837313193386212855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21522265799003698059801893 4035424837313193386212855)
                ·
                  refine ⟨6053137255969790079319283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035424837313193386212855 6053137255969790079319283)
                  ·
                    refine ⟨9079705883954685118978925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6053137255969790079319283 9079705883954685118978925)
                    ·
                      refine ⟨3404889706483006919617097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9079705883954685118978925 3404889706483006919617097)
                      ·
                        rfl

theorem cell23_6630999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_6630999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6630999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6630999 prefixEnd_6630999 := by exact prefixLift 6630999
  have htrace : WordTrace (prefixWord ++ tailWord_6630999) baseStart_6630999 baseEnd_6630999 := by
    simpa [prefixWord, tailWord_6630999, baseEnd_6630999] using wordTrace_append hprefix tailTrace_6630999
  have hstable : (prefixWord ++ tailWord_6630999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6630999).length < 2 ^ (prefixWord ++ tailWord_6630999).sum := by decide
  have hdescent : baseEnd_6630999 < baseStart_6630999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6630999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631008 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_6631008 : Nat := 118140960795 + 6631008 * 2 ^ 59
def prefixEnd_6631008 : Nat := 4983230072969 + 3 ^ 40 * 6631008 * 2
def baseEnd_6631008 : Nat := 3404894327808897384404555

theorem tailTrace_6631008 : CollatzResearch.WordTrace tailWord_6631008 prefixEnd_6631008 3404894327808897384404555 := by
  unfold tailWord_6631008
  simp only [CollatzResearch.WordTrace]
  refine ⟨120926365380498988424846839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161235153840665317899795785 120926365380498988424846839)
  ·
    refine ⟨181389548070748482637270259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120926365380498988424846839 181389548070748482637270259)
    ·
      refine ⟨272084322106122723955905389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181389548070748482637270259 272084322106122723955905389)
      ·
        refine ⟨102031620789796021483464521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272084322106122723955905389 102031620789796021483464521)
        ·
          refine ⟨76523715592347016112598391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102031620789796021483464521 76523715592347016112598391)
          ·
            refine ⟨114785573388520524168897587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76523715592347016112598391 114785573388520524168897587)
            ·
              refine ⟨172178360082780786253346381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114785573388520524168897587 172178360082780786253346381)
              ·
                refine ⟨64566885031042794845004893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172178360082780786253346381 64566885031042794845004893)
                ·
                  refine ⟨24212581886641048066876835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64566885031042794845004893 24212581886641048066876835)
                  ·
                    refine ⟨36318872829961572100315253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24212581886641048066876835 36318872829961572100315253)
                    ·
                      refine ⟨3404894327808897384404555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36318872829961572100315253 3404894327808897384404555)
                      ·
                        rfl

theorem cell23_6631008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_6631008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631008 prefixEnd_6631008 := by exact prefixLift 6631008
  have htrace : WordTrace (prefixWord ++ tailWord_6631008) baseStart_6631008 baseEnd_6631008 := by
    simpa [prefixWord, tailWord_6631008, baseEnd_6631008] using wordTrace_append hprefix tailTrace_6631008
  have hstable : (prefixWord ++ tailWord_6631008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631008).length < 2 ^ (prefixWord ++ tailWord_6631008).sum := by decide
  have hdescent : baseEnd_6631008 < baseStart_6631008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631065 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 2, 7, 2]
def baseStart_6631065 : Nat := 118140960795 + 6631065 * 2 ^ 59
def prefixEnd_6631065 : Nat := 4983230072969 + 3 ^ 40 * 6631065 * 2
def baseEnd_6631065 : Nat := 3404923596206203661391793

theorem tailTrace_6631065 : CollatzResearch.WordTrace tailWord_6631065 prefixEnd_6631065 3404923596206203661391793 := by
  unfold tailWord_6631065
  simp only [CollatzResearch.WordTrace]
  refine ⟨241854809721791475584518649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161236539814527650389679099 241854809721791475584518649)
  ·
    refine ⟨181391107291343606688388987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241854809721791475584518649 181391107291343606688388987)
    ·
      refine ⟨272086660937015410032583481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181391107291343606688388987 272086660937015410032583481)
      ·
        refine ⟨204064995702761557524437611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272086660937015410032583481 204064995702761557524437611)
        ·
          refine ⟨306097493554142336286656417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204064995702761557524437611 306097493554142336286656417)
          ·
            refine ⟨229573120165606752214992313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306097493554142336286656417 229573120165606752214992313)
            ·
              refine ⟨172179840124205064161244235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229573120165606752214992313 172179840124205064161244235)
              ·
                refine ⟨258269760186307596241866353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172179840124205064161244235 258269760186307596241866353)
                ·
                  refine ⟨193702320139730697181399765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258269760186307596241866353 193702320139730697181399765)
                  ·
                    refine ⟨4539898128274938215189057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 193702320139730697181399765 4539898128274938215189057)
                    ·
                      refine ⟨3404923596206203661391793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4539898128274938215189057 3404923596206203661391793)
                      ·
                        rfl

theorem cell23_6631065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_6631065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631065 prefixEnd_6631065 := by exact prefixLift 6631065
  have htrace : WordTrace (prefixWord ++ tailWord_6631065) baseStart_6631065 baseEnd_6631065 := by
    simpa [prefixWord, tailWord_6631065, baseEnd_6631065] using wordTrace_append hprefix tailTrace_6631065
  have hstable : (prefixWord ++ tailWord_6631065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631065).length < 2 ^ (prefixWord ++ tailWord_6631065).sum := by decide
  have hdescent : baseEnd_6631065 < baseStart_6631065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631072 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3]
def baseStart_6631072 : Nat := 118140960795 + 6631072 * 2 ^ 59
def prefixEnd_6631072 : Nat := 4983230072969 + 3 ^ 40 * 6631072 * 2
def baseEnd_6631072 : Nat := 3404927190570785134004261

theorem tailTrace_6631072 : CollatzResearch.WordTrace tailWord_6631072 prefixEnd_6631072 3404927190570785134004261 := by
  unfold tailWord_6631072
  simp only [CollatzResearch.WordTrace]
  refine ⟨120927532516383057890011735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161236710021844077186682313 120927532516383057890011735)
  ·
    refine ⟨181391298774574586835017603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120927532516383057890011735 181391298774574586835017603)
    ·
      refine ⟨272086948161861880252526405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181391298774574586835017603 272086948161861880252526405)
      ·
        refine ⟨51016302780349102547348701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272086948161861880252526405 51016302780349102547348701)
        ·
          refine ⟨19131113542630913455255763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51016302780349102547348701 19131113542630913455255763)
          ·
            refine ⟨28696670313946370182883645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19131113542630913455255763 28696670313946370182883645)
            ·
              refine ⟨10761251367729888818581367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28696670313946370182883645 10761251367729888818581367)
              ·
                refine ⟨16141877051594833227872051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10761251367729888818581367 16141877051594833227872051)
                ·
                  refine ⟨24212815577392249841808077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16141877051594833227872051 24212815577392249841808077)
                  ·
                    refine ⟨9079805841522093690678029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24212815577392249841808077 9079805841522093690678029)
                    ·
                      refine ⟨3404927190570785134004261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9079805841522093690678029 3404927190570785134004261)
                      ·
                        rfl

theorem cell23_6631072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_6631072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631072 prefixEnd_6631072 := by exact prefixLift 6631072
  have htrace : WordTrace (prefixWord ++ tailWord_6631072) baseStart_6631072 baseEnd_6631072 := by
    simpa [prefixWord, tailWord_6631072, baseEnd_6631072] using wordTrace_append hprefix tailTrace_6631072
  have hstable : (prefixWord ++ tailWord_6631072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631072).length < 2 ^ (prefixWord ++ tailWord_6631072).sum := by decide
  have hdescent : baseEnd_6631072 < baseStart_6631072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631085 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_6631085 : Nat := 118140960795 + 6631085 * 2 ^ 59
def prefixEnd_6631085 : Nat := 4983230072969 + 3 ^ 40 * 6631085 * 2
def baseEnd_6631085 : Nat := 3404933865819293583141701

theorem tailTrace_6631085 : CollatzResearch.WordTrace tailWord_6631085 prefixEnd_6631085 3404933865819293583141701 := by
  unfold tailWord_6631085
  simp only [CollatzResearch.WordTrace]
  refine ⟨241855539181719019000246709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161237026121146012666831139 241855539181719019000246709)
  ·
    refine ⟨22673956798286158031273129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241855539181719019000246709 22673956798286158031273129)
    ·
      refine ⟨17005467598714618523454847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22673956798286158031273129 17005467598714618523454847)
      ·
        refine ⟨25508201398071927785182271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17005467598714618523454847 25508201398071927785182271)
        ·
          refine ⟨38262302097107891677773407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25508201398071927785182271 38262302097107891677773407)
          ·
            refine ⟨57393453145661837516660111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38262302097107891677773407 57393453145661837516660111)
            ·
              refine ⟨86090179718492756274990167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57393453145661837516660111 86090179718492756274990167)
              ·
                refine ⟨129135269577739134412485251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86090179718492756274990167 129135269577739134412485251)
                ·
                  refine ⟨193702904366608701618727877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129135269577739134412485251 193702904366608701618727877)
                  ·
                    refine ⟨36319294568739131553511477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193702904366608701618727877 36319294568739131553511477)
                    ·
                      refine ⟨3404933865819293583141701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36319294568739131553511477 3404933865819293583141701)
                      ·
                        rfl

theorem cell23_6631085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_6631085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631085 prefixEnd_6631085 := by exact prefixLift 6631085
  have htrace : WordTrace (prefixWord ++ tailWord_6631085) baseStart_6631085 baseEnd_6631085 := by
    simpa [prefixWord, tailWord_6631085, baseEnd_6631085] using wordTrace_append hprefix tailTrace_6631085
  have hstable : (prefixWord ++ tailWord_6631085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631085).length < 2 ^ (prefixWord ++ tailWord_6631085).sum := by decide
  have hdescent : baseEnd_6631085 < baseStart_6631085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631088 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 1, 8]
def baseStart_6631088 : Nat := 118140960795 + 6631088 * 2 ^ 59
def prefixEnd_6631088 : Nat := 4983230072969 + 3 ^ 40 * 6631088 * 2
def baseEnd_6631088 : Nat := 1134978468753752357134729

theorem tailTrace_6631088 : CollatzResearch.WordTrace tailWord_6631088 prefixEnd_6631088 1134978468753752357134729 := by
  unfold tailWord_6631088
  simp only [CollatzResearch.WordTrace]
  refine ⟨120927824300354075256302959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161237099067138767008403945 120927824300354075256302959)
  ·
    refine ⟨181391736450531112884454439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120927824300354075256302959 181391736450531112884454439)
    ·
      refine ⟨272087604675796669326681659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181391736450531112884454439 272087604675796669326681659)
      ·
        refine ⟨408131407013695003990022489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272087604675796669326681659 408131407013695003990022489)
        ·
          refine ⟨306098555260271252992516867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408131407013695003990022489 306098555260271252992516867)
          ·
            refine ⟨459147832890406879488775301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306098555260271252992516867 459147832890406879488775301)
            ·
              refine ⟨86090218666951289904145369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 459147832890406879488775301 86090218666951289904145369)
              ·
                refine ⟨64567664000213467428109027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86090218666951289904145369 64567664000213467428109027)
                ·
                  refine ⟨96851496000320201142163541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64567664000213467428109027 96851496000320201142163541)
                  ·
                    refine ⟨1134978468753752357134729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96851496000320201142163541 1134978468753752357134729)
                    ·
                      rfl

theorem cell23_6631088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_6631088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631088 prefixEnd_6631088 := by exact prefixLift 6631088
  have htrace : WordTrace (prefixWord ++ tailWord_6631088) baseStart_6631088 baseEnd_6631088 := by
    simpa [prefixWord, tailWord_6631088, baseEnd_6631088] using wordTrace_append hprefix tailTrace_6631088
  have hstable : (prefixWord ++ tailWord_6631088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631088).length < 2 ^ (prefixWord ++ tailWord_6631088).sum := by decide
  have hdescent : baseEnd_6631088 < baseStart_6631088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631145 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 3]
def baseStart_6631145 : Nat := 118140960795 + 6631145 * 2 ^ 59
def prefixEnd_6631145 : Nat := 4983230072969 + 3 ^ 40 * 6631145 * 2
def baseEnd_6631145 : Nat := 3404964674658563348391425

theorem tailTrace_6631145 : CollatzResearch.WordTrace tailWord_6631145 prefixEnd_6631145 3404964674658563348391425 := by
  unfold tailWord_6631145
  simp only [CollatzResearch.WordTrace]
  refine ⟨241857727561501649247430889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161238485041001099498287259 241857727561501649247430889)
  ·
    refine ⟨181393295671126236935573167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241857727561501649247430889 181393295671126236935573167)
    ·
      refine ⟨272089943506689355403359751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181393295671126236935573167 272089943506689355403359751)
      ·
        refine ⟨408134915260034033105039627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272089943506689355403359751 408134915260034033105039627)
        ·
          refine ⟨612202372890051049657559441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408134915260034033105039627 612202372890051049657559441)
          ·
            refine ⟨459151779667538287243169581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612202372890051049657559441 459151779667538287243169581)
            ·
              refine ⟨172181917375326857716188593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459151779667538287243169581 172181917375326857716188593)
              ·
                refine ⟨129136438031495143287141445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172181917375326857716188593 129136438031495143287141445)
                ·
                  refine ⟨24213082130905339366339021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129136438031495143287141445 24213082130905339366339021)
                  ·
                    refine ⟨9079905799089502262377133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24213082130905339366339021 9079905799089502262377133)
                    ·
                      refine ⟨3404964674658563348391425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9079905799089502262377133 3404964674658563348391425)
                      ·
                        rfl

theorem cell23_6631145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_6631145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631145 prefixEnd_6631145 := by exact prefixLift 6631145
  have htrace : WordTrace (prefixWord ++ tailWord_6631145) baseStart_6631145 baseEnd_6631145 := by
    simpa [prefixWord, tailWord_6631145, baseEnd_6631145] using wordTrace_append hprefix tailTrace_6631145
  have hstable : (prefixWord ++ tailWord_6631145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631145).length < 2 ^ (prefixWord ++ tailWord_6631145).sum := by decide
  have hdescent : baseEnd_6631145 < baseStart_6631145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631165 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_6631165 : Nat := 118140960795 + 6631165 * 2 ^ 59
def prefixEnd_6631165 : Nat := 4983230072969 + 3 ^ 40 * 6631165 * 2
def baseEnd_6631165 : Nat := 1134991648090551090047111

theorem tailTrace_6631165 : CollatzResearch.WordTrace tailWord_6631165 prefixEnd_6631165 1134991648090551090047111 := by
  unfold tailWord_6631165
  simp only [CollatzResearch.WordTrace]
  refine ⟨241858457021429192663158949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161238971347619461775439299 241858457021429192663158949)
  ·
    refine ⟨45348460691517973624342303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241858457021429192663158949 45348460691517973624342303)
    ·
      refine ⟨68022691037276960436513455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45348460691517973624342303 68022691037276960436513455)
      ·
        refine ⟨102034036555915440654770183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68022691037276960436513455 102034036555915440654770183)
        ·
          refine ⟨153051054833873160982155275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102034036555915440654770183 153051054833873160982155275)
          ·
            refine ⟨229576582250809741473232913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153051054833873160982155275 229576582250809741473232913)
            ·
              refine ⟨172182436688107306104924685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229576582250809741473232913 172182436688107306104924685)
              ·
                refine ⟨64568413758040239789346757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172182436688107306104924685 64568413758040239789346757)
                ·
                  refine ⟨12106577579632544960502517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64568413758040239789346757 12106577579632544960502517)
                  ·
                    refine ⟨1134991648090551090047111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12106577579632544960502517 1134991648090551090047111)
                    ·
                      rfl

theorem cell23_6631165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_6631165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631165 prefixEnd_6631165 := by exact prefixLift 6631165
  have htrace : WordTrace (prefixWord ++ tailWord_6631165) baseStart_6631165 baseEnd_6631165 := by
    simpa [prefixWord, tailWord_6631165, baseEnd_6631165] using wordTrace_append hprefix tailTrace_6631165
  have hstable : (prefixWord ++ tailWord_6631165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631165).length < 2 ^ (prefixWord ++ tailWord_6631165).sum := by decide
  have hdescent : baseEnd_6631165 < baseStart_6631165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631169 : List Nat := [1, 2, 4, 1, 1, 1, 6, 2, 5]
def baseStart_6631169 : Nat := 118140960795 + 6631169 * 2 ^ 59
def prefixEnd_6631169 : Nat := 4983230072969 + 3 ^ 40 * 6631169 * 2
def baseEnd_6631169 : Nat := 378330777577141250499035

theorem tailTrace_6631169 : CollatzResearch.WordTrace tailWord_6631169 prefixEnd_6631169 378330777577141250499035 := by
  unfold tailWord_6631169
  simp only [CollatzResearch.WordTrace]
  refine ⟨241858602913414701346304561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161239068608943134230869707 241858602913414701346304561)
  ·
    refine ⟨181393952185061026009728421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241858602913414701346304561 181393952185061026009728421)
    ·
      refine ⟨34011366034698942376824079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181393952185061026009728421 34011366034698942376824079)
      ·
        refine ⟨51017049052048413565236119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34011366034698942376824079 51017049052048413565236119)
        ·
          refine ⟨76525573578072620347854179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51017049052048413565236119 76525573578072620347854179)
          ·
            refine ⟨114788360367108930521781269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76525573578072620347854179 114788360367108930521781269)
            ·
              refine ⟨5380704392208231118208497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114788360367108930521781269 5380704392208231118208497)
              ·
                refine ⟨4035528294156173338656373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380704392208231118208497 4035528294156173338656373)
                ·
                  refine ⟨378330777577141250499035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4035528294156173338656373 378330777577141250499035)
                  ·
                    rfl

theorem cell23_6631169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 5].length) (baseStart_6631169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631169 prefixEnd_6631169 := by exact prefixLift 6631169
  have htrace : WordTrace (prefixWord ++ tailWord_6631169) baseStart_6631169 baseEnd_6631169 := by
    simpa [prefixWord, tailWord_6631169, baseEnd_6631169] using wordTrace_append hprefix tailTrace_6631169
  have hstable : (prefixWord ++ tailWord_6631169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631169).length < 2 ^ (prefixWord ++ tailWord_6631169).sum := by decide
  have hdescent : baseEnd_6631169 < baseStart_6631169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631185 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_6631185 : Nat := 118140960795 + 6631185 * 2 ^ 59
def prefixEnd_6631185 : Nat := 4983230072969 + 3 ^ 40 * 6631185 * 2
def baseEnd_6631185 : Nat := 3404985213884743191891241

theorem tailTrace_6631185 : CollatzResearch.WordTrace tailWord_6631185 prefixEnd_6631185 3404985213884743191891241 := by
  unfold tailWord_6631185
  simp only [CollatzResearch.WordTrace]
  refine ⟨241859186481356736078887009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161239457654237824052591339 241859186481356736078887009)
  ·
    refine ⟨181394389861017552059165257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241859186481356736078887009 181394389861017552059165257)
    ·
      refine ⟨136045792395763164044373943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181394389861017552059165257 136045792395763164044373943)
      ·
        refine ⟨204068688593644746066560915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136045792395763164044373943 204068688593644746066560915)
        ·
          refine ⟨306103032890467119099841373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204068688593644746066560915 306103032890467119099841373)
          ·
            refine ⟨114788637333925169662440515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306103032890467119099841373 114788637333925169662440515)
            ·
              refine ⟨172182956000887754493660773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114788637333925169662440515 172182956000887754493660773)
              ·
                refine ⟨32284304250166453967561395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172182956000887754493660773 32284304250166453967561395)
                ·
                  refine ⟨48426456375249680951342093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32284304250166453967561395 48426456375249680951342093)
                  ·
                    refine ⟨18159921140718630356753285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48426456375249680951342093 18159921140718630356753285)
                    ·
                      refine ⟨3404985213884743191891241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18159921140718630356753285 3404985213884743191891241)
                      ·
                        rfl

theorem cell23_6631185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_6631185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631185 prefixEnd_6631185 := by exact prefixLift 6631185
  have htrace : WordTrace (prefixWord ++ tailWord_6631185) baseStart_6631185 baseEnd_6631185 := by
    simpa [prefixWord, tailWord_6631185, baseEnd_6631185] using wordTrace_append hprefix tailTrace_6631185
  have hstable : (prefixWord ++ tailWord_6631185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631185).length < 2 ^ (prefixWord ++ tailWord_6631185).sum := by decide
  have hdescent : baseEnd_6631185 < baseStart_6631185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631202 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_6631202 : Nat := 118140960795 + 6631202 * 2 ^ 59
def prefixEnd_6631202 : Nat := 4983230072969 + 3 ^ 40 * 6631202 * 2
def baseEnd_6631202 : Nat := 3404993943055869625378663

theorem tailTrace_6631202 : CollatzResearch.WordTrace tailWord_6631202 prefixEnd_6631202 3404993943055869625378663 := by
  unfold tailWord_6631202
  simp only [CollatzResearch.WordTrace]
  refine ⟨60464951630573786995563965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161239871014863431988170573 60464951630573786995563965)
  ·
    refine ⟨22674356861465170123336487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60464951630573786995563965 22674356861465170123336487)
    ·
      refine ⟨34011535292197755185004731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22674356861465170123336487 34011535292197755185004731)
      ·
        refine ⟨51017302938296632777507097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34011535292197755185004731 51017302938296632777507097)
        ·
          refine ⟨38262977203722474583130323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51017302938296632777507097 38262977203722474583130323)
          ·
            refine ⟨57394465805583711874695485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38262977203722474583130323 57394465805583711874695485)
            ·
              refine ⟨21522924677093891953010807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57394465805583711874695485 21522924677093891953010807)
              ·
                refine ⟨32284387015640837929516211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21522924677093891953010807 32284387015640837929516211)
                ·
                  refine ⟨48426580523461256894274317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32284387015640837929516211 48426580523461256894274317)
                  ·
                    refine ⟨18159967696297971335352869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48426580523461256894274317 18159967696297971335352869)
                    ·
                      refine ⟨3404993943055869625378663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18159967696297971335352869 3404993943055869625378663)
                      ·
                        rfl

theorem cell23_6631202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_6631202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631202 prefixEnd_6631202 := by exact prefixLift 6631202
  have htrace : WordTrace (prefixWord ++ tailWord_6631202) baseStart_6631202 baseEnd_6631202 := by
    simpa [prefixWord, tailWord_6631202, baseEnd_6631202] using wordTrace_append hprefix tailTrace_6631202
  have hstable : (prefixWord ++ tailWord_6631202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631202).length < 2 ^ (prefixWord ++ tailWord_6631202).sum := by decide
  have hdescent : baseEnd_6631202 < baseStart_6631202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631229 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_6631229 : Nat := 118140960795 + 6631229 * 2 ^ 59
def prefixEnd_6631229 : Nat := 4983230072969 + 3 ^ 40 * 6631229 * 2
def baseEnd_6631229 : Nat := 1135002602344513673247013

theorem tailTrace_6631229 : CollatzResearch.WordTrace tailWord_6631229 prefixEnd_6631229 1135002602344513673247013 := by
  unfold tailWord_6631229
  simp only [CollatzResearch.WordTrace]
  refine ⟨241860791293197331593488741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161240527528798221062325827 241860791293197331593488741)
  ·
    refine ⟨45348898367474499673779139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241860791293197331593488741 45348898367474499673779139)
    ·
      refine ⟨68023347551211749510668709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45348898367474499673779139 68023347551211749510668709)
      ·
        refine ⟨12754377665852203033250383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68023347551211749510668709 12754377665852203033250383)
        ·
          refine ⟨19131566498778304549875575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754377665852203033250383 19131566498778304549875575)
          ·
            refine ⟨28697349748167456824813363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19131566498778304549875575 28697349748167456824813363)
            ·
              refine ⟨43046024622251185237220045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28697349748167456824813363 43046024622251185237220045)
              ·
                refine ⟨16142259233344194463957517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43046024622251185237220045 16142259233344194463957517)
                ·
                  refine ⟨6053347212504072923984069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16142259233344194463957517 6053347212504072923984069)
                  ·
                    refine ⟨1135002602344513673247013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6053347212504072923984069 1135002602344513673247013)
                    ·
                      rfl

theorem cell23_6631229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_6631229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631229 prefixEnd_6631229 := by exact prefixLift 6631229
  have htrace : WordTrace (prefixWord ++ tailWord_6631229) baseStart_6631229 baseEnd_6631229 := by
    simpa [prefixWord, tailWord_6631229, baseEnd_6631229] using wordTrace_append hprefix tailTrace_6631229
  have hstable : (prefixWord ++ tailWord_6631229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631229).length < 2 ^ (prefixWord ++ tailWord_6631229).sum := by decide
  have hdescent : baseEnd_6631229 < baseStart_6631229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631343 : List Nat := [1, 1, 2, 1, 2, 2, 5, 4, 1, 2, 2]
def baseStart_6631343 : Nat := 118140960795 + 6631343 * 2 ^ 59
def prefixEnd_6631343 : Nat := 4983230072969 + 3 ^ 40 * 6631343 * 2
def baseEnd_6631343 : Nat := 3405066343828153573715515

theorem tailTrace_6631343 : CollatzResearch.WordTrace tailWord_6631343 prefixEnd_6631343 3405066343828153573715515 := by
  unfold tailWord_6631343
  simp only [CollatzResearch.WordTrace]
  refine ⟨241864949214784329063138683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161243299476522886042092455 241864949214784329063138683)
  ·
    refine ⟨362797423822176493594708025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241864949214784329063138683 362797423822176493594708025)
    ·
      refine ⟨272098067866632370196031019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362797423822176493594708025 272098067866632370196031019)
      ·
        refine ⟨408147101799948555294046529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272098067866632370196031019 408147101799948555294046529)
        ·
          refine ⟨306110326349961416470534897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408147101799948555294046529 306110326349961416470534897)
          ·
            refine ⟨229582744762471062352901173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306110326349961416470534897 229582744762471062352901173)
            ·
              refine ⟨21523382321481662095584485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229582744762471062352901173 21523382321481662095584485)
              ·
                refine ⟨4035634185277811642922091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21523382321481662095584485 4035634185277811642922091)
                ·
                  refine ⟨6053451277916717464383137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035634185277811642922091 6053451277916717464383137)
                  ·
                    refine ⟨4540088458437538098287353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6053451277916717464383137 4540088458437538098287353)
                    ·
                      refine ⟨3405066343828153573715515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540088458437538098287353 3405066343828153573715515)
                      ·
                        rfl

theorem cell23_6631343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4, 1, 2, 2].length) (baseStart_6631343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631343 prefixEnd_6631343 := by exact prefixLift 6631343
  have htrace : WordTrace (prefixWord ++ tailWord_6631343) baseStart_6631343 baseEnd_6631343 := by
    simpa [prefixWord, tailWord_6631343, baseEnd_6631343] using wordTrace_append hprefix tailTrace_6631343
  have hstable : (prefixWord ++ tailWord_6631343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631343).length < 2 ^ (prefixWord ++ tailWord_6631343).sum := by decide
  have hdescent : baseEnd_6631343 < baseStart_6631343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631349 : List Nat := [1, 3, 3, 2, 1, 4, 1, 8]
def baseStart_6631349 : Nat := 118140960795 + 6631349 * 2 ^ 59
def prefixEnd_6631349 : Nat := 4983230072969 + 3 ^ 40 * 6631349 * 2
def baseEnd_6631349 : Nat := 126113682396743724082981

theorem tailTrace_6631349 : CollatzResearch.WordTrace tailWord_6631349 prefixEnd_6631349 126113682396743724082981 := by
  unfold tailWord_6631349
  simp only [CollatzResearch.WordTrace]
  refine ⟨241865168052762592087857101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161243445368508394725238067 241865168052762592087857101)
  ·
    refine ⟨90699438019785972032946413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241865168052762592087857101 90699438019785972032946413)
    ·
      refine ⟨34012289257419739512354905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90699438019785972032946413 34012289257419739512354905)
      ·
        refine ⟨25509216943064804634266179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34012289257419739512354905 25509216943064804634266179)
        ·
          refine ⟨38263825414597206951399269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25509216943064804634266179 38263825414597206951399269)
          ·
            refine ⟨7174467265236976303387363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38263825414597206951399269 7174467265236976303387363)
            ·
              refine ⟨10761700897855464455081045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7174467265236976303387363 10761700897855464455081045)
              ·
                refine ⟨126113682396743724082981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10761700897855464455081045 126113682396743724082981)
                ·
                  rfl

theorem cell23_6631349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 8].length) (baseStart_6631349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631349 prefixEnd_6631349 := by exact prefixLift 6631349
  have htrace : WordTrace (prefixWord ++ tailWord_6631349) baseStart_6631349 baseEnd_6631349 := by
    simpa [prefixWord, tailWord_6631349, baseEnd_6631349] using wordTrace_append hprefix tailTrace_6631349
  have hstable : (prefixWord ++ tailWord_6631349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631349).length < 2 ^ (prefixWord ++ tailWord_6631349).sum := by decide
  have hdescent : baseEnd_6631349 < baseStart_6631349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631359 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 3]
def baseStart_6631359 : Nat := 118140960795 + 6631359 * 2 ^ 59
def prefixEnd_6631359 : Nat := 4983230072969 + 3 ^ 40 * 6631359 * 2
def baseEnd_6631359 : Nat := 3405074559518625511115441

theorem tailTrace_6631359 : CollatzResearch.WordTrace tailWord_6631359 prefixEnd_6631359 3405074559518625511115441 := by
  unfold tailWord_6631359
  simp only [CollatzResearch.WordTrace]
  refine ⟨241865532782726363795721131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161243688521817575863814087 241865532782726363795721131)
  ·
    refine ⟨362798299174089545693581697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241865532782726363795721131 362798299174089545693581697)
    ·
      refine ⟨272098724380567159270186273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362798299174089545693581697 272098724380567159270186273)
      ·
        refine ⟨204074043285425369452639705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272098724380567159270186273 204074043285425369452639705)
        ·
          refine ⟨153055532464069027089479779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204074043285425369452639705 153055532464069027089479779)
          ·
            refine ⟨229583298696103540634219669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153055532464069027089479779 229583298696103540634219669)
            ·
              refine ⟨10761717126379853467229047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229583298696103540634219669 10761717126379853467229047)
              ·
                refine ⟨16142575689569780200843571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10761717126379853467229047 16142575689569780200843571)
                ·
                  refine ⟨24213863534354670301265357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16142575689569780200843571 24213863534354670301265357)
                  ·
                    refine ⟨9080198825383001362974509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24213863534354670301265357 9080198825383001362974509)
                    ·
                      refine ⟨3405074559518625511115441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9080198825383001362974509 3405074559518625511115441)
                      ·
                        rfl

theorem cell23_6631359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_6631359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631359 prefixEnd_6631359 := by exact prefixLift 6631359
  have htrace : WordTrace (prefixWord ++ tailWord_6631359) baseStart_6631359 baseEnd_6631359 := by
    simpa [prefixWord, tailWord_6631359, baseEnd_6631359] using wordTrace_append hprefix tailTrace_6631359
  have hstable : (prefixWord ++ tailWord_6631359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631359).length < 2 ^ (prefixWord ++ tailWord_6631359).sum := by decide
  have hdescent : baseEnd_6631359 < baseStart_6631359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631416 : List Nat := [2, 1, 2, 1, 1, 3, 5, 1, 1, 4, 2]
def baseStart_6631416 : Nat := 118140960795 + 6631416 * 2 ^ 59
def prefixEnd_6631416 : Nat := 4983230072969 + 3 ^ 40 * 6631416 * 2
def baseEnd_6631416 : Nat := 3405103827915931788102679

theorem tailTrace_6631416 : CollatzResearch.WordTrace tailWord_6631416 prefixEnd_6631416 3405103827915931788102679 := by
  unfold tailWord_6631416
  simp only [CollatzResearch.WordTrace]
  refine ⟨120933805871759931265273051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161245074495679908353697401 120933805871759931265273051)
  ·
    refine ⟨181400708807639896897909577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120933805871759931265273051 181400708807639896897909577)
    ·
      refine ⟨136050531605729922673432183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181400708807639896897909577 136050531605729922673432183)
      ·
        refine ⟨204075797408594884010148275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136050531605729922673432183 204075797408594884010148275)
        ·
          refine ⟨306113696112892326015222413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204075797408594884010148275 306113696112892326015222413)
          ·
            refine ⟨114792636042334622255708405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306113696112892326015222413 114792636042334622255708405)
            ·
              refine ⟨10761809628968870836472663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114792636042334622255708405 10761809628968870836472663)
              ·
                refine ⟨16142714443453306254708995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10761809628968870836472663 16142714443453306254708995)
                ·
                  refine ⟨24214071665179959382063493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16142714443453306254708995 24214071665179959382063493)
                  ·
                    refine ⟨4540138437221242384136905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24214071665179959382063493 4540138437221242384136905)
                    ·
                      refine ⟨3405103827915931788102679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540138437221242384136905 3405103827915931788102679)
                      ·
                        rfl

theorem cell23_6631416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_6631416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631416 prefixEnd_6631416 := by exact prefixLift 6631416
  have htrace : WordTrace (prefixWord ++ tailWord_6631416) baseStart_6631416 baseEnd_6631416 := by
    simpa [prefixWord, tailWord_6631416, baseEnd_6631416] using wordTrace_append hprefix tailTrace_6631416
  have hstable : (prefixWord ++ tailWord_6631416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631416).length < 2 ^ (prefixWord ++ tailWord_6631416).sum := by decide
  have hdescent : baseEnd_6631416 < baseStart_6631416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631499 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 5, 4]
def baseStart_6631499 : Nat := 118140960795 + 6631499 * 2 ^ 59
def prefixEnd_6631499 : Nat := 4983230072969 + 3 ^ 40 * 6631499 * 2
def baseEnd_6631499 : Nat := 1135048815603418321121599

theorem tailTrace_6631499 : CollatzResearch.WordTrace tailWord_6631499 prefixEnd_6631499 1135048815603418321121599 := by
  unfold tailWord_6631499
  simp only [CollatzResearch.WordTrace]
  refine ⟨241870639002219167705817551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161247092668146111803878367 241870639002219167705817551)
  ·
    refine ⟨362805958503328751558726327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241870639002219167705817551 362805958503328751558726327)
    ·
      refine ⟨544208937754993127338089491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362805958503328751558726327 544208937754993127338089491)
      ·
        refine ⟨816313406632489691007134237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544208937754993127338089491 816313406632489691007134237)
        ·
          refine ⟨306117527487183634127675339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 816313406632489691007134237 306117527487183634127675339)
          ·
            refine ⟨459176291230775451191513009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306117527487183634127675339 459176291230775451191513009)
            ·
              refine ⟨344382218423081588393634757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459176291230775451191513009 344382218423081588393634757)
              ·
                refine ⟨64571665954327797823806517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344382218423081588393634757 64571665954327797823806517)
                ·
                  refine ⟨6053593683218231045981861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64571665954327797823806517 6053593683218231045981861)
                  ·
                    refine ⟨1135048815603418321121599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6053593683218231045981861 1135048815603418321121599)
                    ·
                      rfl

theorem cell23_6631499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 4].length) (baseStart_6631499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631499 prefixEnd_6631499 := by exact prefixLift 6631499
  have htrace : WordTrace (prefixWord ++ tailWord_6631499) baseStart_6631499 baseEnd_6631499 := by
    simpa [prefixWord, tailWord_6631499, baseEnd_6631499] using wordTrace_append hprefix tailTrace_6631499
  have hstable : (prefixWord ++ tailWord_6631499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631499).length < 2 ^ (prefixWord ++ tailWord_6631499).sum := by decide
  have hdescent : baseEnd_6631499 < baseStart_6631499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631510 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_6631510 : Nat := 118140960795 + 6631510 * 2 ^ 59
def prefixEnd_6631510 : Nat := 4983230072969 + 3 ^ 40 * 6631510 * 2
def baseEnd_6631510 : Nat := 3405152095097454420327247

theorem tailTrace_6631510 : CollatzResearch.WordTrace tailWord_6631510 prefixEnd_6631510 3405152095097454420327247 := by
  unfold tailWord_6631510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15116940012823707286529249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161247360136786211056311989 15116940012823707286529249)
  ·
    refine ⟨11337705009617780464896937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15116940012823707286529249 11337705009617780464896937)
    ·
      refine ⟨8503278757213335348672703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11337705009617780464896937 8503278757213335348672703)
      ·
        refine ⟨12754918135820003023009055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503278757213335348672703 12754918135820003023009055)
        ·
          refine ⟨19132377203730004534513583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12754918135820003023009055 19132377203730004534513583)
          ·
            refine ⟨28698565805595006801770375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19132377203730004534513583 28698565805595006801770375)
            ·
              refine ⟨43047848708392510202655563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28698565805595006801770375 43047848708392510202655563)
              ·
                refine ⟨64571773062588765303983345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43047848708392510202655563 64571773062588765303983345)
                ·
                  refine ⟨48428829796941573977987509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64571773062588765303983345 48428829796941573977987509)
                  ·
                    refine ⟨4540202793463272560436329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48428829796941573977987509 4540202793463272560436329)
                    ·
                      refine ⟨3405152095097454420327247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540202793463272560436329 3405152095097454420327247)
                      ·
                        rfl

theorem cell23_6631510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_6631510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631510 prefixEnd_6631510 := by exact prefixLift 6631510
  have htrace : WordTrace (prefixWord ++ tailWord_6631510) baseStart_6631510 baseEnd_6631510 := by
    simpa [prefixWord, tailWord_6631510, baseEnd_6631510] using wordTrace_append hprefix tailTrace_6631510
  have hstable : (prefixWord ++ tailWord_6631510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631510).length < 2 ^ (prefixWord ++ tailWord_6631510).sum := by decide
  have hdescent : baseEnd_6631510 < baseStart_6631510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631529 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 6]
def baseStart_6631529 : Nat := 118140960795 + 6631529 * 2 ^ 59
def prefixEnd_6631529 : Nat := 4983230072969 + 3 ^ 40 * 6631529 * 2
def baseEnd_6631529 : Nat := 378351316803321093998851

theorem tailTrace_6631529 : CollatzResearch.WordTrace tailWord_6631529 prefixEnd_6631529 378351316803321093998851 := by
  unfold tailWord_6631529
  simp only [CollatzResearch.WordTrace]
  refine ⟨241871733192110482829409641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161247822128073655219606427 241871733192110482829409641)
  ·
    refine ⟨181403799894082862122057231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241871733192110482829409641 181403799894082862122057231)
    ·
      refine ⟨272105699841124293183085847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181403799894082862122057231 272105699841124293183085847)
      ·
        refine ⟨408158549761686439774628771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272105699841124293183085847 408158549761686439774628771)
        ·
          refine ⟨612237824642529659661943157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408158549761686439774628771 612237824642529659661943157)
          ·
            refine ⟨57397296060237155593307171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 612237824642529659661943157 57397296060237155593307171)
            ·
              refine ⟨86095944090355733389960757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57397296060237155593307171 86095944090355733389960757)
              ·
                refine ⟨8071494758470850005308821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86095944090355733389960757 8071494758470850005308821)
                ·
                  refine ⟨378351316803321093998851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8071494758470850005308821 378351316803321093998851)
                  ·
                    rfl

theorem cell23_6631529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 6].length) (baseStart_6631529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631529 prefixEnd_6631529 := by exact prefixLift 6631529
  have htrace : WordTrace (prefixWord ++ tailWord_6631529) baseStart_6631529 baseEnd_6631529 := by
    simpa [prefixWord, tailWord_6631529, baseEnd_6631529] using wordTrace_append hprefix tailTrace_6631529
  have hstable : (prefixWord ++ tailWord_6631529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631529).length < 2 ^ (prefixWord ++ tailWord_6631529).sum := by decide
  have hdescent : baseEnd_6631529 < baseStart_6631529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631543 : List Nat := [1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_6631543 : Nat := 118140960795 + 6631543 * 2 ^ 59
def prefixEnd_6631543 : Nat := 4983230072969 + 3 ^ 40 * 6631543 * 2
def baseEnd_6631543 : Nat := 3405169039959052791214595

theorem tailTrace_6631543 : CollatzResearch.WordTrace tailWord_6631543 prefixEnd_6631543 3405169039959052791214595 := by
  unfold tailWord_6631543
  simp only [CollatzResearch.WordTrace]
  refine ⟨241872243814059763220419283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161248162542706508813612855 241872243814059763220419283)
  ·
    refine ⟨362808365721089644830628925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241872243814059763220419283 362808365721089644830628925)
    ·
      refine ⟨136053137145408616811485847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362808365721089644830628925 136053137145408616811485847)
      ·
        refine ⟨204079705718112925217228771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136053137145408616811485847 204079705718112925217228771)
        ·
          refine ⟨306119558577169387825843157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204079705718112925217228771 306119558577169387825843157)
          ·
            refine ⟨7174677154152407527168199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 306119558577169387825843157 7174677154152407527168199)
            ·
              refine ⟨10762015731228611290752299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7174677154152407527168199 10762015731228611290752299)
              ·
                refine ⟨16143023596842916936128449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10762015731228611290752299 16143023596842916936128449)
                ·
                  refine ⟨12107267697632187702096337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16143023596842916936128449 12107267697632187702096337)
                  ·
                    refine ⟨9080450773224140776572253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12107267697632187702096337 9080450773224140776572253)
                    ·
                      refine ⟨3405169039959052791214595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9080450773224140776572253 3405169039959052791214595)
                      ·
                        rfl

theorem cell23_6631543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_6631543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631543 prefixEnd_6631543 := by exact prefixLift 6631543
  have htrace : WordTrace (prefixWord ++ tailWord_6631543) baseStart_6631543 baseEnd_6631543 := by
    simpa [prefixWord, tailWord_6631543, baseEnd_6631543] using wordTrace_append hprefix tailTrace_6631543
  have hstable : (prefixWord ++ tailWord_6631543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631543).length < 2 ^ (prefixWord ++ tailWord_6631543).sum := by decide
  have hdescent : baseEnd_6631543 < baseStart_6631543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631573 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_6631573 : Nat := 118140960795 + 6631573 * 2 ^ 59
def prefixEnd_6631573 : Nat := 4983230072969 + 3 ^ 40 * 6631573 * 2
def baseEnd_6631573 : Nat := 3405184444378687673839457

theorem tailTrace_6631573 : CollatzResearch.WordTrace tailWord_6631573 prefixEnd_6631573 3405184444378687673839457 := by
  unfold tailWord_6631573
  simp only [CollatzResearch.WordTrace]
  refine ⟨241873338003951078344011373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161248892002634052229340915 241873338003951078344011373)
  ·
    refine ⟨90702501751481654379004265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241873338003951078344011373 90702501751481654379004265)
    ·
      refine ⟨68026876313611240784253199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90702501751481654379004265 68026876313611240784253199)
      ·
        refine ⟨102040314470416861176379799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68026876313611240784253199 102040314470416861176379799)
        ·
          refine ⟨153060471705625291764569699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102040314470416861176379799 153060471705625291764569699)
          ·
            refine ⟨229590707558437937646854549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153060471705625291764569699 229590707558437937646854549)
            ·
              refine ⟨10762064416801778327196307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229590707558437937646854549 10762064416801778327196307)
              ·
                refine ⟨16143096625202667490794461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10762064416801778327196307 16143096625202667490794461)
                ·
                  refine ⟨6053661234451000309047923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16143096625202667490794461 6053661234451000309047923)
                  ·
                    refine ⟨9080491851676500463571885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6053661234451000309047923 9080491851676500463571885)
                    ·
                      refine ⟨3405184444378687673839457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9080491851676500463571885 3405184444378687673839457)
                      ·
                        rfl

theorem cell23_6631573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_6631573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631573 prefixEnd_6631573 := by exact prefixLift 6631573
  have htrace : WordTrace (prefixWord ++ tailWord_6631573) baseStart_6631573 baseEnd_6631573 := by
    simpa [prefixWord, tailWord_6631573, baseEnd_6631573] using wordTrace_append hprefix tailTrace_6631573
  have hstable : (prefixWord ++ tailWord_6631573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631573).length < 2 ^ (prefixWord ++ tailWord_6631573).sum := by decide
  have hdescent : baseEnd_6631573 < baseStart_6631573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631583 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6631583 : Nat := 118140960795 + 6631583 * 2 ^ 59
def prefixEnd_6631583 : Nat := 4983230072969 + 3 ^ 40 * 6631583 * 2
def baseEnd_6631583 : Nat := 3405189579185232634714411

theorem tailTrace_6631583 : CollatzResearch.WordTrace tailWord_6631583 prefixEnd_6631583 3405189579185232634714411 := by
  unfold tailWord_6631583
  simp only [CollatzResearch.WordTrace]
  refine ⟨241873702733914850051875403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161249135155943233367916935 241873702733914850051875403)
  ·
    refine ⟨362810554100872275077813105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241873702733914850051875403 362810554100872275077813105)
    ·
      refine ⟨272107915575654206308359829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362810554100872275077813105 272107915575654206308359829)
      ·
        refine ⟨12755058542608790920704367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272107915575654206308359829 12755058542608790920704367)
        ·
          refine ⟨19132587813913186381056551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12755058542608790920704367 19132587813913186381056551)
          ·
            refine ⟨28698881720869779571584827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19132587813913186381056551 28698881720869779571584827)
            ·
              refine ⟨43048322581304669357377241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28698881720869779571584827 43048322581304669357377241)
              ·
                refine ⟨32286241935978502018032931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43048322581304669357377241 32286241935978502018032931)
                ·
                  refine ⟨48429362903967753027049397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32286241935978502018032931 48429362903967753027049397)
                  ·
                    refine ⟨4540252772246976846285881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48429362903967753027049397 4540252772246976846285881)
                    ·
                      refine ⟨3405189579185232634714411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540252772246976846285881 3405189579185232634714411)
                      ·
                        rfl

theorem cell23_6631583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6631583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631583 prefixEnd_6631583 := by exact prefixLift 6631583
  have htrace : WordTrace (prefixWord ++ tailWord_6631583) baseStart_6631583 baseEnd_6631583 := by
    simpa [prefixWord, tailWord_6631583, baseEnd_6631583] using wordTrace_append hprefix tailTrace_6631583
  have hstable : (prefixWord ++ tailWord_6631583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631583).length < 2 ^ (prefixWord ++ tailWord_6631583).sum := by decide
  have hdescent : baseEnd_6631583 < baseStart_6631583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631599 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_6631599 : Nat := 118140960795 + 6631599 * 2 ^ 59
def prefixEnd_6631599 : Nat := 4983230072969 + 3 ^ 40 * 6631599 * 2
def baseEnd_6631599 : Nat := 3405197794875704572114337

theorem tailTrace_6631599 : CollatzResearch.WordTrace tailWord_6631599 prefixEnd_6631599 3405197794875704572114337 := by
  unfold tailWord_6631599
  simp only [CollatzResearch.WordTrace]
  refine ⟨241874286301856884784457851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161249524201237923189638567 241874286301856884784457851)
  ·
    refine ⟨362811429452785327176686777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241874286301856884784457851 362811429452785327176686777)
    ·
      refine ⟨272108572089588995382515083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362811429452785327176686777 272108572089588995382515083)
      ·
        refine ⟨408162858134383493073772625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272108572089588995382515083 408162858134383493073772625)
        ·
          refine ⟨306122143600787619805329469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408162858134383493073772625 306122143600787619805329469)
          ·
            refine ⟨114795803850295357426998551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306122143600787619805329469 114795803850295357426998551)
            ·
              refine ⟨172193705775443036140497827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114795803850295357426998551 172193705775443036140497827)
              ·
                refine ⟨258290558663164554210746741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172193705775443036140497827 258290558663164554210746741)
                ·
                  refine ⟨24214739874671676957257507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258290558663164554210746741 24214739874671676957257507)
                  ·
                    refine ⟨36322109812007515435886261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24214739874671676957257507 36322109812007515435886261)
                    ·
                      refine ⟨3405197794875704572114337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36322109812007515435886261 3405197794875704572114337)
                      ·
                        rfl

theorem cell23_6631599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_6631599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631599 prefixEnd_6631599 := by exact prefixLift 6631599
  have htrace : WordTrace (prefixWord ++ tailWord_6631599) baseStart_6631599 baseEnd_6631599 := by
    simpa [prefixWord, tailWord_6631599, baseEnd_6631599] using wordTrace_append hprefix tailTrace_6631599
  have hstable : (prefixWord ++ tailWord_6631599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631599).length < 2 ^ (prefixWord ++ tailWord_6631599).sum := by decide
  have hdescent : baseEnd_6631599 < baseStart_6631599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631607 : List Nat := [1, 1, 3, 1, 4, 4, 1, 3, 1, 1, 3]
def baseStart_6631607 : Nat := 118140960795 + 6631607 * 2 ^ 59
def prefixEnd_6631607 : Nat := 4983230072969 + 3 ^ 40 * 6631607 * 2
def baseEnd_6631607 : Nat := 3405201902720940540814301

theorem tailTrace_6631607 : CollatzResearch.WordTrace tailWord_6631607 prefixEnd_6631607 3405201902720940540814301 := by
  unfold tailWord_6631607
  simp only [CollatzResearch.WordTrace]
  refine ⟨241874578085827902150749075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161249718723885268100499383 241874578085827902150749075)
  ·
    refine ⟨362811867128741853226123613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241874578085827902150749075 362811867128741853226123613)
    ·
      refine ⟨136054450173278194959796355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362811867128741853226123613 136054450173278194959796355)
      ·
        refine ⟨204081675259917292439694533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136054450173278194959796355 204081675259917292439694533)
        ·
          refine ⟨38265314111234492332442725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204081675259917292439694533 38265314111234492332442725)
          ·
            refine ⟨7174746395856467312333011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38265314111234492332442725 7174746395856467312333011)
            ·
              refine ⟨10762119593784700968499517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7174746395856467312333011 10762119593784700968499517)
              ·
                refine ⟨4035794847669262863187319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10762119593784700968499517 4035794847669262863187319)
                ·
                  refine ⟨6053692271503894294780979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035794847669262863187319 6053692271503894294780979)
                  ·
                    refine ⟨9080538407255841442171469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6053692271503894294780979 9080538407255841442171469)
                    ·
                      refine ⟨3405201902720940540814301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9080538407255841442171469 3405201902720940540814301)
                      ·
                        rfl

theorem cell23_6631607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_6631607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631607 prefixEnd_6631607 := by exact prefixLift 6631607
  have htrace : WordTrace (prefixWord ++ tailWord_6631607) baseStart_6631607 baseEnd_6631607 := by
    simpa [prefixWord, tailWord_6631607, baseEnd_6631607] using wordTrace_append hprefix tailTrace_6631607
  have hstable : (prefixWord ++ tailWord_6631607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631607).length < 2 ^ (prefixWord ++ tailWord_6631607).sum := by decide
  have hdescent : baseEnd_6631607 < baseStart_6631607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631616 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_6631616 : Nat := 118140960795 + 6631616 * 2 ^ 59
def prefixEnd_6631616 : Nat := 4983230072969 + 3 ^ 40 * 6631616 * 2
def baseEnd_6631616 : Nat := 3405206524046831005601759

theorem tailTrace_6631616 : CollatzResearch.WordTrace tailWord_6631616 prefixEnd_6631616 3405206524046831005601759 := by
  unfold tailWord_6631616
  simp only [CollatzResearch.WordTrace]
  refine ⟨120937453171397648343913351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161249937561863531125217801 120937453171397648343913351)
  ·
    refine ⟨181406179757096472515870027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120937453171397648343913351 181406179757096472515870027)
    ·
      refine ⟨272109269635644708773805041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181406179757096472515870027 272109269635644708773805041)
      ·
        refine ⟨204081952226733531580353781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272109269635644708773805041 204081952226733531580353781)
        ·
          refine ⟨19132683021256268585658167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204081952226733531580353781 19132683021256268585658167)
          ·
            refine ⟨28699024531884402878487251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19132683021256268585658167 28699024531884402878487251)
            ·
              refine ⟨43048536797826604317730877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28699024531884402878487251 43048536797826604317730877)
              ·
                refine ⟨16143201299184976619149079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43048536797826604317730877 16143201299184976619149079)
                ·
                  refine ⟨24214801948777464928723619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16143201299184976619149079 24214801948777464928723619)
                  ·
                    refine ⟨36322202923166197393085429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24214801948777464928723619 36322202923166197393085429)
                    ·
                      refine ⟨3405206524046831005601759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36322202923166197393085429 3405206524046831005601759)
                      ·
                        rfl

theorem cell23_6631616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_6631616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631616 prefixEnd_6631616 := by exact prefixLift 6631616
  have htrace : WordTrace (prefixWord ++ tailWord_6631616) baseStart_6631616 baseEnd_6631616 := by
    simpa [prefixWord, tailWord_6631616, baseEnd_6631616] using wordTrace_append hprefix tailTrace_6631616
  have hstable : (prefixWord ++ tailWord_6631616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631616).length < 2 ^ (prefixWord ++ tailWord_6631616).sum := by decide
  have hdescent : baseEnd_6631616 < baseStart_6631616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631617 : List Nat := [1, 2, 6, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_6631617 : Nat := 118140960795 + 6631617 * 2 ^ 59
def prefixEnd_6631617 : Nat := 4983230072969 + 3 ^ 40 * 6631617 * 2
def baseEnd_6631617 : Nat := 3405207037527485501689255

theorem tailTrace_6631617 : CollatzResearch.WordTrace tailWord_6631617 prefixEnd_6631617 3405207037527485501689255 := by
  unfold tailWord_6631617
  simp only [CollatzResearch.WordTrace]
  refine ⟨241874942815791673858613105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161249961877194449239075403 241874942815791673858613105)
  ·
    refine ⟨181406207111843755393959829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241874942815791673858613105 181406207111843755393959829)
    ·
      refine ⟨8503415958367676034091867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 181406207111843755393959829 8503415958367676034091867)
      ·
        refine ⟨12755123937551514051137801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503415958367676034091867 12755123937551514051137801)
        ·
          refine ⟨9566342953163635538353351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12755123937551514051137801 9566342953163635538353351)
          ·
            refine ⟨14349514429745453307530027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9566342953163635538353351 14349514429745453307530027)
            ·
              refine ⟨21524271644618179961295041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14349514429745453307530027 21524271644618179961295041)
              ·
                refine ⟨16143203733463634970971281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21524271644618179961295041 16143203733463634970971281)
                ·
                  refine ⟨12107402800097726228228461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16143203733463634970971281 12107402800097726228228461)
                  ·
                    refine ⟨4540276050036647335585673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12107402800097726228228461 4540276050036647335585673)
                    ·
                      refine ⟨3405207037527485501689255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540276050036647335585673 3405207037527485501689255)
                      ·
                        rfl

theorem cell23_6631617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_6631617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631617 prefixEnd_6631617 := by exact prefixLift 6631617
  have htrace : WordTrace (prefixWord ++ tailWord_6631617) baseStart_6631617 baseEnd_6631617 := by
    simpa [prefixWord, tailWord_6631617, baseEnd_6631617] using wordTrace_append hprefix tailTrace_6631617
  have hstable : (prefixWord ++ tailWord_6631617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631617).length < 2 ^ (prefixWord ++ tailWord_6631617).sum := by decide
  have hdescent : baseEnd_6631617 < baseStart_6631617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631639 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_6631639 : Nat := 118140960795 + 6631639 * 2 ^ 59
def prefixEnd_6631639 : Nat := 4983230072969 + 3 ^ 40 * 6631639 * 2
def baseEnd_6631639 : Nat := 3405218334101884415614153

theorem tailTrace_6631639 : CollatzResearch.WordTrace tailWord_6631639 prefixEnd_6631639 3405218334101884415614153 := by
  unfold tailWord_6631639
  simp only [CollatzResearch.WordTrace]
  refine ⟨241875745221711971615913971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161250496814474647743942647 241875745221711971615913971)
  ·
    refine ⟨362813617832567957423870957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241875745221711971615913971 362813617832567957423870957)
    ·
      refine ⟨136055106687212984033951609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362813617832567957423870957 136055106687212984033951609)
      ·
        refine ⟨102041330015409738025463707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136055106687212984033951609 102041330015409738025463707)
        ·
          refine ⟨153061995023114607038195561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102041330015409738025463707 153061995023114607038195561)
          ·
            refine ⟨114796496267335955278646671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153061995023114607038195561 114796496267335955278646671)
            ·
              refine ⟨172194744401003932917970007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114796496267335955278646671 172194744401003932917970007)
              ·
                refine ⟨258292116601505899376955011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172194744401003932917970007 258292116601505899376955011)
                ·
                  refine ⟨387438174902258849065432517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258292116601505899376955011 387438174902258849065432517)
                  ·
                    refine ⟨72644657794173534199768597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 387438174902258849065432517 72644657794173534199768597)
                    ·
                      refine ⟨3405218334101884415614153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72644657794173534199768597 3405218334101884415614153)
                      ·
                        rfl

theorem cell23_6631639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_6631639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631639 prefixEnd_6631639 := by exact prefixLift 6631639
  have htrace : WordTrace (prefixWord ++ tailWord_6631639) baseStart_6631639 baseEnd_6631639 := by
    simpa [prefixWord, tailWord_6631639, baseEnd_6631639] using wordTrace_append hprefix tailTrace_6631639
  have hstable : (prefixWord ++ tailWord_6631639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631639).length < 2 ^ (prefixWord ++ tailWord_6631639).sum := by decide
  have hdescent : baseEnd_6631639 < baseStart_6631639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631640 : List Nat := [2, 1, 2, 2, 4, 1, 4, 1, 2, 4]
def baseStart_6631640 : Nat := 118140960795 + 6631640 * 2 ^ 59
def prefixEnd_6631640 : Nat := 4983230072969 + 3 ^ 40 * 6631640 * 2
def baseEnd_6631640 : Nat := 1135072949194179637233883

theorem tailTrace_6631640 : CollatzResearch.WordTrace tailWord_6631640 prefixEnd_6631640 1135072949194179637233883 := by
  unfold tailWord_6631640
  simp only [CollatzResearch.WordTrace]
  refine ⟨120937890847354174393350187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161250521129805565857800249 120937890847354174393350187)
  ·
    refine ⟨181406836271031261590025281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120937890847354174393350187 181406836271031261590025281)
    ·
      refine ⟨136055127203273446192518961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181406836271031261590025281 136055127203273446192518961)
      ·
        refine ⟨102041345402455084644389221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136055127203273446192518961 102041345402455084644389221)
        ·
          refine ⟨19132752262960328370822979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102041345402455084644389221 19132752262960328370822979)
          ·
            refine ⟨28699128394440492556234469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19132752262960328370822979 28699128394440492556234469)
            ·
              refine ⟨5381086573957592354293963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28699128394440492556234469 5381086573957592354293963)
              ·
                refine ⟨8071629860936388531440945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381086573957592354293963 8071629860936388531440945)
                ·
                  refine ⟨6053722395702291398580709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8071629860936388531440945 6053722395702291398580709)
                  ·
                    refine ⟨1135072949194179637233883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6053722395702291398580709 1135072949194179637233883)
                    ·
                      rfl

theorem cell23_6631640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_6631640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631640 prefixEnd_6631640 := by exact prefixLift 6631640
  have htrace : WordTrace (prefixWord ++ tailWord_6631640) baseStart_6631640 baseEnd_6631640 := by
    simpa [prefixWord, tailWord_6631640, baseEnd_6631640] using wordTrace_append hprefix tailTrace_6631640
  have hstable : (prefixWord ++ tailWord_6631640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631640).length < 2 ^ (prefixWord ++ tailWord_6631640).sum := by decide
  have hdescent : baseEnd_6631640 < baseStart_6631640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631644 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6631644 : Nat := 118140960795 + 6631644 * 2 ^ 59
def prefixEnd_6631644 : Nat := 4983230072969 + 3 ^ 40 * 6631644 * 2
def baseEnd_6631644 : Nat := 1135073633835052298683877

theorem tailTrace_6631644 : CollatzResearch.WordTrace tailWord_6631644 prefixEnd_6631644 1135073633835052298683877 := by
  unfold tailWord_6631644
  simp only [CollatzResearch.WordTrace]
  refine ⟨120937963793346928734922993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161250618391129238313230657 120937963793346928734922993)
  ·
    refine ⟨90703472845010196551192245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120937963793346928734922993 90703472845010196551192245)
    ·
      refine ⟨8503450579219705926674273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90703472845010196551192245 8503450579219705926674273)
      ·
        refine ⟨6377587934414779445005705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8503450579219705926674273 6377587934414779445005705)
        ·
          refine ⟨4783190950811084583754279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6377587934414779445005705 4783190950811084583754279)
          ·
            refine ⟨7174786426216626875631419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4783190950811084583754279 7174786426216626875631419)
            ·
              refine ⟨10762179639324940313447129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7174786426216626875631419 10762179639324940313447129)
              ·
                refine ⟨8071634729493705235085347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10762179639324940313447129 8071634729493705235085347)
                ·
                  refine ⟨12107452094240557852628021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8071634729493705235085347 12107452094240557852628021)
                  ·
                    refine ⟨1135073633835052298683877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12107452094240557852628021 1135073633835052298683877)
                    ·
                      rfl

theorem cell23_6631644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6631644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631644 prefixEnd_6631644 := by exact prefixLift 6631644
  have htrace : WordTrace (prefixWord ++ tailWord_6631644) baseStart_6631644 baseEnd_6631644 := by
    simpa [prefixWord, tailWord_6631644, baseEnd_6631644] using wordTrace_append hprefix tailTrace_6631644
  have hstable : (prefixWord ++ tailWord_6631644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631644).length < 2 ^ (prefixWord ++ tailWord_6631644).sum := by decide
  have hdescent : baseEnd_6631644 < baseStart_6631644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631663 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 3]
def baseStart_6631663 : Nat := 118140960795 + 6631663 * 2 ^ 59
def prefixEnd_6631663 : Nat := 4983230072969 + 3 ^ 40 * 6631663 * 2
def baseEnd_6631663 : Nat := 3405230657637592321714043

theorem tailTrace_6631663 : CollatzResearch.WordTrace tailWord_6631663 prefixEnd_6631663 3405230657637592321714043 := by
  unfold tailWord_6631663
  simp only [CollatzResearch.WordTrace]
  refine ⟨241876620573625023714787643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161251080382416682476525095 241876620573625023714787643)
  ·
    refine ⟨362814930860437535572181465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241876620573625023714787643 362814930860437535572181465)
    ·
      refine ⟨272111198145328151679136099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362814930860437535572181465 272111198145328151679136099)
      ·
        refine ⟨408166797217992227518704149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272111198145328151679136099 408166797217992227518704149)
        ·
          refine ⟨19132818619593385664939257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 408166797217992227518704149 19132818619593385664939257)
          ·
            refine ⟨14349613964695039248704443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19132818619593385664939257 14349613964695039248704443)
            ·
              refine ⟨21524420947042558873056665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14349613964695039248704443 21524420947042558873056665)
              ·
                refine ⟨16143315710281919154792499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21524420947042558873056665 16143315710281919154792499)
                ·
                  refine ⟨24214973565422878732188749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16143315710281919154792499 24214973565422878732188749)
                  ·
                    refine ⟨9080615087033579524570781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24214973565422878732188749 9080615087033579524570781)
                    ·
                      refine ⟨3405230657637592321714043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9080615087033579524570781 3405230657637592321714043)
                      ·
                        rfl

theorem cell23_6631663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_6631663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631663 prefixEnd_6631663 := by exact prefixLift 6631663
  have htrace : WordTrace (prefixWord ++ tailWord_6631663) baseStart_6631663 baseEnd_6631663 := by
    simpa [prefixWord, tailWord_6631663, baseEnd_6631663] using wordTrace_append hprefix tailTrace_6631663
  have hstable : (prefixWord ++ tailWord_6631663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631663).length < 2 ^ (prefixWord ++ tailWord_6631663).sum := by decide
  have hdescent : baseEnd_6631663 < baseStart_6631663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631737 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 4, 2, 2]
def baseStart_6631737 : Nat := 118140960795 + 6631737 * 2 ^ 59
def prefixEnd_6631737 : Nat := 4983230072969 + 3 ^ 40 * 6631737 * 2
def baseEnd_6631737 : Nat := 3405268655206025032188703

theorem tailTrace_6631737 : CollatzResearch.WordTrace tailWord_6631737 prefixEnd_6631737 3405268655206025032188703 := by
  unfold tailWord_6631737
  simp only [CollatzResearch.WordTrace]
  refine ⟨241879319575356934352981465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161252879716904622901987643 241879319575356934352981465)
  ·
    refine ⟨181409489681517700764736099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241879319575356934352981465 181409489681517700764736099)
    ·
      refine ⟨272114234522276551147104149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181409489681517700764736099 272114234522276551147104149)
      ·
        refine ⟨12755354743231713335020507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272114234522276551147104149 12755354743231713335020507)
        ·
          refine ⟨19133032114847570002530761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12755354743231713335020507 19133032114847570002530761)
          ·
            refine ⟨14349774086135677501898071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19133032114847570002530761 14349774086135677501898071)
            ·
              refine ⟨21524661129203516252847107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14349774086135677501898071 21524661129203516252847107)
              ·
                refine ⟨32286991693805274379270661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21524661129203516252847107 32286991693805274379270661)
                ·
                  refine ⟨6053810942588488946113249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32286991693805274379270661 6053810942588488946113249)
                  ·
                    refine ⟨4540358206941366709584937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6053810942588488946113249 4540358206941366709584937)
                    ·
                      refine ⟨3405268655206025032188703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540358206941366709584937 3405268655206025032188703)
                      ·
                        rfl

theorem cell23_6631737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_6631737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631737 prefixEnd_6631737 := by exact prefixLift 6631737
  have htrace : WordTrace (prefixWord ++ tailWord_6631737) baseStart_6631737 baseEnd_6631737 := by
    simpa [prefixWord, tailWord_6631737, baseEnd_6631737] using wordTrace_append hprefix tailTrace_6631737
  have hstable : (prefixWord ++ tailWord_6631737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631737).length < 2 ^ (prefixWord ++ tailWord_6631737).sum := by decide
  have hdescent : baseEnd_6631737 < baseStart_6631737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631743 : List Nat := [1, 1, 2, 2, 4, 1, 1, 6, 5]
def baseStart_6631743 : Nat := 118140960795 + 6631743 * 2 ^ 59
def prefixEnd_6631743 : Nat := 4983230072969 + 3 ^ 40 * 6631743 * 2
def baseEnd_6631743 : Nat := 378363526232216889857075

theorem tailTrace_6631743 : CollatzResearch.WordTrace tailWord_6631743 prefixEnd_6631743 378363526232216889857075 := by
  unfold tailWord_6631743
  simp only [CollatzResearch.WordTrace]
  refine ⟨241879538413335197377699883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161253025608890131585133255 241879538413335197377699883)
  ·
    refine ⟨362819307620002796066549825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241879538413335197377699883 362819307620002796066549825)
    ·
      refine ⟨272114480715002097049912369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362819307620002796066549825 272114480715002097049912369)
      ·
        refine ⟨204085860536251572787434277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272114480715002097049912369 204085860536251572787434277)
        ·
          refine ⟨38266098850547169897643927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204085860536251572787434277 38266098850547169897643927)
          ·
            refine ⟨57399148275820754846465891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38266098850547169897643927 57399148275820754846465891)
            ·
              refine ⟨86098722413731132269698837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57399148275820754846465891 86098722413731132269698837)
              ·
                refine ⟨4035877613143646825142133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86098722413731132269698837 4035877613143646825142133)
                ·
                  refine ⟨378363526232216889857075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4035877613143646825142133 378363526232216889857075)
                  ·
                    rfl

theorem cell23_6631743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 5].length) (baseStart_6631743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631743 prefixEnd_6631743 := by exact prefixLift 6631743
  have htrace : WordTrace (prefixWord ++ tailWord_6631743) baseStart_6631743 baseEnd_6631743 := by
    simpa [prefixWord, tailWord_6631743, baseEnd_6631743] using wordTrace_append hprefix tailTrace_6631743
  have hstable : (prefixWord ++ tailWord_6631743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631743).length < 2 ^ (prefixWord ++ tailWord_6631743).sum := by decide
  have hdescent : baseEnd_6631743 < baseStart_6631743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631756 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_6631756 : Nat := 118140960795 + 6631756 * 2 ^ 59
def prefixEnd_6631756 : Nat := 4983230072969 + 3 ^ 40 * 6631756 * 2
def baseEnd_6631756 : Nat := 1135092803779486819283705

theorem tailTrace_6631756 : CollatzResearch.WordTrace tailWord_6631756 prefixEnd_6631756 1135092803779486819283705 := by
  unfold tailWord_6631756
  simp only [CollatzResearch.WordTrace]
  refine ⟨120940006281144050298961561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161253341708192067065282081 120940006281144050298961561)
  ·
    refine ⟨90705004710858037724221171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120940006281144050298961561 90705004710858037724221171)
    ·
      refine ⟨136057507066287056586331757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90705004710858037724221171 136057507066287056586331757)
      ·
        refine ⟨51021565149857646219874409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136057507066287056586331757 51021565149857646219874409)
        ·
          refine ⟨38266173862393234664905807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51021565149857646219874409 38266173862393234664905807)
          ·
            refine ⟨57399260793589851997358711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38266173862393234664905807 57399260793589851997358711)
            ·
              refine ⟨86098891190384777996038067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57399260793589851997358711 86098891190384777996038067)
              ·
                refine ⟨129148336785577166994057101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86098891190384777996038067 129148336785577166994057101)
                ·
                  refine ⟨48430626294591437622771413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129148336785577166994057101 48430626294591437622771413)
                  ·
                    refine ⟨1135092803779486819283705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48430626294591437622771413 1135092803779486819283705)
                    ·
                      rfl

theorem cell23_6631756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_6631756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631756 prefixEnd_6631756 := by exact prefixLift 6631756
  have htrace : WordTrace (prefixWord ++ tailWord_6631756) baseStart_6631756 baseEnd_6631756 := by
    simpa [prefixWord, tailWord_6631756, baseEnd_6631756] using wordTrace_append hprefix tailTrace_6631756
  have hstable : (prefixWord ++ tailWord_6631756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631756).length < 2 ^ (prefixWord ++ tailWord_6631756).sum := by decide
  have hdescent : baseEnd_6631756 < baseStart_6631756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631813 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_6631813 : Nat := 118140960795 + 6631813 * 2 ^ 59
def prefixEnd_6631813 : Nat := 4983230072969 + 3 ^ 40 * 6631813 * 2
def baseEnd_6631813 : Nat := 3405307679735766734838353

theorem tailTrace_6631813 : CollatzResearch.WordTrace tailWord_6631813 prefixEnd_6631813 3405307679735766734838353 := by
  unfold tailWord_6631813
  simp only [CollatzResearch.WordTrace]
  refine ⟨241882091523081599332748093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161254727682054399555165395 241882091523081599332748093)
  ·
    refine ⟨90705784321155599749780535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241882091523081599332748093 90705784321155599749780535)
    ·
      refine ⟨136058676481733399624670803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90705784321155599749780535 136058676481733399624670803)
      ·
        refine ⟨204088014722600099437006205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136058676481733399624670803 204088014722600099437006205)
        ·
          refine ⟨76533005520975037288877327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204088014722600099437006205 76533005520975037288877327)
          ·
            refine ⟨114799508281462555933315991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76533005520975037288877327 114799508281462555933315991)
            ·
              refine ⟨172199262422193833899973987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114799508281462555933315991 172199262422193833899973987)
              ·
                refine ⟨258298893633290750849960981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172199262422193833899973987 258298893633290750849960981)
                ·
                  refine ⟨12107760639060503946091921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 258298893633290750849960981 12107760639060503946091921)
                  ·
                    refine ⟨9080820479295377959568941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12107760639060503946091921 9080820479295377959568941)
                    ·
                      refine ⟨3405307679735766734838353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9080820479295377959568941 3405307679735766734838353)
                      ·
                        rfl

theorem cell23_6631813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_6631813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631813 prefixEnd_6631813 := by exact prefixLift 6631813
  have htrace : WordTrace (prefixWord ++ tailWord_6631813) baseStart_6631813 baseEnd_6631813 := by
    simpa [prefixWord, tailWord_6631813, baseEnd_6631813] using wordTrace_append hprefix tailTrace_6631813
  have hstable : (prefixWord ++ tailWord_6631813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631813).length < 2 ^ (prefixWord ++ tailWord_6631813).sum := by decide
  have hdescent : baseEnd_6631813 < baseStart_6631813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631863 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 3, 5]
def baseStart_6631863 : Nat := 118140960795 + 6631863 * 2 ^ 59
def prefixEnd_6631863 : Nat := 4983230072969 + 3 ^ 40 * 6631863 * 2
def baseEnd_6631863 : Nat := 1135111117922830513071041

theorem tailTrace_6631863 : CollatzResearch.WordTrace tailWord_6631863 prefixEnd_6631863 1135111117922830513071041 := by
  unfold tailWord_6631863
  simp only [CollatzResearch.WordTrace]
  refine ⟨241883915172900457872068243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161255943448600305248045495 241883915172900457872068243)
  ·
    refine ⟨362825872759350686808102365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241883915172900457872068243 362825872759350686808102365)
    ·
      refine ⟨136059702284756507553038387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362825872759350686808102365 136059702284756507553038387)
      ·
        refine ⟨204089553427134761329557581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136059702284756507553038387 204089553427134761329557581)
        ·
          refine ⟨76533582535175535498584093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204089553427134761329557581 76533582535175535498584093)
          ·
            refine ⟨28700093450690825811969035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76533582535175535498584093 28700093450690825811969035)
            ·
              refine ⟨43050140176036238717953553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28700093450690825811969035 43050140176036238717953553)
              ·
                refine ⟨32287605132027179038465165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43050140176036238717953553 32287605132027179038465165)
                ·
                  refine ⟨12107851924510192139424437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32287605132027179038465165 12107851924510192139424437)
                  ·
                    refine ⟨1135111117922830513071041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12107851924510192139424437 1135111117922830513071041)
                    ·
                      rfl

theorem cell23_6631863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_6631863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631863 prefixEnd_6631863 := by exact prefixLift 6631863
  have htrace : WordTrace (prefixWord ++ tailWord_6631863) baseStart_6631863 baseEnd_6631863 := by
    simpa [prefixWord, tailWord_6631863, baseEnd_6631863] using wordTrace_append hprefix tailTrace_6631863
  have hstable : (prefixWord ++ tailWord_6631863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631863).length < 2 ^ (prefixWord ++ tailWord_6631863).sum := by decide
  have hdescent : baseEnd_6631863 < baseStart_6631863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631937 : List Nat := [1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_6631937 : Nat := 118140960795 + 6631937 * 2 ^ 59
def prefixEnd_6631937 : Nat := 4983230072969 + 3 ^ 40 * 6631937 * 2
def baseEnd_6631937 : Nat := 3405371351336924249687783

theorem tailTrace_6631937 : CollatzResearch.WordTrace tailWord_6631937 prefixEnd_6631937 3405371351336924249687783 := by
  unfold tailWord_6631937
  simp only [CollatzResearch.WordTrace]
  refine ⟨241886614174632368510262065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161257742783088245673508043 241886614174632368510262065)
  ·
    refine ⟨181414960630974276382696549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241886614174632368510262065 181414960630974276382696549)
    ·
      refine ⟨34015305118307676821755603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181414960630974276382696549 34015305118307676821755603)
      ·
        refine ⟨51022957677461515232633405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34015305118307676821755603 51022957677461515232633405)
        ·
          refine ⟨19133609129048068212237527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51022957677461515232633405 19133609129048068212237527)
          ·
            refine ⟨28700413693572102318356291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19133609129048068212237527 28700413693572102318356291)
            ·
              refine ⟨43050620540358153477534437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28700413693572102318356291 43050620540358153477534437)
              ·
                refine ⟨8071991351317153777037707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43050620540358153477534437 8071991351317153777037707)
                ·
                  refine ⟨12107987026975730665556561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8071991351317153777037707 12107987026975730665556561)
                  ·
                    refine ⟨9080990270231797999167421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12107987026975730665556561 9080990270231797999167421)
                    ·
                      refine ⟨3405371351336924249687783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9080990270231797999167421 3405371351336924249687783)
                      ·
                        rfl

theorem cell23_6631937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_6631937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631937 prefixEnd_6631937 := by exact prefixLift 6631937
  have htrace : WordTrace (prefixWord ++ tailWord_6631937) baseStart_6631937 baseEnd_6631937 := by
    simpa [prefixWord, tailWord_6631937, baseEnd_6631937] using wordTrace_append hprefix tailTrace_6631937
  have hstable : (prefixWord ++ tailWord_6631937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631937).length < 2 ^ (prefixWord ++ tailWord_6631937).sum := by decide
  have hdescent : baseEnd_6631937 < baseStart_6631937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631940 : List Nat := [2, 3, 2, 3, 1, 2, 1, 9]
def baseStart_6631940 : Nat := 118140960795 + 6631940 * 2 ^ 59
def prefixEnd_6631940 : Nat := 4983230072969 + 3 ^ 40 * 6631940 * 2
def baseEnd_6631940 : Nat := 126124921917736582887047

theorem tailTrace_6631940 : CollatzResearch.WordTrace tailWord_6631940 prefixEnd_6631940 126124921917736582887047 := by
  unfold tailWord_6631940
  simp only [CollatzResearch.WordTrace]
  refine ⟨120943361796810750011310637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161257815729081000015080849 120943361796810750011310637)
  ·
    refine ⟨45353760673804031254241489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120943361796810750011310637 45353760673804031254241489)
    ·
      refine ⟨34015320505353023440681117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45353760673804031254241489 34015320505353023440681117)
      ·
        refine ⟨12755745189507383790255419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34015320505353023440681117 12755745189507383790255419)
        ·
          refine ⟨19133617784261075685383129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12755745189507383790255419 19133617784261075685383129)
          ·
            refine ⟨14350213338195806764037347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19133617784261075685383129 14350213338195806764037347)
            ·
              refine ⟨21525320007293710146056021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14350213338195806764037347 21525320007293710146056021)
              ·
                refine ⟨126124921917736582887047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21525320007293710146056021 126124921917736582887047)
                ·
                  rfl

theorem cell23_6631940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 9].length) (baseStart_6631940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631940 prefixEnd_6631940 := by exact prefixLift 6631940
  have htrace : WordTrace (prefixWord ++ tailWord_6631940) baseStart_6631940 baseEnd_6631940 := by
    simpa [prefixWord, tailWord_6631940, baseEnd_6631940] using wordTrace_append hprefix tailTrace_6631940
  have hstable : (prefixWord ++ tailWord_6631940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631940).length < 2 ^ (prefixWord ++ tailWord_6631940).sum := by decide
  have hdescent : baseEnd_6631940 < baseStart_6631940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631967 : List Nat := [1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 3]
def baseStart_6631967 : Nat := 118140960795 + 6631967 * 2 ^ 59
def prefixEnd_6631967 : Nat := 4983230072969 + 3 ^ 40 * 6631967 * 2
def baseEnd_6631967 : Nat := 3405386755756559132312645

theorem tailTrace_6631967 : CollatzResearch.WordTrace tailWord_6631967 prefixEnd_6631967 3405386755756559132312645 := by
  unfold tailWord_6631967
  simp only [CollatzResearch.WordTrace]
  refine ⟨241887708364523683633854155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161258472243015789089236103 241887708364523683633854155)
  ·
    refine ⟨362831562546785525450781233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241887708364523683633854155 362831562546785525450781233)
    ·
      refine ⟨272123671910089144088085925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362831562546785525450781233 272123671910089144088085925)
      ·
        refine ⟨51023188483141714516516111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 272123671910089144088085925 51023188483141714516516111)
        ·
          refine ⟨76534782724712571774774167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51023188483141714516516111 76534782724712571774774167)
          ·
            refine ⟨114802174087068857662161251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76534782724712571774774167 114802174087068857662161251)
            ·
              refine ⟨172203261130603286493241877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114802174087068857662161251 172203261130603286493241877)
              ·
                refine ⟨8072027865497029054370713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172203261130603286493241877 8072027865497029054370713)
                ·
                  refine ⟨6054020899122771790778035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8072027865497029054370713 6054020899122771790778035)
                  ·
                    refine ⟨9081031348684157686167053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6054020899122771790778035 9081031348684157686167053)
                    ·
                      refine ⟨3405386755756559132312645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9081031348684157686167053 3405386755756559132312645)
                      ·
                        rfl

theorem cell23_6631967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_6631967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631967 prefixEnd_6631967 := by exact prefixLift 6631967
  have htrace : WordTrace (prefixWord ++ tailWord_6631967) baseStart_6631967 baseEnd_6631967 := by
    simpa [prefixWord, tailWord_6631967, baseEnd_6631967] using wordTrace_append hprefix tailTrace_6631967
  have hstable : (prefixWord ++ tailWord_6631967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631967).length < 2 ^ (prefixWord ++ tailWord_6631967).sum := by decide
  have hdescent : baseEnd_6631967 < baseStart_6631967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631968 : List Nat := [2, 1, 1, 6, 3, 1, 1, 1, 3, 2, 2]
def baseStart_6631968 : Nat := 118140960795 + 6631968 * 2 ^ 59
def prefixEnd_6631968 : Nat := 4983230072969 + 3 ^ 40 * 6631968 * 2
def baseEnd_6631968 : Nat := 3405387269237213628400141

theorem tailTrace_6631968 : CollatzResearch.WordTrace tailWord_6631968 prefixEnd_6631968 3405387269237213628400141 := by
  unfold tailWord_6631968
  simp only [CollatzResearch.WordTrace]
  refine ⟨120943872418760030402320279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161258496558346707203093705 120943872418760030402320279)
  ·
    refine ⟨181415808628140045603480419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120943872418760030402320279 181415808628140045603480419)
    ·
      refine ⟨272123712942210068405220629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181415808628140045603480419 272123712942210068405220629)
      ·
        refine ⟨12755799044166096956494717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272123712942210068405220629 12755799044166096956494717)
        ·
          refine ⟨4783424641562286358685519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12755799044166096956494717 4783424641562286358685519)
          ·
            refine ⟨7175136962343429538028279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4783424641562286358685519 7175136962343429538028279)
            ·
              refine ⟨10762705443515144307042419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7175136962343429538028279 10762705443515144307042419)
              ·
                refine ⟨16144058165272716460563629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10762705443515144307042419 16144058165272716460563629)
                ·
                  refine ⟨6054021811977268672711361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16144058165272716460563629 6054021811977268672711361)
                  ·
                    refine ⟨4540516358982951504533521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6054021811977268672711361 4540516358982951504533521)
                    ·
                      refine ⟨3405387269237213628400141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540516358982951504533521 3405387269237213628400141)
                      ·
                        rfl

theorem cell23_6631968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_6631968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631968 prefixEnd_6631968 := by exact prefixLift 6631968
  have htrace : WordTrace (prefixWord ++ tailWord_6631968) baseStart_6631968 baseEnd_6631968 := by
    simpa [prefixWord, tailWord_6631968, baseEnd_6631968] using wordTrace_append hprefix tailTrace_6631968
  have hstable : (prefixWord ++ tailWord_6631968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631968).length < 2 ^ (prefixWord ++ tailWord_6631968).sum := by decide
  have hdescent : baseEnd_6631968 < baseStart_6631968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631984 : List Nat := [2, 1, 1, 1, 2, 3, 6, 1, 2, 1, 3]
def baseStart_6631984 : Nat := 118140960795 + 6631984 * 2 ^ 59
def prefixEnd_6631984 : Nat := 4983230072969 + 3 ^ 40 * 6631984 * 2
def baseEnd_6631984 : Nat := 3405395484927685565800067

theorem tailTrace_6631984 : CollatzResearch.WordTrace tailWord_6631984 prefixEnd_6631984 3405395484927685565800067 := by
  unfold tailWord_6631984
  simp only [CollatzResearch.WordTrace]
  refine ⟨120944164202731047768611503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161258885603641397024815337 120944164202731047768611503)
  ·
    refine ⟨181416246304096571652917255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120944164202731047768611503 181416246304096571652917255)
    ·
      refine ⟨272124369456144857479375883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181416246304096571652917255 272124369456144857479375883)
      ·
        refine ⟨408186554184217286219063825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272124369456144857479375883 408186554184217286219063825)
        ·
          refine ⟨306139915638162964664297869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408186554184217286219063825 306139915638162964664297869)
          ·
            refine ⟨114802468364311111749111701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306139915638162964664297869 114802468364311111749111701)
            ·
              refine ⟨5381365704577083363239611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114802468364311111749111701 5381365704577083363239611)
              ·
                refine ⟨8072048556865625044859417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381365704577083363239611 8072048556865625044859417)
                ·
                  refine ⟨6054036417649218783644563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8072048556865625044859417 6054036417649218783644563)
                  ·
                    refine ⟨9081054626473828175466845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6054036417649218783644563 9081054626473828175466845)
                    ·
                      refine ⟨3405395484927685565800067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9081054626473828175466845 3405395484927685565800067)
                      ·
                        rfl

theorem cell23_6631984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 1, 2, 1, 3].length) (baseStart_6631984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631984 prefixEnd_6631984 := by exact prefixLift 6631984
  have htrace : WordTrace (prefixWord ++ tailWord_6631984) baseStart_6631984 baseEnd_6631984 := by
    simpa [prefixWord, tailWord_6631984, baseEnd_6631984] using wordTrace_append hprefix tailTrace_6631984
  have hstable : (prefixWord ++ tailWord_6631984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631984).length < 2 ^ (prefixWord ++ tailWord_6631984).sum := by decide
  have hdescent : baseEnd_6631984 < baseStart_6631984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631988 : List Nat := [2, 5, 1, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6631988 : Nat := 118140960795 + 6631988 * 2 ^ 59
def prefixEnd_6631988 : Nat := 4983230072969 + 3 ^ 40 * 6631988 * 2
def baseEnd_6631988 : Nat := 3405397538850303550150049

theorem tailTrace_6631988 : CollatzResearch.WordTrace tailWord_6631988 prefixEnd_6631988 3405397538850303550150049 := by
  unfold tailWord_6631988
  simp only [CollatzResearch.WordTrace]
  refine ⟨120944237148723802110184309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161258982864965069480245745 120944237148723802110184309)
  ·
    refine ⟨11338522232692856447829779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120944237148723802110184309 11338522232692856447829779)
    ·
      refine ⟨17007783349039284671744669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11338522232692856447829779 17007783349039284671744669)
      ·
        refine ⟨6377918755889731751904251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17007783349039284671744669 6377918755889731751904251)
        ·
          refine ⟨9566878133834597627856377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6377918755889731751904251 9566878133834597627856377)
          ·
            refine ⟨7175158600375948220892283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9566878133834597627856377 7175158600375948220892283)
            ·
              refine ⟨10762737900563922331338425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7175158600375948220892283 10762737900563922331338425)
              ·
                refine ⟨8072053425422941748503819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10762737900563922331338425 8072053425422941748503819)
                ·
                  refine ⟨12108080138134412622755729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072053425422941748503819 12108080138134412622755729)
                  ·
                    refine ⟨9081060103600809467066797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12108080138134412622755729 9081060103600809467066797)
                    ·
                      refine ⟨3405397538850303550150049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9081060103600809467066797 3405397538850303550150049)
                      ·
                        rfl

theorem cell23_6631988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6631988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631988 prefixEnd_6631988 := by exact prefixLift 6631988
  have htrace : WordTrace (prefixWord ++ tailWord_6631988) baseStart_6631988 baseEnd_6631988 := by
    simpa [prefixWord, tailWord_6631988, baseEnd_6631988] using wordTrace_append hprefix tailTrace_6631988
  have hstable : (prefixWord ++ tailWord_6631988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631988).length < 2 ^ (prefixWord ++ tailWord_6631988).sum := by decide
  have hdescent : baseEnd_6631988 < baseStart_6631988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6631994 : List Nat := [3, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2]
def baseStart_6631994 : Nat := 118140960795 + 6631994 * 2 ^ 59
def prefixEnd_6631994 : Nat := 4983230072969 + 3 ^ 40 * 6631994 * 2
def baseEnd_6631994 : Nat := 3405400619734230526675021

theorem tailTrace_6631994 : CollatzResearch.WordTrace tailWord_6631994 prefixEnd_6631994 3405400619734230526675021 := by
  unfold tailWord_6631994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60472173283856466811271759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161259128756950578163391357 60472173283856466811271759)
  ·
    refine ⟨90708259925784700216907639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60472173283856466811271759 90708259925784700216907639)
    ·
      refine ⟨136062389888677050325361459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90708259925784700216907639 136062389888677050325361459)
      ·
        refine ⟨204093584833015575488042189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136062389888677050325361459 204093584833015575488042189)
        ·
          refine ⟨76535094312380840808015821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204093584833015575488042189 76535094312380840808015821)
          ·
            refine ⟨28700660367142815303005933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76535094312380840808015821 28700660367142815303005933)
            ·
              refine ⟨10762747637678555738627225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28700660367142815303005933 10762747637678555738627225)
              ·
                refine ⟨8072060728258916803970419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10762747637678555738627225 8072060728258916803970419)
                ·
                  refine ⟨12108091092388375205955629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072060728258916803970419 12108091092388375205955629)
                  ·
                    refine ⟨4540534159645640702233361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12108091092388375205955629 4540534159645640702233361)
                    ·
                      refine ⟨3405400619734230526675021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540534159645640702233361 3405400619734230526675021)
                      ·
                        rfl

theorem cell23_6631994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_6631994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6631994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6631994 prefixEnd_6631994 := by exact prefixLift 6631994
  have htrace : WordTrace (prefixWord ++ tailWord_6631994) baseStart_6631994 baseEnd_6631994 := by
    simpa [prefixWord, tailWord_6631994, baseEnd_6631994] using wordTrace_append hprefix tailTrace_6631994
  have hstable : (prefixWord ++ tailWord_6631994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6631994).length < 2 ^ (prefixWord ++ tailWord_6631994).sum := by decide
  have hdescent : baseEnd_6631994 < baseStart_6631994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6631994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632007 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_6632007 : Nat := 118140960795 + 6632007 * 2 ^ 59
def prefixEnd_6632007 : Nat := 4983230072969 + 3 ^ 40 * 6632007 * 2
def baseEnd_6632007 : Nat := 3405407294982738975812461

theorem tailTrace_6632007 : CollatzResearch.WordTrace tailWord_6632007 prefixEnd_6632007 3405407294982738975812461 := by
  unfold tailWord_6632007
  simp only [CollatzResearch.WordTrace]
  refine ⟨241889167284378770465310275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161259444856252513643540183 241889167284378770465310275)
  ·
    refine ⟨362833750926568155697965413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241889167284378770465310275 362833750926568155697965413)
    ·
      refine ⟨68031328298731529193368515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362833750926568155697965413 68031328298731529193368515)
      ·
        refine ⟨102046992448097293790052773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68031328298731529193368515 102046992448097293790052773)
        ·
          refine ⟨19133811084018242585634895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102046992448097293790052773 19133811084018242585634895)
          ·
            refine ⟨28700716626027363878452343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19133811084018242585634895 28700716626027363878452343)
            ·
              refine ⟨43051074939041045817678515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28700716626027363878452343 43051074939041045817678515)
              ·
                refine ⟨64576612408561568726517773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43051074939041045817678515 64576612408561568726517773)
                ·
                  refine ⟨24216229653210588272444165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64576612408561568726517773 24216229653210588272444165)
                  ·
                    refine ⟨4540543059976985301083281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24216229653210588272444165 4540543059976985301083281)
                    ·
                      refine ⟨3405407294982738975812461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540543059976985301083281 3405407294982738975812461)
                      ·
                        rfl

theorem cell23_6632007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_6632007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632007 prefixEnd_6632007 := by exact prefixLift 6632007
  have htrace : WordTrace (prefixWord ++ tailWord_6632007) baseStart_6632007 baseEnd_6632007 := by
    simpa [prefixWord, tailWord_6632007, baseEnd_6632007] using wordTrace_append hprefix tailTrace_6632007
  have hstable : (prefixWord ++ tailWord_6632007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632007).length < 2 ^ (prefixWord ++ tailWord_6632007).sum := by decide
  have hdescent : baseEnd_6632007 < baseStart_6632007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632010 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_6632010 : Nat := 118140960795 + 6632010 * 2 ^ 59
def prefixEnd_6632010 : Nat := 4983230072969 + 3 ^ 40 * 6632010 * 2
def baseEnd_6632010 : Nat := 3405408835424702464074947

theorem tailTrace_6632010 : CollatzResearch.WordTrace tailWord_6632010 prefixEnd_6632010 3405408835424702464074947 := by
  unfold tailWord_6632010
  simp only [CollatzResearch.WordTrace]
  refine ⟨60472319175841975494417371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161259517802245267985112989 60472319175841975494417371)
  ·
    refine ⟨90708478763762963241626057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60472319175841975494417371 90708478763762963241626057)
    ·
      refine ⟨68031359072822222431219543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90708478763762963241626057 68031359072822222431219543)
      ·
        refine ⟨102047038609233333646829315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68031359072822222431219543 102047038609233333646829315)
        ·
          refine ⟨153070557913850000470243973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102047038609233333646829315 153070557913850000470243973)
          ·
            refine ⟨28700729608846875088170745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153070557913850000470243973 28700729608846875088170745)
            ·
              refine ⟨21525547206635156316128059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28700729608846875088170745 21525547206635156316128059)
              ·
                refine ⟨32288320809952734474192089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21525547206635156316128059 32288320809952734474192089)
                ·
                  refine ⟨24216240607464550855644067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32288320809952734474192089 24216240607464550855644067)
                  ·
                    refine ⟨36324360911196826283466101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24216240607464550855644067 36324360911196826283466101)
                    ·
                      refine ⟨3405408835424702464074947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36324360911196826283466101 3405408835424702464074947)
                      ·
                        rfl

theorem cell23_6632010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_6632010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632010 prefixEnd_6632010 := by exact prefixLift 6632010
  have htrace : WordTrace (prefixWord ++ tailWord_6632010) baseStart_6632010 baseEnd_6632010 := by
    simpa [prefixWord, tailWord_6632010, baseEnd_6632010] using wordTrace_append hprefix tailTrace_6632010
  have hstable : (prefixWord ++ tailWord_6632010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632010).length < 2 ^ (prefixWord ++ tailWord_6632010).sum := by decide
  have hdescent : baseEnd_6632010 < baseStart_6632010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632024 : List Nat := [2, 1, 2, 2, 1, 2, 3, 4, 2, 2, 2]
def baseStart_6632024 : Nat := 118140960795 + 6632024 * 2 ^ 59
def prefixEnd_6632024 : Nat := 4983230072969 + 3 ^ 40 * 6632024 * 2
def baseEnd_6632024 : Nat := 3405416024153865409299883

theorem tailTrace_6632024 : CollatzResearch.WordTrace tailWord_6632024 prefixEnd_6632024 3405416024153865409299883 := by
  unfold tailWord_6632024
  simp only [CollatzResearch.WordTrace]
  refine ⟨120944893662658591184339563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161259858216878121579119417 120944893662658591184339563)
  ·
    refine ⟨181417340493987886776509345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120944893662658591184339563 181417340493987886776509345)
    ·
      refine ⟨136063005370490915082382009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181417340493987886776509345 136063005370490915082382009)
      ·
        refine ⟨102047254027868186311786507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136063005370490915082382009 102047254027868186311786507)
        ·
          refine ⟨153070881041802279467679761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102047254027868186311786507 153070881041802279467679761)
          ·
            refine ⟨114803160781351709600759821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153070881041802279467679761 114803160781351709600759821)
            ·
              refine ⟨43051185293006891100284933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114803160781351709600759821 43051185293006891100284933)
              ·
                refine ⟨8072097242438792081303425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43051185293006891100284933 8072097242438792081303425)
                ·
                  refine ⟨6054072931829094060977569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8072097242438792081303425 6054072931829094060977569)
                  ·
                    refine ⟨4540554698871820545733177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6054072931829094060977569 4540554698871820545733177)
                    ·
                      refine ⟨3405416024153865409299883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540554698871820545733177 3405416024153865409299883)
                      ·
                        rfl

theorem cell23_6632024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_6632024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632024 prefixEnd_6632024 := by exact prefixLift 6632024
  have htrace : WordTrace (prefixWord ++ tailWord_6632024) baseStart_6632024 baseEnd_6632024 := by
    simpa [prefixWord, tailWord_6632024, baseEnd_6632024] using wordTrace_append hprefix tailTrace_6632024
  have hstable : (prefixWord ++ tailWord_6632024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632024).length < 2 ^ (prefixWord ++ tailWord_6632024).sum := by decide
  have hdescent : baseEnd_6632024 < baseStart_6632024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632034 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 2, 6]
def baseStart_6632034 : Nat := 118140960795 + 6632034 * 2 ^ 59
def prefixEnd_6632034 : Nat := 4983230072969 + 3 ^ 40 * 6632034 * 2
def baseEnd_6632034 : Nat := 1135140386320136790058279

theorem tailTrace_6632034 : CollatzResearch.WordTrace tailWord_6632034 prefixEnd_6632034 1135140386320136790058279 := by
  unfold tailWord_6632034
  simp only [CollatzResearch.WordTrace]
  refine ⟨60472538013820238519135789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161260101370187302717695437 60472538013820238519135789)
  ·
    refine ⟨22677201755182589444675921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60472538013820238519135789 22677201755182589444675921)
    ·
      refine ⟨17007901316386942083506941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22677201755182589444675921 17007901316386942083506941)
      ·
        refine ⟨6377962993645103281315103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17007901316386942083506941 6377962993645103281315103)
        ·
          refine ⟨9566944490467654921972655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6377962993645103281315103 9566944490467654921972655)
          ·
            refine ⟨14350416735701482382958983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9566944490467654921972655 14350416735701482382958983)
            ·
              refine ⟨21525625103552223574438475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14350416735701482382958983 21525625103552223574438475)
              ·
                refine ⟨32288437655328335361657713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21525625103552223574438475 32288437655328335361657713)
                ·
                  refine ⟨24216328241496251521243285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32288437655328335361657713 24216328241496251521243285)
                  ·
                    refine ⟨1135140386320136790058279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24216328241496251521243285 1135140386320136790058279)
                    ·
                      rfl

theorem cell23_6632034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_6632034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632034 prefixEnd_6632034 := by exact prefixLift 6632034
  have htrace : WordTrace (prefixWord ++ tailWord_6632034) baseStart_6632034 baseEnd_6632034 := by
    simpa [prefixWord, tailWord_6632034, baseEnd_6632034] using wordTrace_append hprefix tailTrace_6632034
  have hstable : (prefixWord ++ tailWord_6632034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632034).length < 2 ^ (prefixWord ++ tailWord_6632034).sum := by decide
  have hdescent : baseEnd_6632034 < baseStart_6632034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632037 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_6632037 : Nat := 118140960795 + 6632037 * 2 ^ 59
def prefixEnd_6632037 : Nat := 4983230072969 + 3 ^ 40 * 6632037 * 2
def baseEnd_6632037 : Nat := 3405422699402373858437323

theorem tailTrace_6632037 : CollatzResearch.WordTrace tailWord_6632037 prefixEnd_6632037 3405422699402373858437323 := by
  unfold tailWord_6632037
  simp only [CollatzResearch.WordTrace]
  refine ⟨241890261474270085588902365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161260174316180057059268243 241890261474270085588902365)
  ·
    refine ⟨90708848052851282095838387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241890261474270085588902365 90708848052851282095838387)
    ·
      refine ⟨136063272079276923143757581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90708848052851282095838387 136063272079276923143757581)
      ·
        refine ⟨51023727029728846178909093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136063272079276923143757581 51023727029728846178909093)
        ·
          refine ⟨9566948818074158658545455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51023727029728846178909093 9566948818074158658545455)
          ·
            refine ⟨14350423227111237987818183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9566948818074158658545455 14350423227111237987818183)
            ·
              refine ⟨21525634840666856981727275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14350423227111237987818183 21525634840666856981727275)
              ·
                refine ⟨32288452261000285472590913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21525634840666856981727275 32288452261000285472590913)
                ·
                  refine ⟨24216339195750214104443185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32288452261000285472590913 24216339195750214104443185)
                  ·
                    refine ⟨18162254396812660578332389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24216339195750214104443185 18162254396812660578332389)
                    ·
                      refine ⟨3405422699402373858437323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18162254396812660578332389 3405422699402373858437323)
                      ·
                        rfl

theorem cell23_6632037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_6632037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632037 prefixEnd_6632037 := by exact prefixLift 6632037
  have htrace : WordTrace (prefixWord ++ tailWord_6632037) baseStart_6632037 baseEnd_6632037 := by
    simpa [prefixWord, tailWord_6632037, baseEnd_6632037] using wordTrace_append hprefix tailTrace_6632037
  have hstable : (prefixWord ++ tailWord_6632037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632037).length < 2 ^ (prefixWord ++ tailWord_6632037).sum := by decide
  have hdescent : baseEnd_6632037 < baseStart_6632037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632184 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 1, 5]
def baseStart_6632184 : Nat := 118140960795 + 6632184 * 2 ^ 59
def prefixEnd_6632184 : Nat := 4983230072969 + 3 ^ 40 * 6632184 * 2
def baseEnd_6632184 : Nat := 1135166060352861594433049

theorem tailTrace_6632184 : CollatzResearch.WordTrace tailWord_6632184 prefixEnd_6632184 1135166060352861594433049 := by
  unfold tailWord_6632184
  simp only [CollatzResearch.WordTrace]
  refine ⟨120947811502368764847251803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161263748669825019796335737 120947811502368764847251803)
  ·
    refine ⟨181421717253553147270877705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120947811502368764847251803 181421717253553147270877705)
    ·
      refine ⟨136066287940164860453158279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181421717253553147270877705 136066287940164860453158279)
      ·
        refine ⟨204099431910247290679737419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136066287940164860453158279 204099431910247290679737419)
        ·
          refine ⟨306149147865370936019606129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204099431910247290679737419 306149147865370936019606129)
          ·
            refine ⟨229611860899028202014704597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306149147865370936019606129 229611860899028202014704597)
            ·
              refine ⟨5381527989820973484719639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 229611860899028202014704597 5381527989820973484719639)
              ·
                refine ⟨8072291984731460227079459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381527989820973484719639 8072291984731460227079459)
                ·
                  refine ⟨12108437977097190340619189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072291984731460227079459 12108437977097190340619189)
                  ·
                    refine ⟨1135166060352861594433049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12108437977097190340619189 1135166060352861594433049)
                    ·
                      rfl

theorem cell23_6632184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_6632184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632184 prefixEnd_6632184 := by exact prefixLift 6632184
  have htrace : WordTrace (prefixWord ++ tailWord_6632184) baseStart_6632184 baseEnd_6632184 := by
    simpa [prefixWord, tailWord_6632184, baseEnd_6632184] using wordTrace_append hprefix tailTrace_6632184
  have hstable : (prefixWord ++ tailWord_6632184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632184).length < 2 ^ (prefixWord ++ tailWord_6632184).sum := by decide
  have hdescent : baseEnd_6632184 < baseStart_6632184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632187 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 4, 6, 2]
def baseStart_6632187 : Nat := 118140960795 + 6632187 * 2 ^ 59
def prefixEnd_6632187 : Nat := 4983230072969 + 3 ^ 40 * 6632187 * 2
def baseEnd_6632187 : Nat := 3405499721500548271561633

theorem tailTrace_6632187 : CollatzResearch.WordTrace tailWord_6632187 prefixEnd_6632187 3405499721500548271561633 := by
  unfold tailWord_6632187
  simp only [CollatzResearch.WordTrace]
  refine ⟨241895732423726661206862815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161263821615817774137908543 241895732423726661206862815)
  ·
    refine ⟨362843598635589991810294223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241895732423726661206862815 362843598635589991810294223)
    ·
      refine ⟨544265397953384987715441335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362843598635589991810294223 544265397953384987715441335)
      ·
        refine ⟨816398096930077481573162003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544265397953384987715441335 816398096930077481573162003)
        ·
          refine ⟨1224597145395116222359743005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816398096930077481573162003 1224597145395116222359743005)
          ·
            refine ⟨459223929523168583384903627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1224597145395116222359743005 459223929523168583384903627)
            ·
              refine ⟨688835894284752875077355441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459223929523168583384903627 688835894284752875077355441)
              ·
                refine ⟨516626920713564656308016581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 688835894284752875077355441 516626920713564656308016581)
                ·
                  refine ⟨96867547633793373057753109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 516626920713564656308016581 96867547633793373057753109)
                  ·
                    refine ⟨4540666295334064362082177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96867547633793373057753109 4540666295334064362082177)
                    ·
                      refine ⟨3405499721500548271561633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540666295334064362082177 3405499721500548271561633)
                      ·
                        rfl

theorem cell23_6632187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 6, 2].length) (baseStart_6632187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632187 prefixEnd_6632187 := by exact prefixLift 6632187
  have htrace : WordTrace (prefixWord ++ tailWord_6632187) baseStart_6632187 baseEnd_6632187 := by
    simpa [prefixWord, tailWord_6632187, baseEnd_6632187] using wordTrace_append hprefix tailTrace_6632187
  have hstable : (prefixWord ++ tailWord_6632187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632187).length < 2 ^ (prefixWord ++ tailWord_6632187).sum := by decide
  have hdescent : baseEnd_6632187 < baseStart_6632187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632197 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_6632197 : Nat := 118140960795 + 6632197 * 2 ^ 59
def prefixEnd_6632197 : Nat := 4983230072969 + 3 ^ 40 * 6632197 * 2
def baseEnd_6632197 : Nat := 1135168285435697744145529

theorem tailTrace_6632197 : CollatzResearch.WordTrace tailWord_6632197 prefixEnd_6632197 1135168285435697744145529 := by
  unfold tailWord_6632197
  simp only [CollatzResearch.WordTrace]
  refine ⟨241896097153690432914726845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161264064769126955276484563 241896097153690432914726845)
  ·
    refine ⟨90711036432633912343022567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241896097153690432914726845 90711036432633912343022567)
    ·
      refine ⟨136066554648950868514533851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90711036432633912343022567 136066554648950868514533851)
      ·
        refine ⟨204099831973426302771800777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136066554648950868514533851 204099831973426302771800777)
        ·
          refine ⟨153074873980069727078850583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204099831973426302771800777 153074873980069727078850583)
          ·
            refine ⟨229612310970104590618275875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153074873980069727078850583 229612310970104590618275875)
            ·
              refine ⟨344418466455156885927413813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229612310970104590618275875 344418466455156885927413813)
              ·
                refine ⟨32289231230170958055695045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 344418466455156885927413813 32289231230170958055695045)
                ·
                  refine ⟨6054230855657054635442821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32289231230170958055695045 6054230855657054635442821)
                  ·
                    refine ⟨1135168285435697744145529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6054230855657054635442821 1135168285435697744145529)
                    ·
                      rfl

theorem cell23_6632197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_6632197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632197 prefixEnd_6632197 := by exact prefixLift 6632197
  have htrace : WordTrace (prefixWord ++ tailWord_6632197) baseStart_6632197 baseEnd_6632197 := by
    simpa [prefixWord, tailWord_6632197, baseEnd_6632197] using wordTrace_append hprefix tailTrace_6632197
  have hstable : (prefixWord ++ tailWord_6632197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632197).length < 2 ^ (prefixWord ++ tailWord_6632197).sum := by decide
  have hdescent : baseEnd_6632197 < baseStart_6632197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632207 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 3]
def baseStart_6632207 : Nat := 118140960795 + 6632207 * 2 ^ 59
def prefixEnd_6632207 : Nat := 4983230072969 + 3 ^ 40 * 6632207 * 2
def baseEnd_6632207 : Nat := 3405509991113638193311541

theorem tailTrace_6632207 : CollatzResearch.WordTrace tailWord_6632207 prefixEnd_6632207 3405509991113638193311541 := by
  unfold tailWord_6632207
  simp only [CollatzResearch.WordTrace]
  refine ⟨241896461883654204622590875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161264307922436136415060583 241896461883654204622590875)
  ·
    refine ⟨362844692825481306933886313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241896461883654204622590875 362844692825481306933886313)
    ·
      refine ⟨272133519619110980200414735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362844692825481306933886313 272133519619110980200414735)
      ·
        refine ⟨408200279428666470300622103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272133519619110980200414735 408200279428666470300622103)
        ·
          refine ⟨612300419142999705450933155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408200279428666470300622103 612300419142999705450933155)
          ·
            refine ⟨918450628714499558176399733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612300419142999705450933155 918450628714499558176399733)
            ·
              refine ⟨86104746441984333579037475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 918450628714499558176399733 86104746441984333579037475)
              ·
                refine ⟨129157119662976500368556213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86104746441984333579037475 129157119662976500368556213)
                ·
                  refine ⟨12108479968404046909552145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129157119662976500368556213 12108479968404046909552145)
                  ·
                    refine ⟨9081359976303035182164109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12108479968404046909552145 9081359976303035182164109)
                    ·
                      refine ⟨3405509991113638193311541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9081359976303035182164109 3405509991113638193311541)
                      ·
                        rfl

theorem cell23_6632207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_6632207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632207 prefixEnd_6632207 := by exact prefixLift 6632207
  have htrace : WordTrace (prefixWord ++ tailWord_6632207) baseStart_6632207 baseEnd_6632207 := by
    simpa [prefixWord, tailWord_6632207, baseEnd_6632207] using wordTrace_append hprefix tailTrace_6632207
  have hstable : (prefixWord ++ tailWord_6632207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632207).length < 2 ^ (prefixWord ++ tailWord_6632207).sum := by decide
  have hdescent : baseEnd_6632207 < baseStart_6632207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632224 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3]
def baseStart_6632224 : Nat := 118140960795 + 6632224 * 2 ^ 59
def prefixEnd_6632224 : Nat := 4983230072969 + 3 ^ 40 * 6632224 * 2
def baseEnd_6632224 : Nat := 3405518720284764626798963

theorem tailTrace_6632224 : CollatzResearch.WordTrace tailWord_6632224 prefixEnd_6632224 3405518720284764626798963 := by
  unfold tailWord_6632224
  simp only [CollatzResearch.WordTrace]
  refine ⟨120948540962296308262979863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161264721283061744350639817 120948540962296308262979863)
  ·
    refine ⟨181422811443444462394469795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120948540962296308262979863 181422811443444462394469795)
    ·
      refine ⟨272134217165166693591704693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181422811443444462394469795 272134217165166693591704693)
      ·
        refine ⟨25512582859234377524222315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 272134217165166693591704693 25512582859234377524222315)
        ·
          refine ⟨38268874288851566286333473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25512582859234377524222315 38268874288851566286333473)
          ·
            refine ⟨28701655716638674714750105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38268874288851566286333473 28701655716638674714750105)
            ·
              refine ⟨21526241787479006036062579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28701655716638674714750105 21526241787479006036062579)
              ·
                refine ⟨32289362681218509054093869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21526241787479006036062579 32289362681218509054093869)
                ·
                  refine ⟨12108511005456940895285201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32289362681218509054093869 12108511005456940895285201)
                  ·
                    refine ⟨9081383254092705671463901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12108511005456940895285201 9081383254092705671463901)
                    ·
                      refine ⟨3405518720284764626798963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9081383254092705671463901 3405518720284764626798963)
                      ·
                        rfl

theorem cell23_6632224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_6632224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632224 prefixEnd_6632224 := by exact prefixLift 6632224
  have htrace : WordTrace (prefixWord ++ tailWord_6632224) baseStart_6632224 baseEnd_6632224 := by
    simpa [prefixWord, tailWord_6632224, baseEnd_6632224] using wordTrace_append hprefix tailTrace_6632224
  have hstable : (prefixWord ++ tailWord_6632224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632224).length < 2 ^ (prefixWord ++ tailWord_6632224).sum := by decide
  have hdescent : baseEnd_6632224 < baseStart_6632224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632238 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_6632238 : Nat := 118140960795 + 6632238 * 2 ^ 59
def prefixEnd_6632238 : Nat := 4983230072969 + 3 ^ 40 * 6632238 * 2
def baseEnd_6632238 : Nat := 3405525909013927572023899

theorem tailTrace_6632238 : CollatzResearch.WordTrace tailWord_6632238 prefixEnd_6632238 3405525909013927572023899 := by
  unfold tailWord_6632238
  simp only [CollatzResearch.WordTrace]
  refine ⟨30237199068317737114621171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161265061697694597944646245 30237199068317737114621171)
  ·
    refine ⟨45355798602476605671931757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30237199068317737114621171 45355798602476605671931757)
    ·
      refine ⟨17008424475928727126974409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45355798602476605671931757 17008424475928727126974409)
      ·
        refine ⟨12756318356946545345230807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17008424475928727126974409 12756318356946545345230807)
        ·
          refine ⟨19134477535419818017846211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12756318356946545345230807 19134477535419818017846211)
          ·
            refine ⟨28701716303129727026769317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19134477535419818017846211 28701716303129727026769317)
            ·
              refine ⟨5381571806836823817519247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28701716303129727026769317 5381571806836823817519247)
              ·
                refine ⟨8072357710255235726278871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381571806836823817519247 8072357710255235726278871)
                ·
                  refine ⟨12108536565382853589418307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072357710255235726278871 12108536565382853589418307)
                  ·
                    refine ⟨18162804848074280384127461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12108536565382853589418307 18162804848074280384127461)
                    ·
                      refine ⟨3405525909013927572023899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18162804848074280384127461 3405525909013927572023899)
                      ·
                        rfl

theorem cell23_6632238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_6632238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632238 prefixEnd_6632238 := by exact prefixLift 6632238
  have htrace : WordTrace (prefixWord ++ tailWord_6632238) baseStart_6632238 baseEnd_6632238 := by
    simpa [prefixWord, tailWord_6632238, baseEnd_6632238] using wordTrace_append hprefix tailTrace_6632238
  have hstable : (prefixWord ++ tailWord_6632238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632238).length < 2 ^ (prefixWord ++ tailWord_6632238).sum := by decide
  have hdescent : baseEnd_6632238 < baseStart_6632238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632244 : List Nat := [2, 5, 1, 1, 3, 1, 10]
def baseStart_6632244 : Nat := 118140960795 + 6632244 * 2 ^ 59
def prefixEnd_6632244 : Nat := 4983230072969 + 3 ^ 40 * 6632244 * 2
def baseEnd_6632244 : Nat := 42043567776516722821591

theorem tailTrace_6632244 : CollatzResearch.WordTrace tailWord_6632244 prefixEnd_6632244 42043567776516722821591 := by
  unfold tailWord_6632244
  simp only [CollatzResearch.WordTrace]
  refine ⟨120948905692260079970843893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161265207589680106627791857 120948905692260079970843893)
  ·
    refine ⟨11338959908649382497266615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120948905692260079970843893 11338959908649382497266615)
    ·
      refine ⟨17008439862974073745899923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11338959908649382497266615 17008439862974073745899923)
      ·
        refine ⟨25512659794461110618849885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17008439862974073745899923 25512659794461110618849885)
        ·
          refine ⟨9567247422922916482068707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25512659794461110618849885 9567247422922916482068707)
          ·
            refine ⟨14350871134384374723103061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9567247422922916482068707 14350871134384374723103061)
            ·
              refine ⟨42043567776516722821591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14350871134384374723103061 42043567776516722821591)
              ·
                rfl

theorem cell23_6632244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 10].length) (baseStart_6632244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632244 prefixEnd_6632244 := by exact prefixLift 6632244
  have htrace : WordTrace (prefixWord ++ tailWord_6632244) baseStart_6632244 baseEnd_6632244 := by
    simpa [prefixWord, tailWord_6632244, baseEnd_6632244] using wordTrace_append hprefix tailTrace_6632244
  have hstable : (prefixWord ++ tailWord_6632244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632244).length < 2 ^ (prefixWord ++ tailWord_6632244).sum := by decide
  have hdescent : baseEnd_6632244 < baseStart_6632244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632281 : List Nat := [1, 2, 1, 2, 2, 4, 1, 4, 1, 3, 2]
def baseStart_6632281 : Nat := 118140960795 + 6632281 * 2 ^ 59
def prefixEnd_6632281 : Nat := 4983230072969 + 3 ^ 40 * 6632281 * 2
def baseEnd_6632281 : Nat := 3405547988682070903786201

theorem tailTrace_6632281 : CollatzResearch.WordTrace tailWord_6632281 prefixEnd_6632281 3405547988682070903786201 := by
  unfold tailWord_6632281
  simp only [CollatzResearch.WordTrace]
  refine ⟨241899160885386115260784697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161266107256924076840523131 241899160885386115260784697)
  ·
    refine ⟨181424370664039586445588523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241899160885386115260784697 181424370664039586445588523)
    ·
      refine ⟨272136555996059379668382785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181424370664039586445588523 272136555996059379668382785)
      ·
        refine ⟨204102416997044534751287089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272136555996059379668382785 204102416997044534751287089)
        ·
          refine ⟨153076812747783401063465317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204102416997044534751287089 153076812747783401063465317)
          ·
            refine ⟨28701902390209387699399747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153076812747783401063465317 28701902390209387699399747)
            ·
              refine ⟨43052853585314081549099621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28701902390209387699399747 43052853585314081549099621)
              ·
                refine ⟨8072410047246390290456179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43052853585314081549099621 8072410047246390290456179)
                ·
                  refine ⟨12108615070869585435684269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072410047246390290456179 12108615070869585435684269)
                  ·
                    refine ⟨4540730651576094538381601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12108615070869585435684269 4540730651576094538381601)
                    ·
                      refine ⟨3405547988682070903786201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540730651576094538381601 3405547988682070903786201)
                      ·
                        rfl

theorem cell23_6632281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_6632281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632281 prefixEnd_6632281 := by exact prefixLift 6632281
  have htrace : WordTrace (prefixWord ++ tailWord_6632281) baseStart_6632281 baseEnd_6632281 := by
    simpa [prefixWord, tailWord_6632281, baseEnd_6632281] using wordTrace_append hprefix tailTrace_6632281
  have hstable : (prefixWord ++ tailWord_6632281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632281).length < 2 ^ (prefixWord ++ tailWord_6632281).sum := by decide
  have hdescent : baseEnd_6632281 < baseStart_6632281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632284 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_6632284 : Nat := 118140960795 + 6632284 * 2 ^ 59
def prefixEnd_6632284 : Nat := 4983230072969 + 3 ^ 40 * 6632284 * 2
def baseEnd_6632284 : Nat := 3405549529124034392048687

theorem tailTrace_6632284 : CollatzResearch.WordTrace tailWord_6632284 prefixEnd_6632284 3405549529124034392048687 := by
  unfold tailWord_6632284
  simp only [CollatzResearch.WordTrace]
  refine ⟨120949635152187623386571953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161266180202916831182095937 120949635152187623386571953)
  ·
    refine ⟨90712226364140717539928965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120949635152187623386571953 90712226364140717539928965)
    ·
      refine ⟨17008542443276384538736681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90712226364140717539928965 17008542443276384538736681)
      ·
        refine ⟨12756406832457288404052511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17008542443276384538736681 12756406832457288404052511)
        ·
          refine ⟨19134610248685932606078767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12756406832457288404052511 19134610248685932606078767)
          ·
            refine ⟨28701915373028898909118151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19134610248685932606078767 28701915373028898909118151)
            ·
              refine ⟨43052873059543348363677227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28701915373028898909118151 43052873059543348363677227)
              ·
                refine ⟨64579309589315022545515841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43052873059543348363677227 64579309589315022545515841)
                ·
                  refine ⟨48434482191986266909136881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64579309589315022545515841 48434482191986266909136881)
                  ·
                    refine ⟨36325861643989700181852661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48434482191986266909136881 36325861643989700181852661)
                    ·
                      refine ⟨3405549529124034392048687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36325861643989700181852661 3405549529124034392048687)
                      ·
                        rfl

theorem cell23_6632284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_6632284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632284 prefixEnd_6632284 := by exact prefixLift 6632284
  have htrace : WordTrace (prefixWord ++ tailWord_6632284) baseStart_6632284 baseEnd_6632284 := by
    simpa [prefixWord, tailWord_6632284, baseEnd_6632284] using wordTrace_append hprefix tailTrace_6632284
  have hstable : (prefixWord ++ tailWord_6632284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632284).length < 2 ^ (prefixWord ++ tailWord_6632284).sum := by decide
  have hdescent : baseEnd_6632284 < baseStart_6632284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632297 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 3]
def baseStart_6632297 : Nat := 118140960795 + 6632297 * 2 ^ 59
def prefixEnd_6632297 : Nat := 4983230072969 + 3 ^ 40 * 6632297 * 2
def baseEnd_6632297 : Nat := 3405556204372542841186127

theorem tailTrace_6632297 : CollatzResearch.WordTrace tailWord_6632297 prefixEnd_6632297 3405556204372542841186127 := by
  unfold tailWord_6632297
  simp only [CollatzResearch.WordTrace]
  refine ⟨241899744453328149993367145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161266496302218766662244763 241899744453328149993367145)
  ·
    refine ⟨181424808339996112495025359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241899744453328149993367145 181424808339996112495025359)
    ·
      refine ⟨272137212509994168742538039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181424808339996112495025359 272137212509994168742538039)
      ·
        refine ⟨408205818764991253113807059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272137212509994168742538039 408205818764991253113807059)
        ·
          refine ⟨612308728147486879670710589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408205818764991253113807059 612308728147486879670710589)
          ·
            refine ⟨229615773055307579876516471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 612308728147486879670710589 229615773055307579876516471)
            ·
              refine ⟨344423659582961369814774707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229615773055307579876516471 344423659582961369814774707)
              ·
                refine ⟨516635489374442054722162061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344423659582961369814774707 516635489374442054722162061)
                ·
                  refine ⟨193738308515415770520810773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 516635489374442054722162061 193738308515415770520810773)
                  ·
                    refine ⟨9081483211660114243163005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 193738308515415770520810773 9081483211660114243163005)
                    ·
                      refine ⟨3405556204372542841186127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9081483211660114243163005 3405556204372542841186127)
                      ·
                        rfl

theorem cell23_6632297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_6632297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632297 prefixEnd_6632297 := by exact prefixLift 6632297
  have htrace : WordTrace (prefixWord ++ tailWord_6632297) baseStart_6632297 baseEnd_6632297 := by
    simpa [prefixWord, tailWord_6632297, baseEnd_6632297] using wordTrace_append hprefix tailTrace_6632297
  have hstable : (prefixWord ++ tailWord_6632297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632297).length < 2 ^ (prefixWord ++ tailWord_6632297).sum := by decide
  have hdescent : baseEnd_6632297 < baseStart_6632297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632307 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4]
def baseStart_6632307 : Nat := 118140960795 + 6632307 * 2 ^ 59
def prefixEnd_6632307 : Nat := 4983230072969 + 3 ^ 40 * 6632307 * 2
def baseEnd_6632307 : Nat := 3405561339179087802061081

theorem tailTrace_6632307 : CollatzResearch.WordTrace tailWord_6632307 prefixEnd_6632307 3405561339179087802061081 := by
  unfold tailWord_6632307
  simp only [CollatzResearch.WordTrace]
  refine ⟨241900109183291921701231175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161266739455527947800820783 241900109183291921701231175)
  ·
    refine ⟨362850163774937882551846763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241900109183291921701231175 362850163774937882551846763)
    ·
      refine ⟨544275245662406823827770145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362850163774937882551846763 544275245662406823827770145)
      ·
        refine ⟨408206434246805117870827609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544275245662406823827770145 408206434246805117870827609)
        ·
          refine ⟨306154825685103838403120707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408206434246805117870827609 306154825685103838403120707)
          ·
            refine ⟨459232238527655757604681061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306154825685103838403120707 459232238527655757604681061)
            ·
              refine ⟨86106044723935454550877699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 459232238527655757604681061 86106044723935454550877699)
              ·
                refine ⟨129159067085903181826316549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86106044723935454550877699 129159067085903181826316549)
                ·
                  refine ⟨24217325078606846592434353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129159067085903181826316549 24217325078606846592434353)
                  ·
                    refine ⟨18162993808955134944325765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24217325078606846592434353 18162993808955134944325765)
                    ·
                      refine ⟨3405561339179087802061081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18162993808955134944325765 3405561339179087802061081)
                      ·
                        rfl

theorem cell23_6632307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_6632307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632307 prefixEnd_6632307 := by exact prefixLift 6632307
  have htrace : WordTrace (prefixWord ++ tailWord_6632307) baseStart_6632307 baseEnd_6632307 := by
    simpa [prefixWord, tailWord_6632307, baseEnd_6632307] using wordTrace_append hprefix tailTrace_6632307
  have hstable : (prefixWord ++ tailWord_6632307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632307).length < 2 ^ (prefixWord ++ tailWord_6632307).sum := by decide
  have hdescent : baseEnd_6632307 < baseStart_6632307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632322 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6632322 : Nat := 118140960795 + 6632322 * 2 ^ 59
def prefixEnd_6632322 : Nat := 4983230072969 + 3 ^ 40 * 6632322 * 2
def baseEnd_6632322 : Nat := 3405569041388905243373513

theorem tailTrace_6632322 : CollatzResearch.WordTrace tailWord_6632322 prefixEnd_6632322 3405569041388905243373513 := by
  unfold tailWord_6632322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60475164069559394815756805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161267104185491719508684813 60475164069559394815756805)
  ·
    refine ⟨11339093263042386527954401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60475164069559394815756805 11339093263042386527954401)
    ·
      refine ⟨8504319947281789895965801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11339093263042386527954401 8504319947281789895965801)
      ·
        refine ⟨6378239960461342421974351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8504319947281789895965801 6378239960461342421974351)
        ·
          refine ⟨9567359940692013632961527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378239960461342421974351 9567359940692013632961527)
          ·
            refine ⟨14351039911038020449442291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9567359940692013632961527 14351039911038020449442291)
            ·
              refine ⟨21526559866557030674163437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14351039911038020449442291 21526559866557030674163437)
              ·
                refine ⟨8072459949958886502811289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21526559866557030674163437 8072459949958886502811289)
                ·
                  refine ⟨6054344962469164877108467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8072459949958886502811289 6054344962469164877108467)
                  ·
                    refine ⟨9081517443703747315662701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6054344962469164877108467 9081517443703747315662701)
                    ·
                      refine ⟨3405569041388905243373513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9081517443703747315662701 3405569041388905243373513)
                      ·
                        rfl

theorem cell23_6632322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6632322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632322 prefixEnd_6632322 := by exact prefixLift 6632322
  have htrace : WordTrace (prefixWord ++ tailWord_6632322) baseStart_6632322 baseEnd_6632322 := by
    simpa [prefixWord, tailWord_6632322, baseEnd_6632322] using wordTrace_append hprefix tailTrace_6632322
  have hstable : (prefixWord ++ tailWord_6632322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632322).length < 2 ^ (prefixWord ++ tailWord_6632322).sum := by decide
  have hdescent : baseEnd_6632322 < baseStart_6632322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632387 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5]
def baseStart_6632387 : Nat := 118140960795 + 6632387 * 2 ^ 59
def prefixEnd_6632387 : Nat := 4983230072969 + 3 ^ 40 * 6632387 * 2
def baseEnd_6632387 : Nat := 3405602417631447489060713

theorem tailTrace_6632387 : CollatzResearch.WordTrace tailWord_6632387 prefixEnd_6632387 3405602417631447489060713 := by
  unfold tailWord_6632387
  simp only [CollatzResearch.WordTrace]
  refine ⟨241903027023002095364143415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161268684682001396909428943 241903027023002095364143415)
  ·
    refine ⟨362854540534503143046215123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241903027023002095364143415 362854540534503143046215123)
    ·
      refine ⟨544281810801754714569322685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362854540534503143046215123 544281810801754714569322685)
      ·
        refine ⟨204105679050658017963496007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544281810801754714569322685 204105679050658017963496007)
        ·
          refine ⟨306158518575987026945244011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204105679050658017963496007 306158518575987026945244011)
          ·
            refine ⟨459237777863980540417866017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306158518575987026945244011 459237777863980540417866017)
            ·
              refine ⟨344428333397985405313399513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 459237777863980540417866017 344428333397985405313399513)
              ·
                refine ⟨258321250048489053985049635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344428333397985405313399513 258321250048489053985049635)
                ·
                  refine ⟨387481875072733580977574453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258321250048489053985049635 387481875072733580977574453)
                  ·
                    refine ⟨36326425788068773216647605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387481875072733580977574453 36326425788068773216647605)
                    ·
                      refine ⟨3405602417631447489060713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36326425788068773216647605 3405602417631447489060713)
                      ·
                        rfl

theorem cell23_6632387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_6632387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632387 prefixEnd_6632387 := by exact prefixLift 6632387
  have htrace : WordTrace (prefixWord ++ tailWord_6632387) baseStart_6632387 baseEnd_6632387 := by
    simpa [prefixWord, tailWord_6632387, baseEnd_6632387] using wordTrace_append hprefix tailTrace_6632387
  have hstable : (prefixWord ++ tailWord_6632387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632387).length < 2 ^ (prefixWord ++ tailWord_6632387).sum := by decide
  have hdescent : baseEnd_6632387 < baseStart_6632387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632441 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 6]
def baseStart_6632441 : Nat := 118140960795 + 6632441 * 2 ^ 59
def prefixEnd_6632441 : Nat := 4983230072969 + 3 ^ 40 * 6632441 * 2
def baseEnd_6632441 : Nat := 378403349509643364198385

theorem tailTrace_6632441 : CollatzResearch.WordTrace tailWord_6632441 prefixEnd_6632441 378403349509643364198385 := by
  unfold tailWord_6632441
  simp only [CollatzResearch.WordTrace]
  refine ⟨241904996564806462586609177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161269997709870975057739451 241904996564806462586609177)
  ·
    refine ⟨181428747423604846939956883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241904996564806462586609177 181428747423604846939956883)
    ·
      refine ⟨272143121135407270409935325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181428747423604846939956883 272143121135407270409935325)
      ·
        refine ⟨102053670425777726403725747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272143121135407270409935325 102053670425777726403725747)
        ·
          refine ⟨153080505638666589605588621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102053670425777726403725747 153080505638666589605588621)
          ·
            refine ⟨57405189614499971102095733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153080505638666589605588621 57405189614499971102095733)
            ·
              refine ⟨5381736526359372290821475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57405189614499971102095733 5381736526359372290821475)
              ·
                refine ⟨8072604789539058436232213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381736526359372290821475 8072604789539058436232213)
                ·
                  refine ⟨378403349509643364198385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8072604789539058436232213 378403349509643364198385)
                  ·
                    rfl

theorem cell23_6632441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 6].length) (baseStart_6632441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632441 prefixEnd_6632441 := by exact prefixLift 6632441
  have htrace : WordTrace (prefixWord ++ tailWord_6632441) baseStart_6632441 baseEnd_6632441 := by
    simpa [prefixWord, tailWord_6632441, baseEnd_6632441] using wordTrace_append hprefix tailTrace_6632441
  have hstable : (prefixWord ++ tailWord_6632441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632441).length < 2 ^ (prefixWord ++ tailWord_6632441).sum := by decide
  have hdescent : baseEnd_6632441 < baseStart_6632441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632508 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_6632508 : Nat := 118140960795 + 6632508 * 2 ^ 59
def prefixEnd_6632508 : Nat := 4983230072969 + 3 ^ 40 * 6632508 * 2
def baseEnd_6632508 : Nat := 3405664548790641515647657

theorem tailTrace_6632508 : CollatzResearch.WordTrace tailWord_6632508 prefixEnd_6632508 3405664548790641515647657 := by
  unfold tailWord_6632508
  simp only [CollatzResearch.WordTrace]
  refine ⟨120953720127781866514649089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161271626837042488686198785 120953720127781866514649089)
  ·
    refine ⟨90715290095836399885986817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120953720127781866514649089 90715290095836399885986817)
    ·
      refine ⟨68036467571877299914490113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90715290095836399885986817 68036467571877299914490113)
      ·
        refine ⟨51027350678907974935867585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68036467571877299914490113 51027350678907974935867585)
        ·
          refine ⟨38270513009180981201900689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51027350678907974935867585 38270513009180981201900689)
          ·
            refine ⟨28702884756885735901425517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38270513009180981201900689 28702884756885735901425517)
            ·
              refine ⟨10763581783832150963034569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28702884756885735901425517 10763581783832150963034569)
              ·
                refine ⟨8072686337874113222275927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10763581783832150963034569 8072686337874113222275927)
                ·
                  refine ⟨12109029506811169833413891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072686337874113222275927 12109029506811169833413891)
                  ·
                    refine ⟨18163544260216754750120837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12109029506811169833413891 18163544260216754750120837)
                    ·
                      refine ⟨3405664548790641515647657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18163544260216754750120837 3405664548790641515647657)
                      ·
                        rfl

theorem cell23_6632508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_6632508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632508 prefixEnd_6632508 := by exact prefixLift 6632508
  have htrace : WordTrace (prefixWord ++ tailWord_6632508) baseStart_6632508 baseEnd_6632508 := by
    simpa [prefixWord, tailWord_6632508, baseEnd_6632508] using wordTrace_append hprefix tailTrace_6632508
  have hstable : (prefixWord ++ tailWord_6632508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632508).length < 2 ^ (prefixWord ++ tailWord_6632508).sum := by decide
  have hdescent : baseEnd_6632508 < baseStart_6632508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632518 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_6632518 : Nat := 118140960795 + 6632518 * 2 ^ 59
def prefixEnd_6632518 : Nat := 4983230072969 + 3 ^ 40 * 6632518 * 2
def baseEnd_6632518 : Nat := 1135223227865728825507537

theorem tailTrace_6632518 : CollatzResearch.WordTrace tailWord_6632518 prefixEnd_6632518 1135223227865728825507537 := by
  unfold tailWord_6632518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559618905797734523036319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161271869990351669824774805 7559618905797734523036319)
  ·
    refine ⟨11339428358696601784554479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7559618905797734523036319 11339428358696601784554479)
    ·
      refine ⟨17009142538044902676831719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11339428358696601784554479 17009142538044902676831719)
      ·
        refine ⟨25513713807067354015247579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17009142538044902676831719 25513713807067354015247579)
        ·
          refine ⟨38270570710601031022871369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25513713807067354015247579 38270570710601031022871369)
          ·
            refine ⟨28702928032950773267153527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38270570710601031022871369 28702928032950773267153527)
            ·
              refine ⟨43054392049426159900730291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28702928032950773267153527 43054392049426159900730291)
              ·
                refine ⟨64581588074139239851095437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43054392049426159900730291 64581588074139239851095437)
                ·
                  refine ⟨24218095527802214944160789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64581588074139239851095437 24218095527802214944160789)
                  ·
                    refine ⟨1135223227865728825507537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24218095527802214944160789 1135223227865728825507537)
                    ·
                      rfl

theorem cell23_6632518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_6632518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632518 prefixEnd_6632518 := by exact prefixLift 6632518
  have htrace : WordTrace (prefixWord ++ tailWord_6632518) baseStart_6632518 baseEnd_6632518 := by
    simpa [prefixWord, tailWord_6632518, baseEnd_6632518] using wordTrace_append hprefix tailTrace_6632518
  have hstable : (prefixWord ++ tailWord_6632518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632518).length < 2 ^ (prefixWord ++ tailWord_6632518).sum := by decide
  have hdescent : baseEnd_6632518 < baseStart_6632518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632544 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 9]
def baseStart_6632544 : Nat := 118140960795 + 6632544 * 2 ^ 59
def prefixEnd_6632544 : Nat := 4983230072969 + 3 ^ 40 * 6632544 * 2
def baseEnd_6632544 : Nat := 1135227678031401124932497

theorem tailTrace_6632544 : CollatzResearch.WordTrace tailWord_6632544 prefixEnd_6632544 1135227678031401124932497 := by
  unfold tailWord_6632544
  simp only [CollatzResearch.WordTrace]
  refine ⟨120954376641716655588804343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161272502188955540785072457 120954376641716655588804343)
  ·
    refine ⟨181431564962574983383206515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120954376641716655588804343 181431564962574983383206515)
    ·
      refine ⟨272147347443862475074809773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181431564962574983383206515 272147347443862475074809773)
      ·
        refine ⟨102055255291448428153053665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272147347443862475074809773 102055255291448428153053665)
        ·
          refine ⟨76541441468586321114790249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102055255291448428153053665 76541441468586321114790249)
          ·
            refine ⟨57406081101439740836092687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76541441468586321114790249 57406081101439740836092687)
            ·
              refine ⟨86109121652159611254139031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57406081101439740836092687 86109121652159611254139031)
              ·
                refine ⟨129163682478239416881208547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86109121652159611254139031 129163682478239416881208547)
                ·
                  refine ⟨193745523717359125321812821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129163682478239416881208547 193745523717359125321812821)
                  ·
                    refine ⟨1135227678031401124932497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193745523717359125321812821 1135227678031401124932497)
                    ·
                      rfl

theorem cell23_6632544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_6632544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632544 prefixEnd_6632544 := by exact prefixLift 6632544
  have htrace : WordTrace (prefixWord ++ tailWord_6632544) baseStart_6632544 baseEnd_6632544 := by
    simpa [prefixWord, tailWord_6632544, baseEnd_6632544] using wordTrace_append hprefix tailTrace_6632544
  have hstable : (prefixWord ++ tailWord_6632544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632544).length < 2 ^ (prefixWord ++ tailWord_6632544).sum := by decide
  have hdescent : baseEnd_6632544 < baseStart_6632544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632558 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_6632558 : Nat := 118140960795 + 6632558 * 2 ^ 59
def prefixEnd_6632558 : Nat := 4983230072969 + 3 ^ 40 * 6632558 * 2
def baseEnd_6632558 : Nat := 3405690222823366320022427

theorem tailTrace_6632558 : CollatzResearch.WordTrace tailWord_6632558 prefixEnd_6632558 3405690222823366320022427 := by
  unfold tailWord_6632558
  simp only [CollatzResearch.WordTrace]
  refine ⟨30238657988172823946077291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161272842603588394379078885 30238657988172823946077291)
  ·
    refine ⟨45357986982259235919115937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30238657988172823946077291 45357986982259235919115937)
    ·
      refine ⟨34018490236694426939336953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45357986982259235919115937 34018490236694426939336953)
      ·
        refine ⟨25513867677520820204502715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34018490236694426939336953 25513867677520820204502715)
        ·
          refine ⟨38270801516281230306754073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25513867677520820204502715 38270801516281230306754073)
          ·
            refine ⟨28703101137210922730065555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38270801516281230306754073 28703101137210922730065555)
            ·
              refine ⟨43054651705816384095098333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28703101137210922730065555 43054651705816384095098333)
              ·
                refine ⟨16145494389681144035661875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43054651705816384095098333 16145494389681144035661875)
                ·
                  refine ⟨24218241584521716053492813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16145494389681144035661875 24218241584521716053492813)
                  ·
                    refine ⟨9081840594195643520059805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24218241584521716053492813 9081840594195643520059805)
                    ·
                      refine ⟨3405690222823366320022427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9081840594195643520059805 3405690222823366320022427)
                      ·
                        rfl

theorem cell23_6632558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_6632558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632558 prefixEnd_6632558 := by exact prefixLift 6632558
  have htrace : WordTrace (prefixWord ++ tailWord_6632558) baseStart_6632558 baseEnd_6632558 := by
    simpa [prefixWord, tailWord_6632558, baseEnd_6632558] using wordTrace_append hprefix tailTrace_6632558
  have hstable : (prefixWord ++ tailWord_6632558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632558).length < 2 ^ (prefixWord ++ tailWord_6632558).sum := by decide
  have hdescent : baseEnd_6632558 < baseStart_6632558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632565 : List Nat := [1, 3, 4, 3, 1, 1, 3, 7]
def baseStart_6632565 : Nat := 118140960795 + 6632565 * 2 ^ 59
def prefixEnd_6632565 : Nat := 4983230072969 + 3 ^ 40 * 6632565 * 2
def baseEnd_6632565 : Nat := 126136808043998066393885

theorem tailTrace_6632565 : CollatzResearch.WordTrace tailWord_6632565 prefixEnd_6632565 126136808043998066393885 := by
  unfold tailWord_6632565
  simp only [CollatzResearch.WordTrace]
  refine ⟨241909519216357231764123149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161273012810904821176082099 241909519216357231764123149)
  ·
    refine ⟨90716069706133961911546181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241909519216357231764123149 90716069706133961911546181)
    ·
      refine ⟨17009263069900117858414909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90716069706133961911546181 17009263069900117858414909)
      ·
        refine ⟨6378473651212544196905591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17009263069900117858414909 6378473651212544196905591)
        ·
          refine ⟨9567710476818816295358387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378473651212544196905591 9567710476818816295358387)
          ·
            refine ⟨14351565715228224443037581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9567710476818816295358387 14351565715228224443037581)
            ·
              refine ⟨5381837143210584166139093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14351565715228224443037581 5381837143210584166139093)
              ·
                refine ⟨126136808043998066393885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5381837143210584166139093 126136808043998066393885)
                ·
                  rfl

theorem cell23_6632565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 7].length) (baseStart_6632565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632565 prefixEnd_6632565 := by exact prefixLift 6632565
  have htrace : WordTrace (prefixWord ++ tailWord_6632565) baseStart_6632565 baseEnd_6632565 := by
    simpa [prefixWord, tailWord_6632565, baseEnd_6632565] using wordTrace_append hprefix tailTrace_6632565
  have hstable : (prefixWord ++ tailWord_6632565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632565).length < 2 ^ (prefixWord ++ tailWord_6632565).sum := by decide
  have hdescent : baseEnd_6632565 < baseStart_6632565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632568 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 3, 3, 2]
def baseStart_6632568 : Nat := 118140960795 + 6632568 * 2 ^ 59
def prefixEnd_6632568 : Nat := 4983230072969 + 3 ^ 40 * 6632568 * 2
def baseEnd_6632568 : Nat := 3405695357629911280897381

theorem tailTrace_6632568 : CollatzResearch.WordTrace tailWord_6632568 prefixEnd_6632568 3405695357629911280897381 := by
  unfold tailWord_6632568
  simp only [CollatzResearch.WordTrace]
  refine ⟨120954814317673181638241179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161273085756897575517654905 120954814317673181638241179)
  ·
    refine ⟨181432221476509772457361769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120954814317673181638241179 181432221476509772457361769)
    ·
      refine ⟨136074166107382329343021327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181432221476509772457361769 136074166107382329343021327)
      ·
        refine ⟨204111249161073494014531991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136074166107382329343021327 204111249161073494014531991)
        ·
          refine ⟨306166873741610241021797987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204111249161073494014531991 306166873741610241021797987)
          ·
            refine ⟨459250310612415361532696981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306166873741610241021797987 459250310612415361532696981)
            ·
              refine ⟨21527358309956970071845171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 459250310612415361532696981 21527358309956970071845171)
              ·
                refine ⟨32291037464935455107767757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21527358309956970071845171 32291037464935455107767757)
                ·
                  refine ⟨12109139049350795665412909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32291037464935455107767757 12109139049350795665412909)
                  ·
                    refine ⟨4540927143506548374529841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12109139049350795665412909 4540927143506548374529841)
                    ·
                      refine ⟨3405695357629911280897381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540927143506548374529841 3405695357629911280897381)
                      ·
                        rfl

theorem cell23_6632568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_6632568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632568 prefixEnd_6632568 := by exact prefixLift 6632568
  have htrace : WordTrace (prefixWord ++ tailWord_6632568) baseStart_6632568 baseEnd_6632568 := by
    simpa [prefixWord, tailWord_6632568, baseEnd_6632568] using wordTrace_append hprefix tailTrace_6632568
  have hstable : (prefixWord ++ tailWord_6632568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632568).length < 2 ^ (prefixWord ++ tailWord_6632568).sum := by decide
  have hdescent : baseEnd_6632568 < baseStart_6632568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632585 : List Nat := [1, 2, 1, 1, 4, 4, 1, 3, 1, 3, 2]
def baseStart_6632585 : Nat := 118140960795 + 6632585 * 2 ^ 59
def prefixEnd_6632585 : Nat := 4983230072969 + 3 ^ 40 * 6632585 * 2
def baseEnd_6632585 : Nat := 3405704086801037714384803

theorem tailTrace_6632585 : CollatzResearch.WordTrace tailWord_6632585 prefixEnd_6632585 3405704086801037714384803 := by
  unfold tailWord_6632585
  simp only [CollatzResearch.WordTrace]
  refine ⟨241910248676284775179851209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161273499117523183453234139 241910248676284775179851209)
  ·
    refine ⟨181432686507213581384888407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241910248676284775179851209 181432686507213581384888407)
    ·
      refine ⟨272149029760820372077332611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181432686507213581384888407 272149029760820372077332611)
      ·
        refine ⟨408223544641230558115998917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272149029760820372077332611 408223544641230558115998917)
        ·
          refine ⟨76541914620230729646749797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 408223544641230558115998917 76541914620230729646749797)
          ·
            refine ⟨14351608991293261808765587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76541914620230729646749797 14351608991293261808765587)
            ·
              refine ⟨21527413486939892713148381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14351608991293261808765587 21527413486939892713148381)
              ·
                refine ⟨8072780057602459767430643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21527413486939892713148381 8072780057602459767430643)
                ·
                  refine ⟨12109170086403689651145965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8072780057602459767430643 12109170086403689651145965)
                  ·
                    refine ⟨4540938782401383619179737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12109170086403689651145965 4540938782401383619179737)
                    ·
                      refine ⟨3405704086801037714384803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4540938782401383619179737 3405704086801037714384803)
                      ·
                        rfl

theorem cell23_6632585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 3, 2].length) (baseStart_6632585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632585 prefixEnd_6632585 := by exact prefixLift 6632585
  have htrace : WordTrace (prefixWord ++ tailWord_6632585) baseStart_6632585 baseEnd_6632585 := by
    simpa [prefixWord, tailWord_6632585, baseEnd_6632585] using wordTrace_append hprefix tailTrace_6632585
  have hstable : (prefixWord ++ tailWord_6632585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632585).length < 2 ^ (prefixWord ++ tailWord_6632585).sum := by decide
  have hdescent : baseEnd_6632585 < baseStart_6632585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632671 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_6632671 : Nat := 118140960795 + 6632671 * 2 ^ 59
def prefixEnd_6632671 : Nat := 4983230072969 + 3 ^ 40 * 6632671 * 2
def baseEnd_6632671 : Nat := 3405748246137324377909407

theorem tailTrace_6632671 : CollatzResearch.WordTrace tailWord_6632671 prefixEnd_6632671 3405748246137324377909407 := by
  unfold tailWord_6632671
  simp only [CollatzResearch.WordTrace]
  refine ⟨241913385353973211867481867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161275590235982141244987911 241913385353973211867481867)
  ·
    refine ⟨362870078030959817801222801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241913385353973211867481867 362870078030959817801222801)
    ·
      refine ⟨272152558523219863350917101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362870078030959817801222801 272152558523219863350917101)
      ·
        refine ⟨102057209446207448756593913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272152558523219863350917101 102057209446207448756593913)
        ·
          refine ⟨76542907084655586567445435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102057209446207448756593913 76542907084655586567445435)
          ·
            refine ⟨114814360626983379851168153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76542907084655586567445435 114814360626983379851168153)
            ·
              refine ⟨86110770470237534888376115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114814360626983379851168153 86110770470237534888376115)
              ·
                refine ⟨129166155705356302332564173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86110770470237534888376115 129166155705356302332564173)
                ·
                  refine ⟨48437308389508613374711565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129166155705356302332564173 48437308389508613374711565)
                  ·
                    refine ⟨18163990646065730015516837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48437308389508613374711565 18163990646065730015516837)
                    ·
                      refine ⟨3405748246137324377909407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18163990646065730015516837 3405748246137324377909407)
                      ·
                        rfl

theorem cell23_6632671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_6632671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632671 prefixEnd_6632671 := by exact prefixLift 6632671
  have htrace : WordTrace (prefixWord ++ tailWord_6632671) baseStart_6632671 baseEnd_6632671 := by
    simpa [prefixWord, tailWord_6632671, baseEnd_6632671] using wordTrace_append hprefix tailTrace_6632671
  have hstable : (prefixWord ++ tailWord_6632671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632671).length < 2 ^ (prefixWord ++ tailWord_6632671).sum := by decide
  have hdescent : baseEnd_6632671 < baseStart_6632671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632685 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_6632685 : Nat := 118140960795 + 6632685 * 2 ^ 59
def prefixEnd_6632685 : Nat := 4983230072969 + 3 ^ 40 * 6632685 * 2
def baseEnd_6632685 : Nat := 1135251811622162441044781

theorem tailTrace_6632685 : CollatzResearch.WordTrace tailWord_6632685 prefixEnd_6632685 1135251811622162441044781 := by
  unfold tailWord_6632685
  simp only [CollatzResearch.WordTrace]
  refine ⟨241913895975922492258491509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161275930650614994838994339 241913895975922492258491509)
  ·
    refine ⟨22679427747742733649233579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241913895975922492258491509 22679427747742733649233579)
    ·
      refine ⟨34019141621614100473850369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22679427747742733649233579 34019141621614100473850369)
      ·
        refine ⟨25514356216210575355387777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34019141621614100473850369 25514356216210575355387777)
        ·
          refine ⟨19135767162157931516540833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25514356216210575355387777 19135767162157931516540833)
          ·
            refine ⟨14351825371618448637405625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19135767162157931516540833 14351825371618448637405625)
            ·
              refine ⟨10763869028713836478054219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14351825371618448637405625 10763869028713836478054219)
              ·
                refine ⟨16145803543070754717081329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10763869028713836478054219 16145803543070754717081329)
                ·
                  refine ⟨12109352657303066037810997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16145803543070754717081329 12109352657303066037810997)
                  ·
                    refine ⟨1135251811622162441044781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12109352657303066037810997 1135251811622162441044781)
                    ·
                      rfl

theorem cell23_6632685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_6632685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632685 prefixEnd_6632685 := by exact prefixLift 6632685
  have htrace : WordTrace (prefixWord ++ tailWord_6632685) baseStart_6632685 baseEnd_6632685 := by
    simpa [prefixWord, tailWord_6632685, baseEnd_6632685] using wordTrace_append hprefix tailTrace_6632685
  have hstable : (prefixWord ++ tailWord_6632685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632685).length < 2 ^ (prefixWord ++ tailWord_6632685).sum := by decide
  have hdescent : baseEnd_6632685 < baseStart_6632685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632688 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 6, 4, 2]
def baseStart_6632688 : Nat := 118140960795 + 6632688 * 2 ^ 59
def prefixEnd_6632688 : Nat := 4983230072969 + 3 ^ 40 * 6632688 * 2
def baseEnd_6632688 : Nat := 3405756975308450811396829

theorem tailTrace_6632688 : CollatzResearch.WordTrace tailWord_6632688 prefixEnd_6632688 3405756975308450811396829 := by
  unfold tailWord_6632688
  simp only [CollatzResearch.WordTrace]
  refine ⟨120957002697455811885425359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161276003596607749180567145 120957002697455811885425359)
  ·
    refine ⟨181435504046183717828138039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120957002697455811885425359 181435504046183717828138039)
    ·
      refine ⟨272153256069275576742207059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181435504046183717828138039 272153256069275576742207059)
      ·
        refine ⟨408229884103913365113310589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272153256069275576742207059 408229884103913365113310589)
        ·
          refine ⟨153086206538967511917491471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408229884103913365113310589 153086206538967511917491471)
          ·
            refine ⟨229629309808451267876237207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153086206538967511917491471 229629309808451267876237207)
            ·
              refine ⟨344443964712676901814355811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229629309808451267876237207 344443964712676901814355811)
              ·
                refine ⟨516665947069015352721533717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344443964712676901814355811 516665947069015352721533717)
                ·
                  refine ⟨24218716268860094658821893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 516665947069015352721533717 24218716268860094658821893)
                  ·
                    refine ⟨4541009300411267748529105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24218716268860094658821893 4541009300411267748529105)
                    ·
                      refine ⟨3405756975308450811396829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541009300411267748529105 3405756975308450811396829)
                      ·
                        rfl

theorem cell23_6632688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 6, 4, 2].length) (baseStart_6632688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632688 prefixEnd_6632688 := by exact prefixLift 6632688
  have htrace : WordTrace (prefixWord ++ tailWord_6632688) baseStart_6632688 baseEnd_6632688 := by
    simpa [prefixWord, tailWord_6632688, baseEnd_6632688] using wordTrace_append hprefix tailTrace_6632688
  have hstable : (prefixWord ++ tailWord_6632688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632688).length < 2 ^ (prefixWord ++ tailWord_6632688).sum := by decide
  have hdescent : baseEnd_6632688 < baseStart_6632688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632706 : List Nat := [3, 4, 1, 1, 4, 1, 2, 2, 5]
def baseStart_6632706 : Nat := 118140960795 + 6632706 * 2 ^ 59
def prefixEnd_6632706 : Nat := 4983230072969 + 3 ^ 40 * 6632706 * 2
def baseEnd_6632706 : Nat := 378418468662247971219083

theorem tailTrace_6632706 : CollatzResearch.WordTrace tailWord_6632706 prefixEnd_6632706 378418468662247971219083 := by
  unfold tailWord_6632706
  simp only [CollatzResearch.WordTrace]
  refine ⟨60478665477211603211251493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161276441272564275230003981 60478665477211603211251493)
  ·
    refine ⟨11339749776977175602109655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60478665477211603211251493 11339749776977175602109655)
    ·
      refine ⟨17009624665465763403164483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11339749776977175602109655 17009624665465763403164483)
      ·
        refine ⟨25514436998198645104746725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17009624665465763403164483 25514436998198645104746725)
        ·
          refine ⟨4783956937162245957140011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25514436998198645104746725 4783956937162245957140011)
          ·
            refine ⟨7175935405743368935710017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4783956937162245957140011 7175935405743368935710017)
            ·
              refine ⟨5381951554307526701782513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7175935405743368935710017 5381951554307526701782513)
              ·
                refine ⟨4036463665730645026336885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5381951554307526701782513 4036463665730645026336885)
                ·
                  refine ⟨378418468662247971219083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4036463665730645026336885 378418468662247971219083)
                  ·
                    rfl

theorem cell23_6632706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_6632706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632706 prefixEnd_6632706 := by exact prefixLift 6632706
  have htrace : WordTrace (prefixWord ++ tailWord_6632706) baseStart_6632706 baseEnd_6632706 := by
    simpa [prefixWord, tailWord_6632706, baseEnd_6632706] using wordTrace_append hprefix tailTrace_6632706
  have hstable : (prefixWord ++ tailWord_6632706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632706).length < 2 ^ (prefixWord ++ tailWord_6632706).sum := by decide
  have hdescent : baseEnd_6632706 < baseStart_6632706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632728 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 6]
def baseStart_6632728 : Nat := 118140960795 + 6632728 * 2 ^ 59
def prefixEnd_6632728 : Nat := 4983230072969 + 3 ^ 40 * 6632728 * 2
def baseEnd_6632728 : Nat := 378419723837181183877405

theorem tailTrace_6632728 : CollatzResearch.WordTrace tailWord_6632728 prefixEnd_6632728 378419723837181183877405 := by
  unfold tailWord_6632728
  simp only [CollatzResearch.WordTrace]
  refine ⟨120957732157383355301153419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161276976209844473734871225 120957732157383355301153419)
  ·
    refine ⟨181436598236075032951730129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120957732157383355301153419 181436598236075032951730129)
    ·
      refine ⟨136077448677056274713797597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181436598236075032951730129 136077448677056274713797597)
      ·
        refine ⟨51029043253896103017674099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136077448677056274713797597 51029043253896103017674099)
        ·
          refine ⟨76543564880844154526511149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51029043253896103017674099 76543564880844154526511149)
          ·
            refine ⟨28703836830316557947441681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76543564880844154526511149 28703836830316557947441681)
            ·
              refine ⟨21527877622737418460581261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28703836830316557947441681 21527877622737418460581261)
              ·
                refine ⟨8072954108526531922717973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21527877622737418460581261 8072954108526531922717973)
                ·
                  refine ⟨378419723837181183877405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8072954108526531922717973 378419723837181183877405)
                  ·
                    rfl

theorem cell23_6632728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 6].length) (baseStart_6632728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632728 prefixEnd_6632728 := by exact prefixLift 6632728
  have htrace : WordTrace (prefixWord ++ tailWord_6632728) baseStart_6632728 baseEnd_6632728 := by
    simpa [prefixWord, tailWord_6632728, baseEnd_6632728] using wordTrace_append hprefix tailTrace_6632728
  have hstable : (prefixWord ++ tailWord_6632728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632728).length < 2 ^ (prefixWord ++ tailWord_6632728).sum := by decide
  have hdescent : baseEnd_6632728 < baseStart_6632728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632749 : List Nat := [1, 5, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6632749 : Nat := 118140960795 + 6632749 * 2 ^ 59
def prefixEnd_6632749 : Nat := 4983230072969 + 3 ^ 40 * 6632749 * 2
def baseEnd_6632749 : Nat := 1135262765876125024244683

theorem tailTrace_6632749 : CollatzResearch.WordTrace tailWord_6632749 prefixEnd_6632749 1135262765876125024244683 := by
  unfold tailWord_6632749
  simp only [CollatzResearch.WordTrace]
  refine ⟨241916230247690631188821301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161277486831793754125880867 241916230247690631188821301)
  ·
    refine ⟨22679646585720996673951997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241916230247690631188821301 22679646585720996673951997)
    ·
      refine ⟨8504867469645373752731999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22679646585720996673951997 8504867469645373752731999)
      ·
        refine ⟨12757301204468060629097999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8504867469645373752731999 12757301204468060629097999)
        ·
          refine ⟨19135951806702090943646999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12757301204468060629097999 19135951806702090943646999)
          ·
            refine ⟨28703927710053136415470499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19135951806702090943646999 28703927710053136415470499)
            ·
              refine ⟨43055891565079704623205749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28703927710053136415470499 43055891565079704623205749)
              ·
                refine ⟨4036489834226222308425539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43055891565079704623205749 4036489834226222308425539)
                ·
                  refine ⟨6054734751339333462638309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4036489834226222308425539 6054734751339333462638309)
                  ·
                    refine ⟨1135262765876125024244683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6054734751339333462638309 1135262765876125024244683)
                    ·
                      rfl

theorem cell23_6632749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6632749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632749 prefixEnd_6632749 := by exact prefixLift 6632749
  have htrace : WordTrace (prefixWord ++ tailWord_6632749) baseStart_6632749 baseEnd_6632749 := by
    simpa [prefixWord, tailWord_6632749, baseEnd_6632749] using wordTrace_append hprefix tailTrace_6632749
  have hstable : (prefixWord ++ tailWord_6632749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632749).length < 2 ^ (prefixWord ++ tailWord_6632749).sum := by decide
  have hdescent : baseEnd_6632749 < baseStart_6632749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632751 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_6632751 : Nat := 118140960795 + 6632751 * 2 ^ 59
def prefixEnd_6632751 : Nat := 4983230072969 + 3 ^ 40 * 6632751 * 2
def baseEnd_6632751 : Nat := 3405789324589684064909039

theorem tailTrace_6632751 : CollatzResearch.WordTrace tailWord_6632751 prefixEnd_6632751 3405789324589684064909039 := by
  unfold tailWord_6632751
  simp only [CollatzResearch.WordTrace]
  refine ⟨241916303193683385530394107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161277535462455590353596071 241916303193683385530394107)
  ·
    refine ⟨362874454790525078295591161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241916303193683385530394107 362874454790525078295591161)
    ·
      refine ⟨272155841092893808721693371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362874454790525078295591161 272155841092893808721693371)
      ·
        refine ⟨408233761639340713082540057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272155841092893808721693371 408233761639340713082540057)
        ·
          refine ⟨306175321229505534811905043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408233761639340713082540057 306175321229505534811905043)
          ·
            refine ⟨459262981844258302217857565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306175321229505534811905043 459262981844258302217857565)
            ·
              refine ⟨172223618191596863331696587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459262981844258302217857565 172223618191596863331696587)
              ·
                refine ⟨258335427287395294997544881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172223618191596863331696587 258335427287395294997544881)
                ·
                  refine ⟨193751570465546471248158661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258335427287395294997544881 193751570465546471248158661)
                  ·
                    refine ⟨36328419462289963359029749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193751570465546471248158661 36328419462289963359029749)
                    ·
                      refine ⟨3405789324589684064909039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36328419462289963359029749 3405789324589684064909039)
                      ·
                        rfl

theorem cell23_6632751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_6632751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632751 prefixEnd_6632751 := by exact prefixLift 6632751
  have htrace : WordTrace (prefixWord ++ tailWord_6632751) baseStart_6632751 baseEnd_6632751 := by
    simpa [prefixWord, tailWord_6632751, baseEnd_6632751] using wordTrace_append hprefix tailTrace_6632751
  have hstable : (prefixWord ++ tailWord_6632751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632751).length < 2 ^ (prefixWord ++ tailWord_6632751).sum := by decide
  have hdescent : baseEnd_6632751 < baseStart_6632751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632778 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_6632778 : Nat := 118140960795 + 6632778 * 2 ^ 59
def prefixEnd_6632778 : Nat := 4983230072969 + 3 ^ 40 * 6632778 * 2
def baseEnd_6632778 : Nat := 3405803188567355459271415

theorem tailTrace_6632778 : CollatzResearch.WordTrace tailWord_6632778 prefixEnd_6632778 3405803188567355459271415 := by
  unfold tailWord_6632778
  simp only [CollatzResearch.WordTrace]
  refine ⟨60479321991146392285406747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161278191976390379427751325 60479321991146392285406747)
  ·
    refine ⟨90718982986719588428110121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60479321991146392285406747 90718982986719588428110121)
    ·
      refine ⟨68039237240039691321082591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90718982986719588428110121 68039237240039691321082591)
      ·
        refine ⟨102058855860059536981623887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68039237240039691321082591 102058855860059536981623887)
        ·
          refine ⟨153088283790089305472435831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102058855860059536981623887 153088283790089305472435831)
          ·
            refine ⟨229632425685133958208653747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153088283790089305472435831 229632425685133958208653747)
            ·
              refine ⟨344448638527700937312980621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229632425685133958208653747 344448638527700937312980621)
              ·
                refine ⟨129168239447887851492367733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344448638527700937312980621 129168239447887851492367733)
                ·
                  refine ⟨12109522448239486077409475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129168239447887851492367733 12109522448239486077409475)
                  ·
                    refine ⟨18164283672359229116114213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12109522448239486077409475 18164283672359229116114213)
                    ·
                      refine ⟨3405803188567355459271415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18164283672359229116114213 3405803188567355459271415)
                      ·
                        rfl

theorem cell23_6632778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_6632778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632778 prefixEnd_6632778 := by exact prefixLift 6632778
  have htrace : WordTrace (prefixWord ++ tailWord_6632778) baseStart_6632778 baseEnd_6632778 := by
    simpa [prefixWord, tailWord_6632778, baseEnd_6632778] using wordTrace_append hprefix tailTrace_6632778
  have hstable : (prefixWord ++ tailWord_6632778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632778).length < 2 ^ (prefixWord ++ tailWord_6632778).sum := by decide
  have hdescent : baseEnd_6632778 < baseStart_6632778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632815 : List Nat := [1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 3]
def baseStart_6632815 : Nat := 118140960795 + 6632815 * 2 ^ 59
def prefixEnd_6632815 : Nat := 4983230072969 + 3 ^ 40 * 6632815 * 2
def baseEnd_6632815 : Nat := 3405822187351571814508745

theorem tailTrace_6632815 : CollatzResearch.WordTrace tailWord_6632815 prefixEnd_6632815 3405822187351571814508745 := by
  unfold tailWord_6632815
  simp only [CollatzResearch.WordTrace]
  refine ⟨241918637465451524460723899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161279091643634349640482599 241918637465451524460723899)
  ·
    refine ⟨362877956198177286691085849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241918637465451524460723899 362877956198177286691085849)
    ·
      refine ⟨272158467148632965018314387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362877956198177286691085849 272158467148632965018314387)
      ·
        refine ⟨408237700722949447527471581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272158467148632965018314387 408237700722949447527471581)
        ·
          refine ⟨153089137771106042822801843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408237700722949447527471581 153089137771106042822801843)
          ·
            refine ⟨229633706656659064234202765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153089137771106042822801843 229633706656659064234202765)
            ·
              refine ⟨86112639996247149087826037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229633706656659064234202765 86112639996247149087826037)
              ·
                refine ⟨8073059999648170226983691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86112639996247149087826037 8073059999648170226983691)
                ·
                  refine ⟨12109589999472255340475537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8073059999648170226983691 12109589999472255340475537)
                  ·
                    refine ⟨9082192499604191505356653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12109589999472255340475537 9082192499604191505356653)
                    ·
                      refine ⟨3405822187351571814508745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9082192499604191505356653 3405822187351571814508745)
                      ·
                        rfl

theorem cell23_6632815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_6632815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632815 prefixEnd_6632815 := by exact prefixLift 6632815
  have htrace : WordTrace (prefixWord ++ tailWord_6632815) baseStart_6632815 baseEnd_6632815 := by
    simpa [prefixWord, tailWord_6632815, baseEnd_6632815] using wordTrace_append hprefix tailTrace_6632815
  have hstable : (prefixWord ++ tailWord_6632815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632815).length < 2 ^ (prefixWord ++ tailWord_6632815).sum := by decide
  have hdescent : baseEnd_6632815 < baseStart_6632815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632839 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 2, 4]
def baseStart_6632839 : Nat := 118140960795 + 6632839 * 2 ^ 59
def prefixEnd_6632839 : Nat := 4983230072969 + 3 ^ 40 * 6632839 * 2
def baseEnd_6632839 : Nat := 1135278170295759906869545

theorem tailTrace_6632839 : CollatzResearch.WordTrace tailWord_6632839 prefixEnd_6632839 1135278170295759906869545 := by
  unfold tailWord_6632839
  simp only [CollatzResearch.WordTrace]
  refine ⟨241919512817364576559597571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161279675211576384373065047 241919512817364576559597571)
  ·
    refine ⟨362879269226046864839396357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241919512817364576559597571 362879269226046864839396357)
    ·
      refine ⟨68039862979883787157386817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 362879269226046864839396357 68039862979883787157386817)
      ·
        refine ⟨51029897234912840368040113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68039862979883787157386817 51029897234912840368040113)
        ·
          refine ⟨38272422926184630276030085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51029897234912840368040113 38272422926184630276030085)
          ·
            refine ⟨7176079298659618176755641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38272422926184630276030085 7176079298659618176755641)
            ·
              refine ⟨5382059473994713632566731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7176079298659618176755641 5382059473994713632566731)
              ·
                refine ⟨8073089210992070448850097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382059473994713632566731 8073089210992070448850097)
                ·
                  refine ⟨6054816908244052836637573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8073089210992070448850097 6054816908244052836637573)
                  ·
                    refine ⟨1135278170295759906869545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6054816908244052836637573 1135278170295759906869545)
                    ·
                      rfl

theorem cell23_6632839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_6632839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632839 prefixEnd_6632839 := by exact prefixLift 6632839
  have htrace : WordTrace (prefixWord ++ tailWord_6632839) baseStart_6632839 baseEnd_6632839 := by
    simpa [prefixWord, tailWord_6632839, baseEnd_6632839] using wordTrace_append hprefix tailTrace_6632839
  have hstable : (prefixWord ++ tailWord_6632839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632839).length < 2 ^ (prefixWord ++ tailWord_6632839).sum := by decide
  have hdescent : baseEnd_6632839 < baseStart_6632839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632846 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6632846 : Nat := 118140960795 + 6632846 * 2 ^ 59
def prefixEnd_6632846 : Nat := 4983230072969 + 3 ^ 40 * 6632846 * 2
def baseEnd_6632846 : Nat := 3405838105251861193221103

theorem tailTrace_6632846 : CollatzResearch.WordTrace tailWord_6632846 prefixEnd_6632846 3405838105251861193221103 := by
  unfold tailWord_6632846
  simp only [CollatzResearch.WordTrace]
  refine ⟨30239971016042402094387799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161279845418892811170068261 30239971016042402094387799)
  ·
    refine ⟨45359956524063603141581699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30239971016042402094387799 45359956524063603141581699)
    ·
      refine ⟨68039934786095404712372549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45359956524063603141581699 68039934786095404712372549)
      ·
        refine ⟨12757487772392888383569853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68039934786095404712372549 12757487772392888383569853)
        ·
          refine ⟨4784057914647333143838695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12757487772392888383569853 4784057914647333143838695)
          ·
            refine ⟨7176086871970999715758043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784057914647333143838695 7176086871970999715758043)
            ·
              refine ⟨10764130307956499573637065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7176086871970999715758043 10764130307956499573637065)
              ·
                refine ⟨8073097730967374680227799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10764130307956499573637065 8073097730967374680227799)
                ·
                  refine ⟨12109646596451062020341699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8073097730967374680227799 12109646596451062020341699)
                  ·
                    refine ⟨18164469894676593030512549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12109646596451062020341699 18164469894676593030512549)
                    ·
                      refine ⟨3405838105251861193221103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18164469894676593030512549 3405838105251861193221103)
                      ·
                        rfl

theorem cell23_6632846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6632846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632846 prefixEnd_6632846 := by exact prefixLift 6632846
  have htrace : WordTrace (prefixWord ++ tailWord_6632846) baseStart_6632846 baseEnd_6632846 := by
    simpa [prefixWord, tailWord_6632846, baseEnd_6632846] using wordTrace_append hprefix tailTrace_6632846
  have hstable : (prefixWord ++ tailWord_6632846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632846).length < 2 ^ (prefixWord ++ tailWord_6632846).sum := by decide
  have hdescent : baseEnd_6632846 < baseStart_6632846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632885 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_6632885 : Nat := 118140960795 + 6632885 * 2 ^ 59
def prefixEnd_6632885 : Nat := 4983230072969 + 3 ^ 40 * 6632885 * 2
def baseEnd_6632885 : Nat := 3405858130997386540633423

theorem tailTrace_6632885 : CollatzResearch.WordTrace tailWord_6632885 prefixEnd_6632885 3405858130997386540633423 := by
  unfold tailWord_6632885
  simp only [CollatzResearch.WordTrace]
  refine ⟨241921190575197926415772109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161280793716798617610514739 241921190575197926415772109)
  ·
    refine ⟨90720446465699222405914541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241921190575197926415772109 90720446465699222405914541)
    ·
      refine ⟨34020167424637208402217953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90720446465699222405914541 34020167424637208402217953)
      ·
        refine ⟨25515125568477906301663465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34020167424637208402217953 25515125568477906301663465)
        ·
          refine ⟨19136344176358429726247599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25515125568477906301663465 19136344176358429726247599)
          ·
            refine ⟨28704516264537644589371399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19136344176358429726247599 28704516264537644589371399)
            ·
              refine ⟨43056774396806466884057099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28704516264537644589371399 43056774396806466884057099)
              ·
                refine ⟨64585161595209700326085649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43056774396806466884057099 64585161595209700326085649)
                ·
                  refine ⟨48438871196407275244564237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64585161595209700326085649 48438871196407275244564237)
                  ·
                    refine ⟨18164576698652728216711589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48438871196407275244564237 18164576698652728216711589)
                    ·
                      refine ⟨3405858130997386540633423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18164576698652728216711589 3405858130997386540633423)
                      ·
                        rfl

theorem cell23_6632885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_6632885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632885 prefixEnd_6632885 := by exact prefixLift 6632885
  have htrace : WordTrace (prefixWord ++ tailWord_6632885) baseStart_6632885 baseEnd_6632885 := by
    simpa [prefixWord, tailWord_6632885, baseEnd_6632885] using wordTrace_append hprefix tailTrace_6632885
  have hstable : (prefixWord ++ tailWord_6632885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632885).length < 2 ^ (prefixWord ++ tailWord_6632885).sum := by decide
  have hdescent : baseEnd_6632885 < baseStart_6632885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632888 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_6632888 : Nat := 118140960795 + 6632888 * 2 ^ 59
def prefixEnd_6632888 : Nat := 4983230072969 + 3 ^ 40 * 6632888 * 2
def baseEnd_6632888 : Nat := 3405859671439350028895909

theorem tailTrace_6632888 : CollatzResearch.WordTrace tailWord_6632888 prefixEnd_6632888 3405859671439350028895909 := by
  unfold tailWord_6632888
  simp only [CollatzResearch.WordTrace]
  refine ⟨120960649997093528964065659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161280866662791371952087545 120960649997093528964065659)
  ·
    refine ⟨181440974995640293446098489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120960649997093528964065659 181440974995640293446098489)
    ·
      refine ⟨136080731246730220084573867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181440974995640293446098489 136080731246730220084573867)
      ·
        refine ⟨204121096870095330126860801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136080731246730220084573867 204121096870095330126860801)
        ·
          refine ⟨153090822652571497595145601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204121096870095330126860801 153090822652571497595145601)
          ·
            refine ⟨114818116989428623196359201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153090822652571497595145601 114818116989428623196359201)
            ·
              refine ⟨86113587742071467397269401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114818116989428623196359201 86113587742071467397269401)
              ·
                refine ⟨64585190806553600547952051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86113587742071467397269401 64585190806553600547952051)
                ·
                  refine ⟨96877786209830400821928077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64585190806553600547952051 96877786209830400821928077)
                  ·
                    refine ⟨36329169828686400308223029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96877786209830400821928077 36329169828686400308223029)
                    ·
                      refine ⟨3405859671439350028895909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36329169828686400308223029 3405859671439350028895909)
                      ·
                        rfl

theorem cell23_6632888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_6632888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632888 prefixEnd_6632888 := by exact prefixLift 6632888
  have htrace : WordTrace (prefixWord ++ tailWord_6632888) baseStart_6632888 baseEnd_6632888 := by
    simpa [prefixWord, tailWord_6632888, baseEnd_6632888] using wordTrace_append hprefix tailTrace_6632888
  have hstable : (prefixWord ++ tailWord_6632888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632888).length < 2 ^ (prefixWord ++ tailWord_6632888).sum := by decide
  have hdescent : baseEnd_6632888 < baseStart_6632888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632942 : List Nat := [4, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_6632942 : Nat := 118140960795 + 6632942 * 2 ^ 59
def prefixEnd_6632942 : Nat := 4983230072969 + 3 ^ 40 * 6632942 * 2
def baseEnd_6632942 : Nat := 378431933266076979735629

theorem tailTrace_6632942 : CollatzResearch.WordTrace tailWord_6632942 prefixEnd_6632942 378431933266076979735629 := by
  unfold tailWord_6632942
  simp only [CollatzResearch.WordTrace]
  refine ⟨30240408691998928143824635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161282179690660950100398053 30240408691998928143824635)
  ·
    refine ⟨45360613037998392215736953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30240408691998928143824635 45360613037998392215736953)
    ·
      refine ⟨34020459778498794161802715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45360613037998392215736953 34020459778498794161802715)
      ·
        refine ⟨51030689667748191242704073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34020459778498794161802715 51030689667748191242704073)
        ·
          refine ⟨38273017250811143432028055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51030689667748191242704073 38273017250811143432028055)
          ·
            refine ⟨57409525876216715148042083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38273017250811143432028055 57409525876216715148042083)
            ·
              refine ⟨86114288814325072722063125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57409525876216715148042083 86114288814325072722063125)
              ·
                refine ⟨4036607288171487783846709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86114288814325072722063125 4036607288171487783846709)
                ·
                  refine ⟨378431933266076979735629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4036607288171487783846709 378431933266076979735629)
                  ·
                    rfl

theorem cell23_6632942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_6632942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632942 prefixEnd_6632942 := by exact prefixLift 6632942
  have htrace : WordTrace (prefixWord ++ tailWord_6632942) baseStart_6632942 baseEnd_6632942 := by
    simpa [prefixWord, tailWord_6632942, baseEnd_6632942] using wordTrace_append hprefix tailTrace_6632942
  have hstable : (prefixWord ++ tailWord_6632942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632942).length < 2 ^ (prefixWord ++ tailWord_6632942).sum := by decide
  have hdescent : baseEnd_6632942 < baseStart_6632942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6632992 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_6632992 : Nat := 118140960795 + 6632992 * 2 ^ 59
def prefixEnd_6632992 : Nat := 4983230072969 + 3 ^ 40 * 6632992 * 2
def baseEnd_6632992 : Nat := 3405913073427417621995431

theorem tailTrace_6632992 : CollatzResearch.WordTrace tailWord_6632992 prefixEnd_6632992 3405913073427417621995431 := by
  unfold tailWord_6632992
  simp only [CollatzResearch.WordTrace]
  refine ⟨120962546592905141844958615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161283395457206855793278153 120962546592905141844958615)
  ·
    refine ⟨181443819889357712767437923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120962546592905141844958615 181443819889357712767437923)
    ·
      refine ⟨272165729834036569151156885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181443819889357712767437923 272165729834036569151156885)
      ·
        refine ⟨12757768585970464178960479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 272165729834036569151156885 12757768585970464178960479)
        ·
          refine ⟨19136652878955696268440719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12757768585970464178960479 19136652878955696268440719)
          ·
            refine ⟨28704979318433544402661079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19136652878955696268440719 28704979318433544402661079)
            ·
              refine ⟨43057468977650316603991619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28704979318433544402661079 43057468977650316603991619)
              ·
                refine ⟨64586203466475474905987429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43057468977650316603991619 64586203466475474905987429)
                ·
                  refine ⟨12109913149964151544872643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64586203466475474905987429 12109913149964151544872643)
                  ·
                    refine ⟨18164869724946227317308965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12109913149964151544872643 18164869724946227317308965)
                    ·
                      refine ⟨3405913073427417621995431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18164869724946227317308965 3405913073427417621995431)
                      ·
                        rfl

theorem cell23_6632992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_6632992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6632992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6632992 prefixEnd_6632992 := by exact prefixLift 6632992
  have htrace : WordTrace (prefixWord ++ tailWord_6632992) baseStart_6632992 baseEnd_6632992 := by
    simpa [prefixWord, tailWord_6632992, baseEnd_6632992] using wordTrace_append hprefix tailTrace_6632992
  have hstable : (prefixWord ++ tailWord_6632992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6632992).length < 2 ^ (prefixWord ++ tailWord_6632992).sum := by decide
  have hdescent : baseEnd_6632992 < baseStart_6632992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6632992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633082 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2]
def baseStart_6633082 : Nat := 118140960795 + 6633082 * 2 ^ 59
def prefixEnd_6633082 : Nat := 4983230072969 + 3 ^ 40 * 6633082 * 2
def baseEnd_6633082 : Nat := 3405959286686322269870017

theorem tailTrace_6633082 : CollatzResearch.WordTrace tailWord_6633082 prefixEnd_6633082 3405959286686322269870017 := by
  unfold tailWord_6633082
  simp only [CollatzResearch.WordTrace]
  refine ⟨60482093938871057265173375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161285583836989486040462333 60482093938871057265173375)
  ·
    refine ⟨90723140908306585897760063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60482093938871057265173375 90723140908306585897760063)
    ·
      refine ⟨136084711362459878846640095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90723140908306585897760063 136084711362459878846640095)
      ·
        refine ⟨204127067043689818269960143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136084711362459878846640095 204127067043689818269960143)
        ·
          refine ⟨306190600565534727404940215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204127067043689818269960143 306190600565534727404940215)
          ·
            refine ⟨459285900848302091107410323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306190600565534727404940215 459285900848302091107410323)
            ·
              refine ⟨688928851272453136661115485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459285900848302091107410323 688928851272453136661115485)
              ·
                refine ⟨258348319227169926247918307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 688928851272453136661115485 258348319227169926247918307)
                ·
                  refine ⟨387522478840754889371877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258348319227169926247918307 387522478840754889371877461)
                  ·
                    refine ⟨4541279048915096359826689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 387522478840754889371877461 4541279048915096359826689)
                    ·
                      refine ⟨3405959286686322269870017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541279048915096359826689 3405959286686322269870017)
                      ·
                        rfl

theorem cell23_6633082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_6633082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633082 prefixEnd_6633082 := by exact prefixLift 6633082
  have htrace : WordTrace (prefixWord ++ tailWord_6633082) baseStart_6633082 baseEnd_6633082 := by
    simpa [prefixWord, tailWord_6633082, baseEnd_6633082] using wordTrace_append hprefix tailTrace_6633082
  have hstable : (prefixWord ++ tailWord_6633082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633082).length < 2 ^ (prefixWord ++ tailWord_6633082).sum := by decide
  have hdescent : baseEnd_6633082 < baseStart_6633082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633096 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 1, 5]
def baseStart_6633096 : Nat := 118140960795 + 6633096 * 2 ^ 59
def prefixEnd_6633096 : Nat := 4983230072969 + 3 ^ 40 * 6633096 * 2
def baseEnd_6633096 : Nat := 1135322158471828405031651

theorem tailTrace_6633096 : CollatzResearch.WordTrace tailWord_6633096 prefixEnd_6633096 1135322158471828405031651 := by
  unfold tailWord_6633096
  simp only [CollatzResearch.WordTrace]
  refine ⟨120964443188716754725851571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161285924251622339634468761 120964443188716754725851571)
  ·
    refine ⟨181446664783075132088777357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120964443188716754725851571 181446664783075132088777357)
    ·
      refine ⟨68042499293653174533291509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181446664783075132088777357 68042499293653174533291509)
      ·
        refine ⟨6378984308779985112496079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68042499293653174533291509 6378984308779985112496079)
        ·
          refine ⟨9568476463169977668744119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378984308779985112496079 9568476463169977668744119)
          ·
            refine ⟨14352714694754966503116179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9568476463169977668744119 14352714694754966503116179)
            ·
              refine ⟨21529072042132449754674269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14352714694754966503116179 21529072042132449754674269)
              ·
                refine ⟨8073402015799668658002851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21529072042132449754674269 8073402015799668658002851)
                ·
                  refine ⟨12110103023699502987004277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8073402015799668658002851 12110103023699502987004277)
                  ·
                    refine ⟨1135322158471828405031651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12110103023699502987004277 1135322158471828405031651)
                    ·
                      rfl

theorem cell23_6633096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_6633096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633096 prefixEnd_6633096 := by exact prefixLift 6633096
  have htrace : WordTrace (prefixWord ++ tailWord_6633096) baseStart_6633096 baseEnd_6633096 := by
    simpa [prefixWord, tailWord_6633096, baseEnd_6633096] using wordTrace_append hprefix tailTrace_6633096
  have hstable : (prefixWord ++ tailWord_6633096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633096).length < 2 ^ (prefixWord ++ tailWord_6633096).sum := by decide
  have hdescent : baseEnd_6633096 < baseStart_6633096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633099 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 5, 2, 2]
def baseStart_6633099 : Nat := 118140960795 + 6633099 * 2 ^ 59
def prefixEnd_6633099 : Nat := 4983230072969 + 3 ^ 40 * 6633099 * 2
def baseEnd_6633099 : Nat := 3405968015857448703357439

theorem tailTrace_6633099 : CollatzResearch.WordTrace tailWord_6633099 prefixEnd_6633099 3405968015857448703357439 := by
  unfold tailWord_6633099
  simp only [CollatzResearch.WordTrace]
  refine ⟨241928995796422640964062351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161285997197615093976041567 241928995796422640964062351)
  ·
    refine ⟨362893493694633961446093527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241928995796422640964062351 362893493694633961446093527)
    ·
      refine ⟨544340240541950942169140291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362893493694633961446093527 544340240541950942169140291)
      ·
        refine ⟨816510360812926413253710437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544340240541950942169140291 816510360812926413253710437)
        ·
          refine ⟨153095692652423702485070707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 816510360812926413253710437 153095692652423702485070707)
          ·
            refine ⟨229643538978635553727606061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153095692652423702485070707 229643538978635553727606061)
            ·
              refine ⟨86116327116988332647852273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229643538978635553727606061 86116327116988332647852273)
              ·
                refine ⟨64587245337741249485889205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86116327116988332647852273 64587245337741249485889205)
                ·
                  refine ⟨6055054250413242139302113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64587245337741249485889205 6055054250413242139302113)
                  ·
                    refine ⟨4541290687809931604476585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6055054250413242139302113 4541290687809931604476585)
                    ·
                      refine ⟨3405968015857448703357439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541290687809931604476585 3405968015857448703357439)
                      ·
                        rfl

theorem cell23_6633099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 2, 2].length) (baseStart_6633099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633099 prefixEnd_6633099 := by exact prefixLift 6633099
  have htrace : WordTrace (prefixWord ++ tailWord_6633099) baseStart_6633099 baseEnd_6633099 := by
    simpa [prefixWord, tailWord_6633099, baseEnd_6633099] using wordTrace_append hprefix tailTrace_6633099
  have hstable : (prefixWord ++ tailWord_6633099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633099).length < 2 ^ (prefixWord ++ tailWord_6633099).sum := by decide
  have hdescent : baseEnd_6633099 < baseStart_6633099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633149 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_6633149 : Nat := 118140960795 + 6633149 * 2 ^ 59
def prefixEnd_6633149 : Nat := 4983230072969 + 3 ^ 40 * 6633149 * 2
def baseEnd_6633149 : Nat := 3405993689890173507732209

theorem tailTrace_6633149 : CollatzResearch.WordTrace tailWord_6633149 prefixEnd_6633149 3405993689890173507732209 := by
  unfold tailWord_6633149
  simp only [CollatzResearch.WordTrace]
  refine ⟨241930819446241499503382501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161287212964160999668921667 241930819446241499503382501)
  ·
    refine ⟨45362028646170281156884219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241930819446241499503382501 45362028646170281156884219)
    ·
      refine ⟨68043042969255421735326329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45362028646170281156884219 68043042969255421735326329)
      ·
        refine ⟨51032282226941566301494747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68043042969255421735326329 51032282226941566301494747)
        ·
          refine ⟨76548423340412349452242121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51032282226941566301494747 76548423340412349452242121)
          ·
            refine ⟨57411317505309262089181591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76548423340412349452242121 57411317505309262089181591)
            ·
              refine ⟨86116976257963893133772387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57411317505309262089181591 86116976257963893133772387)
              ·
                refine ⟨129175464386945839700658581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86116976257963893133772387 129175464386945839700658581)
                ·
                  refine ⟨6055099893138086235968371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129175464386945839700658581 6055099893138086235968371)
                  ·
                    refine ⟨9082649839707129353952557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6055099893138086235968371 9082649839707129353952557)
                    ·
                      refine ⟨3405993689890173507732209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9082649839707129353952557 3405993689890173507732209)
                      ·
                        rfl

theorem cell23_6633149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_6633149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633149 prefixEnd_6633149 := by exact prefixLift 6633149
  have htrace : WordTrace (prefixWord ++ tailWord_6633149) baseStart_6633149 baseEnd_6633149 := by
    simpa [prefixWord, tailWord_6633149, baseEnd_6633149] using wordTrace_append hprefix tailTrace_6633149
  have hstable : (prefixWord ++ tailWord_6633149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633149).length < 2 ^ (prefixWord ++ tailWord_6633149).sum := by decide
  have hdescent : baseEnd_6633149 < baseStart_6633149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633150 : List Nat := [4, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_6633150 : Nat := 118140960795 + 6633150 * 2 ^ 59
def prefixEnd_6633150 : Nat := 4983230072969 + 3 ^ 40 * 6633150 * 2
def baseEnd_6633150 : Nat := 3405994203370828003819705

theorem tailTrace_6633150 : CollatzResearch.WordTrace tailWord_6633150 prefixEnd_6633150 3405994203370828003819705 := by
  unfold tailWord_6633150
  simp only [CollatzResearch.WordTrace]
  refine ⟨30241356989904734584271113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161287237279491917782779269 30241356989904734584271113)
  ·
    refine ⟨22681017742428550938203335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30241356989904734584271113 22681017742428550938203335)
    ·
      refine ⟨34021526613642826407305003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22681017742428550938203335 34021526613642826407305003)
      ·
        refine ⟨51032289920464239610957505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34021526613642826407305003 51032289920464239610957505)
        ·
          refine ⟨38274217440348179708218129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51032289920464239610957505 38274217440348179708218129)
          ·
            refine ⟨28705663080261134781163597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38274217440348179708218129 28705663080261134781163597)
            ·
              refine ⟨10764623655097925542936349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28705663080261134781163597 10764623655097925542936349)
              ·
                refine ⟨4036733870661722078601131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10764623655097925542936349 4036733870661722078601131)
                ·
                  refine ⟨6055100805992583117901697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4036733870661722078601131 6055100805992583117901697)
                  ·
                    refine ⟨4541325604494437338426273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6055100805992583117901697 4541325604494437338426273)
                    ·
                      refine ⟨3405994203370828003819705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541325604494437338426273 3405994203370828003819705)
                      ·
                        rfl

theorem cell23_6633150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_6633150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633150 prefixEnd_6633150 := by exact prefixLift 6633150
  have htrace : WordTrace (prefixWord ++ tailWord_6633150) baseStart_6633150 baseEnd_6633150 := by
    simpa [prefixWord, tailWord_6633150, baseEnd_6633150] using wordTrace_append hprefix tailTrace_6633150
  have hstable : (prefixWord ++ tailWord_6633150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633150).length < 2 ^ (prefixWord ++ tailWord_6633150).sum := by decide
  have hdescent : baseEnd_6633150 < baseStart_6633150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633155 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8]
def baseStart_6633155 : Nat := 118140960795 + 6633155 * 2 ^ 59
def prefixEnd_6633155 : Nat := 4983230072969 + 3 ^ 40 * 6633155 * 2
def baseEnd_6633155 : Nat := 3405996770774100484257181

theorem tailTrace_6633155 : CollatzResearch.WordTrace tailWord_6633155 prefixEnd_6633155 3405996770774100484257181 := by
  unfold tailWord_6633155
  simp only [CollatzResearch.WordTrace]
  refine ⟨241931038284219762528100919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161287358856146508352067279 241931038284219762528100919)
  ·
    refine ⟨362896557426329643792151379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241931038284219762528100919 362896557426329643792151379)
    ·
      refine ⟨544344836139494465688227069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362896557426329643792151379 544344836139494465688227069)
      ·
        refine ⟨204129313552310424633085151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544344836139494465688227069 204129313552310424633085151)
        ·
          refine ⟨306193970328465636949627727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204129313552310424633085151 306193970328465636949627727)
          ·
            refine ⟨459290955492698455424441591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306193970328465636949627727 459290955492698455424441591)
            ·
              refine ⟨688936433239047683136662387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459290955492698455424441591 688936433239047683136662387)
              ·
                refine ⟨1033404649858571524704993581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 688936433239047683136662387 1033404649858571524704993581)
                ·
                  refine ⟨387526743696964321764372593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1033404649858571524704993581 387526743696964321764372593)
                  ·
                    refine ⟨290645057772723241323279445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 387526743696964321764372593 290645057772723241323279445)
                    ·
                      refine ⟨3405996770774100484257181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 290645057772723241323279445 3405996770774100484257181)
                      ·
                        rfl

theorem cell23_6633155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_6633155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633155 prefixEnd_6633155 := by exact prefixLift 6633155
  have htrace : WordTrace (prefixWord ++ tailWord_6633155) baseStart_6633155 baseEnd_6633155 := by
    simpa [prefixWord, tailWord_6633155, baseEnd_6633155] using wordTrace_append hprefix tailTrace_6633155
  have hstable : (prefixWord ++ tailWord_6633155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633155).length < 2 ^ (prefixWord ++ tailWord_6633155).sum := by decide
  have hdescent : baseEnd_6633155 < baseStart_6633155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633166 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_6633166 : Nat := 118140960795 + 6633166 * 2 ^ 59
def prefixEnd_6633166 : Nat := 4983230072969 + 3 ^ 40 * 6633166 * 2
def baseEnd_6633166 : Nat := 3406002419061299941219631

theorem tailTrace_6633166 : CollatzResearch.WordTrace tailWord_6633166 prefixEnd_6633166 3406002419061299941219631 := by
  unfold tailWord_6633166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30241429935897488925843919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161287626324786607604500901 30241429935897488925843919)
  ·
    refine ⟨45362144903846233388765879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30241429935897488925843919 45362144903846233388765879)
    ·
      refine ⟨68043217355769350083148819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45362144903846233388765879 68043217355769350083148819)
      ·
        refine ⟨102064826033654025124723229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68043217355769350083148819 102064826033654025124723229)
        ·
          refine ⟨38274309762620259421771211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102064826033654025124723229 38274309762620259421771211)
          ·
            refine ⟨57411464643930389132656817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38274309762620259421771211 57411464643930389132656817)
            ·
              refine ⟨43058598482947791849492613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57411464643930389132656817 43058598482947791849492613)
              ·
                refine ⟨8073487215552710971779865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43058598482947791849492613 8073487215552710971779865)
                ·
                  refine ⟨6055115411664533228834899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8073487215552710971779865 6055115411664533228834899)
                  ·
                    refine ⟨9082673117496799843252349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6055115411664533228834899 9082673117496799843252349)
                    ·
                      refine ⟨3406002419061299941219631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9082673117496799843252349 3406002419061299941219631)
                      ·
                        rfl

theorem cell23_6633166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_6633166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633166 prefixEnd_6633166 := by exact prefixLift 6633166
  have htrace : WordTrace (prefixWord ++ tailWord_6633166) baseStart_6633166 baseEnd_6633166 := by
    simpa [prefixWord, tailWord_6633166, baseEnd_6633166] using wordTrace_append hprefix tailTrace_6633166
  have hstable : (prefixWord ++ tailWord_6633166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633166).length < 2 ^ (prefixWord ++ tailWord_6633166).sum := by decide
  have hdescent : baseEnd_6633166 < baseStart_6633166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633206 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_6633206 : Nat := 118140960795 + 6633206 * 2 ^ 59
def prefixEnd_6633206 : Nat := 4983230072969 + 3 ^ 40 * 6633206 * 2
def baseEnd_6633206 : Nat := 3406022958287479784719447

theorem tailTrace_6633206 : CollatzResearch.WordTrace tailWord_6633206 prefixEnd_6633206 3406022958287479784719447 := by
  unfold tailWord_6633206
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120806150439687389887967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161288598938023332158804981 15120806150439687389887967)
  ·
    refine ⟨22681209225659531084831951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15120806150439687389887967 22681209225659531084831951)
    ·
      refine ⟨34021813838489296627247927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22681209225659531084831951 34021813838489296627247927)
      ·
        refine ⟨51032720757733944940871891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34021813838489296627247927 51032720757733944940871891)
        ·
          refine ⟨76549081136600917411307837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51032720757733944940871891 76549081136600917411307837)
          ·
            refine ⟨28705905426225344029240439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76549081136600917411307837 28705905426225344029240439)
            ·
              refine ⟨43058858139338016043860659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28705905426225344029240439 43058858139338016043860659)
              ·
                refine ⟨64588287209007024065790989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43058858139338016043860659 64588287209007024065790989)
                ·
                  refine ⟨24220607703377634024671621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64588287209007024065790989 24220607703377634024671621)
                  ·
                    refine ⟨4541363944383306379625929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24220607703377634024671621 4541363944383306379625929)
                    ·
                      refine ⟨3406022958287479784719447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541363944383306379625929 3406022958287479784719447)
                      ·
                        rfl

theorem cell23_6633206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_6633206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633206 prefixEnd_6633206 := by exact prefixLift 6633206
  have htrace : WordTrace (prefixWord ++ tailWord_6633206) baseStart_6633206 baseEnd_6633206 := by
    simpa [prefixWord, tailWord_6633206, baseEnd_6633206] using wordTrace_append hprefix tailTrace_6633206
  have hstable : (prefixWord ++ tailWord_6633206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633206).length < 2 ^ (prefixWord ++ tailWord_6633206).sum := by decide
  have hdescent : baseEnd_6633206 < baseStart_6633206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633239 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_6633239 : Nat := 118140960795 + 6633239 * 2 ^ 59
def prefixEnd_6633239 : Nat := 4983230072969 + 3 ^ 40 * 6633239 * 2
def baseEnd_6633239 : Nat := 3406039903149078155606795

theorem tailTrace_6633239 : CollatzResearch.WordTrace tailWord_6633239 prefixEnd_6633239 3406039903149078155606795 := by
  unfold tailWord_6633239
  simp only [CollatzResearch.WordTrace]
  refine ⟨241934102015915444874158771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161289401343943629916105847 241934102015915444874158771)
  ·
    refine ⟨362901153023873167311238157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241934102015915444874158771 362901153023873167311238157)
    ·
      refine ⟨136087932383952437741714309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362901153023873167311238157 136087932383952437741714309)
      ·
        refine ⟨25516487321991082076571433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136087932383952437741714309 25516487321991082076571433)
        ·
          refine ⟨19137365491493311557428575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25516487321991082076571433 19137365491493311557428575)
          ·
            refine ⟨28706048237239967336142863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19137365491493311557428575 28706048237239967336142863)
            ·
              refine ⟨43059072355859951004214295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28706048237239967336142863 43059072355859951004214295)
              ·
                refine ⟨64588608533789926506321443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43059072355859951004214295 64588608533789926506321443)
                ·
                  refine ⟨96882912800684889759482165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64588608533789926506321443 96882912800684889759482165)
                  ·
                    refine ⟨9082773075064208414951453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96882912800684889759482165 9082773075064208414951453)
                    ·
                      refine ⟨3406039903149078155606795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9082773075064208414951453 3406039903149078155606795)
                      ·
                        rfl

theorem cell23_6633239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_6633239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633239 prefixEnd_6633239 := by exact prefixLift 6633239
  have htrace : WordTrace (prefixWord ++ tailWord_6633239) baseStart_6633239 baseEnd_6633239 := by
    simpa [prefixWord, tailWord_6633239, baseEnd_6633239] using wordTrace_append hprefix tailTrace_6633239
  have hstable : (prefixWord ++ tailWord_6633239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633239).length < 2 ^ (prefixWord ++ tailWord_6633239).sum := by decide
  have hdescent : baseEnd_6633239 < baseStart_6633239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633349 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_6633349 : Nat := 118140960795 + 6633349 * 2 ^ 59
def prefixEnd_6633349 : Nat := 4983230072969 + 3 ^ 40 * 6633349 * 2
def baseEnd_6633349 : Nat := 1135365462007024241743763

theorem tailTrace_6633349 : CollatzResearch.WordTrace tailWord_6633349 prefixEnd_6633349 1135365462007024241743763 := by
  unfold tailWord_6633349
  simp only [CollatzResearch.WordTrace]
  refine ⟨241938114045516933660663101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161292076030344622440442067 241938114045516933660663101)
  ·
    refine ⟨90726792767068850122748663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241938114045516933660663101 90726792767068850122748663)
    ·
      refine ⟨136090189150603275184122995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90726792767068850122748663 136090189150603275184122995)
      ·
        refine ⟨204135283725904912776184493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136090189150603275184122995 204135283725904912776184493)
        ·
          refine ⟨76550731397214342291069185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204135283725904912776184493 76550731397214342291069185)
          ·
            refine ⟨57413048547910756718301889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76550731397214342291069185 57413048547910756718301889)
            ·
              refine ⟨43059786410933067538726417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57413048547910756718301889 43059786410933067538726417)
              ·
                refine ⟨32294839808199800654044813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43059786410933067538726417 32294839808199800654044813)
                ·
                  refine ⟨12110564928074925245266805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32294839808199800654044813 12110564928074925245266805)
                  ·
                    refine ⟨1135365462007024241743763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12110564928074925245266805 1135365462007024241743763)
                    ·
                      rfl

theorem cell23_6633349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_6633349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633349 prefixEnd_6633349 := by exact prefixLift 6633349
  have htrace : WordTrace (prefixWord ++ tailWord_6633349) baseStart_6633349 baseEnd_6633349 := by
    simpa [prefixWord, tailWord_6633349, baseEnd_6633349] using wordTrace_append hprefix tailTrace_6633349
  have hstable : (prefixWord ++ tailWord_6633349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633349).length < 2 ^ (prefixWord ++ tailWord_6633349).sum := by decide
  have hdescent : baseEnd_6633349 < baseStart_6633349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633356 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 6, 3, 2]
def baseStart_6633356 : Nat := 118140960795 + 6633356 * 2 ^ 59
def prefixEnd_6633356 : Nat := 4983230072969 + 3 ^ 40 * 6633356 * 2
def baseEnd_6633356 : Nat := 3406099980385654197843757

theorem tailTrace_6633356 : CollatzResearch.WordTrace tailWord_6633356 prefixEnd_6633356 3406099980385654197843757 := by
  unfold tailWord_6633356
  simp only [CollatzResearch.WordTrace]
  refine ⟨120969184678245786928083961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161292246237661049237445281 120969184678245786928083961)
  ·
    refine ⟨90726888508684340196062971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120969184678245786928083961 90726888508684340196062971)
    ·
      refine ⟨136090332763026510294094457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90726888508684340196062971 136090332763026510294094457)
      ·
        refine ⟨102067749572269882720570843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136090332763026510294094457 102067749572269882720570843)
        ·
          refine ⟨153101624358404824080856265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102067749572269882720570843 153101624358404824080856265)
          ·
            refine ⟨114826218268803618060642199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153101624358404824080856265 114826218268803618060642199)
            ·
              refine ⟨172239327403205427090963299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114826218268803618060642199 172239327403205427090963299)
              ·
                refine ⟨258358991104808140636444949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172239327403205427090963299 258358991104808140636444949)
                ·
                  refine ⟨12110577708037881592333357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 258358991104808140636444949 12110577708037881592333357)
                  ·
                    refine ⟨4541466640514205597125009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12110577708037881592333357 4541466640514205597125009)
                    ·
                      refine ⟨3406099980385654197843757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541466640514205597125009 3406099980385654197843757)
                      ·
                        rfl

theorem cell23_6633356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_6633356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633356 prefixEnd_6633356 := by exact prefixLift 6633356
  have htrace : WordTrace (prefixWord ++ tailWord_6633356) baseStart_6633356 baseEnd_6633356 := by
    simpa [prefixWord, tailWord_6633356, baseEnd_6633356] using wordTrace_append hprefix tailTrace_6633356
  have hstable : (prefixWord ++ tailWord_6633356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633356).length < 2 ^ (prefixWord ++ tailWord_6633356).sum := by decide
  have hdescent : baseEnd_6633356 < baseStart_6633356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633373 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_6633373 : Nat := 118140960795 + 6633373 * 2 ^ 59
def prefixEnd_6633373 : Nat := 4983230072969 + 3 ^ 40 * 6633373 * 2
def baseEnd_6633373 : Nat := 3406108709556780631331179

theorem tailTrace_6633373 : CollatzResearch.WordTrace tailWord_6633373 prefixEnd_6633373 3406108709556780631331179 := by
  unfold tailWord_6633373
  simp only [CollatzResearch.WordTrace]
  refine ⟨241938989397429985759536773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161292659598286657173024515 241938989397429985759536773)
  ·
    refine ⟨45363560512018122329913145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241938989397429985759536773 45363560512018122329913145)
    ·
      refine ⟨34022670384013591747434859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45363560512018122329913145 34022670384013591747434859)
      ·
        refine ⟨51034005576020387621152289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34022670384013591747434859 51034005576020387621152289)
        ·
          refine ⟨38275504182015290715864217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51034005576020387621152289 38275504182015290715864217)
          ·
            refine ⟨28706628136511468036898163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38275504182015290715864217 28706628136511468036898163)
            ·
              refine ⟨43059942204767202055347245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28706628136511468036898163 43059942204767202055347245)
              ·
                refine ⟨16147478326787700770755217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43059942204767202055347245 16147478326787700770755217)
                ·
                  refine ⟨12110608745090775578066413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16147478326787700770755217 12110608745090775578066413)
                  ·
                    refine ⟨4541478279409040841774905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12110608745090775578066413 4541478279409040841774905)
                    ·
                      refine ⟨3406108709556780631331179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541478279409040841774905 3406108709556780631331179)
                      ·
                        rfl

theorem cell23_6633373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_6633373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633373 prefixEnd_6633373 := by exact prefixLift 6633373
  have htrace : WordTrace (prefixWord ++ tailWord_6633373) baseStart_6633373 baseEnd_6633373 := by
    simpa [prefixWord, tailWord_6633373, baseEnd_6633373] using wordTrace_append hprefix tailTrace_6633373
  have hstable : (prefixWord ++ tailWord_6633373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633373).length < 2 ^ (prefixWord ++ tailWord_6633373).sum := by decide
  have hdescent : baseEnd_6633373 < baseStart_6633373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633397 : List Nat := [1, 3, 3, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_6633397 : Nat := 118140960795 + 6633397 * 2 ^ 59
def prefixEnd_6633397 : Nat := 4983230072969 + 3 ^ 40 * 6633397 * 2
def baseEnd_6633397 : Nat := 3406121033092488537431069

theorem tailTrace_6633397 : CollatzResearch.WordTrace tailWord_6633397 prefixEnd_6633397 3406121033092488537431069 := by
  unfold tailWord_6633397
  simp only [CollatzResearch.WordTrace]
  refine ⟨241939864749343037858410445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161293243166228691905606963 241939864749343037858410445)
  ·
    refine ⟨90727449281003639196903917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241939864749343037858410445 90727449281003639196903917)
    ·
      refine ⟨34022793480376364698838969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90727449281003639196903917 34022793480376364698838969)
      ·
        refine ⟨25517095110282273524129227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34022793480376364698838969 25517095110282273524129227)
        ·
          refine ⟨38275642665423410286193841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25517095110282273524129227 38275642665423410286193841)
          ·
            refine ⟨28706731999067557714645381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38275642665423410286193841 28706731999067557714645381)
            ·
              refine ⟨5382512249825167071496009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28706731999067557714645381 5382512249825167071496009)
              ·
                refine ⟨4036884187368875303622007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5382512249825167071496009 4036884187368875303622007)
                ·
                  refine ⟨6055326281053312955433011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4036884187368875303622007 6055326281053312955433011)
                  ·
                    refine ⟨9082989421579969433149517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6055326281053312955433011 9082989421579969433149517)
                    ·
                      refine ⟨3406121033092488537431069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9082989421579969433149517 3406121033092488537431069)
                      ·
                        rfl

theorem cell23_6633397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_6633397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633397 prefixEnd_6633397 := by exact prefixLift 6633397
  have htrace : WordTrace (prefixWord ++ tailWord_6633397) baseStart_6633397 baseEnd_6633397 := by
    simpa [prefixWord, tailWord_6633397, baseEnd_6633397] using wordTrace_append hprefix tailTrace_6633397
  have hstable : (prefixWord ++ tailWord_6633397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633397).length < 2 ^ (prefixWord ++ tailWord_6633397).sum := by decide
  have hdescent : baseEnd_6633397 < baseStart_6633397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633399 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_6633399 : Nat := 118140960795 + 6633399 * 2 ^ 59
def prefixEnd_6633399 : Nat := 4983230072969 + 3 ^ 40 * 6633399 * 2
def baseEnd_6633399 : Nat := 3406122060053797529606059

theorem tailTrace_6633399 : CollatzResearch.WordTrace tailWord_6633399 prefixEnd_6633399 3406122060053797529606059 := by
  unfold tailWord_6633399
  simp only [CollatzResearch.WordTrace]
  refine ⟨241939937695335792199983251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161293291796890528133322167 241939937695335792199983251)
  ·
    refine ⟨362909906543003688299974877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241939937695335792199983251 362909906543003688299974877)
    ·
      refine ⟨136091214953626383112490579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362909906543003688299974877 136091214953626383112490579)
      ·
        refine ⟨204136822430439574668735869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136091214953626383112490579 204136822430439574668735869)
        ·
          refine ⟨76551308411414840500775951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204136822430439574668735869 76551308411414840500775951)
          ·
            refine ⟨114826962617122260751163927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76551308411414840500775951 114826962617122260751163927)
            ·
              refine ⟨172240443925683391126745891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114826962617122260751163927 172240443925683391126745891)
              ·
                refine ⟨258360665888525086690118837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172240443925683391126745891 258360665888525086690118837)
                ·
                  refine ⟨24221312427049226877198641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 258360665888525086690118837 24221312427049226877198641)
                  ·
                    refine ⟨18165984320286920157898981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24221312427049226877198641 18165984320286920157898981)
                    ·
                      refine ⟨3406122060053797529606059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18165984320286920157898981 3406122060053797529606059)
                      ·
                        rfl

theorem cell23_6633399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_6633399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633399 prefixEnd_6633399 := by exact prefixLift 6633399
  have htrace : WordTrace (prefixWord ++ tailWord_6633399) baseStart_6633399 baseEnd_6633399 := by
    simpa [prefixWord, tailWord_6633399, baseEnd_6633399] using wordTrace_append hprefix tailTrace_6633399
  have hstable : (prefixWord ++ tailWord_6633399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633399).length < 2 ^ (prefixWord ++ tailWord_6633399).sum := by decide
  have hdescent : baseEnd_6633399 < baseStart_6633399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633416 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_6633416 : Nat := 118140960795 + 6633416 * 2 ^ 59
def prefixEnd_6633416 : Nat := 4983230072969 + 3 ^ 40 * 6633416 * 2
def baseEnd_6633416 : Nat := 3406130789224923963093481

theorem tailTrace_6633416 : CollatzResearch.WordTrace tailWord_6633416 prefixEnd_6633416 3406130789224923963093481 := by
  unfold tailWord_6633416
  simp only [CollatzResearch.WordTrace]
  refine ⟨120970278868137102051676051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161293705157516136068901401 120970278868137102051676051)
  ·
    refine ⟨181455418302205653077514077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120970278868137102051676051 181455418302205653077514077)
    ·
      refine ⟨68045781863327119904067779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181455418302205653077514077 68045781863327119904067779)
      ·
        refine ⟨102068672794990679856101669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68045781863327119904067779 102068672794990679856101669)
        ·
          refine ⟨19137876149060752473019063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102068672794990679856101669 19137876149060752473019063)
          ·
            refine ⟨28706814223591128709528595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19137876149060752473019063 28706814223591128709528595)
            ·
              refine ⟨43060221335386693064292893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28706814223591128709528595 43060221335386693064292893)
              ·
                refine ⟨16147583000770009899109835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43060221335386693064292893 16147583000770009899109835)
                ·
                  refine ⟨24221374501155014848664753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16147583000770009899109835 24221374501155014848664753)
                  ·
                    refine ⟨18166030875866261136498565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24221374501155014848664753 18166030875866261136498565)
                    ·
                      refine ⟨3406130789224923963093481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18166030875866261136498565 3406130789224923963093481)
                      ·
                        rfl

theorem cell23_6633416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_6633416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633416 prefixEnd_6633416 := by exact prefixLift 6633416
  have htrace : WordTrace (prefixWord ++ tailWord_6633416) baseStart_6633416 baseEnd_6633416 := by
    simpa [prefixWord, tailWord_6633416, baseEnd_6633416] using wordTrace_append hprefix tailTrace_6633416
  have hstable : (prefixWord ++ tailWord_6633416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633416).length < 2 ^ (prefixWord ++ tailWord_6633416).sum := by decide
  have hdescent : baseEnd_6633416 < baseStart_6633416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633420 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 3, 2, 2]
def baseStart_6633420 : Nat := 118140960795 + 6633420 * 2 ^ 59
def prefixEnd_6633420 : Nat := 4983230072969 + 3 ^ 40 * 6633420 * 2
def baseEnd_6633420 : Nat := 3406132843147541947443463

theorem tailTrace_6633420 : CollatzResearch.WordTrace tailWord_6633420 prefixEnd_6633420 3406132843147541947443463 := by
  unfold tailWord_6633420
  simp only [CollatzResearch.WordTrace]
  refine ⟨120970351814129856393248857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161293802418839808524331809 120970351814129856393248857)
  ·
    refine ⟨90727763860597392294936643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120970351814129856393248857 90727763860597392294936643)
    ·
      refine ⟨136091645790896088442404965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90727763860597392294936643 136091645790896088442404965)
      ·
        refine ⟨25517183585793016582950931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136091645790896088442404965 25517183585793016582950931)
        ·
          refine ⟨38275775378689524874426397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25517183585793016582950931 38275775378689524874426397)
          ·
            refine ⟨14353415767008571827909899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38275775378689524874426397 14353415767008571827909899)
            ·
              refine ⟨21530123650512857741864849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14353415767008571827909899 21530123650512857741864849)
              ·
                refine ⟨16147592737884643306398637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21530123650512857741864849 16147592737884643306398637)
                ·
                  refine ⟨6055347276706741239899489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16147592737884643306398637 6055347276706741239899489)
                  ·
                    refine ⟨4541510457530055929924617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6055347276706741239899489 4541510457530055929924617)
                    ·
                      refine ⟨3406132843147541947443463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541510457530055929924617 3406132843147541947443463)
                      ·
                        rfl

theorem cell23_6633420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_6633420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633420 prefixEnd_6633420 := by exact prefixLift 6633420
  have htrace : WordTrace (prefixWord ++ tailWord_6633420) baseStart_6633420 baseEnd_6633420 := by
    simpa [prefixWord, tailWord_6633420, baseEnd_6633420] using wordTrace_append hprefix tailTrace_6633420
  have hstable : (prefixWord ++ tailWord_6633420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633420).length < 2 ^ (prefixWord ++ tailWord_6633420).sum := by decide
  have hdescent : baseEnd_6633420 < baseStart_6633420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633437 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_6633437 : Nat := 118140960795 + 6633437 * 2 ^ 59
def prefixEnd_6633437 : Nat := 4983230072969 + 3 ^ 40 * 6633437 * 2
def baseEnd_6633437 : Nat := 3406141572318668380930885

theorem tailTrace_6633437 : CollatzResearch.WordTrace tailWord_6633437 prefixEnd_6633437 3406141572318668380930885 := by
  unfold tailWord_6633437
  simp only [CollatzResearch.WordTrace]
  refine ⟨241941323669198124689866565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161294215779465416459911043 241941323669198124689866565)
  ·
    refine ⟨45363998187974648379349981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241941323669198124689866565 45363998187974648379349981)
    ·
      refine ⟨17011499320490493142256243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45363998187974648379349981 17011499320490493142256243)
      ·
        refine ⟨25517248980735739713384365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17011499320490493142256243 25517248980735739713384365)
        ·
          refine ⟨9568968367775902392519137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25517248980735739713384365 9568968367775902392519137)
          ·
            refine ⟨7176726275831926794389353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9568968367775902392519137 7176726275831926794389353)
            ·
              refine ⟨5382544706873945095792015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7176726275831926794389353 5382544706873945095792015)
              ·
                refine ⟨8073817060310917643688023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382544706873945095792015 8073817060310917643688023)
                ·
                  refine ⟨12110725590466376465532035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8073817060310917643688023 12110725590466376465532035)
                  ·
                    refine ⟨18166088385699564698298053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12110725590466376465532035 18166088385699564698298053)
                    ·
                      refine ⟨3406141572318668380930885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18166088385699564698298053 3406141572318668380930885)
                      ·
                        rfl

theorem cell23_6633437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_6633437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633437 prefixEnd_6633437 := by exact prefixLift 6633437
  have htrace : WordTrace (prefixWord ++ tailWord_6633437) baseStart_6633437 baseEnd_6633437 := by
    simpa [prefixWord, tailWord_6633437, baseEnd_6633437] using wordTrace_append hprefix tailTrace_6633437
  have hstable : (prefixWord ++ tailWord_6633437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633437).length < 2 ^ (prefixWord ++ tailWord_6633437).sum := by decide
  have hdescent : baseEnd_6633437 < baseStart_6633437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633447 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 2, 4]
def baseStart_6633447 : Nat := 118140960795 + 6633447 * 2 ^ 59
def prefixEnd_6633447 : Nat := 4983230072969 + 3 ^ 40 * 6633447 * 2
def baseEnd_6633447 : Nat := 1135382235708404447268613

theorem tailTrace_6633447 : CollatzResearch.WordTrace tailWord_6633447 prefixEnd_6633447 1135382235708404447268613 := by
  unfold tailWord_6633447
  simp only [CollatzResearch.WordTrace]
  refine ⟨241941688399161896397730595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161294458932774597598487063 241941688399161896397730595)
  ·
    refine ⟨362912532598742844596595893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241941688399161896397730595 362912532598742844596595893)
    ·
      refine ⟨34023049931132141680930865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 362912532598742844596595893 34023049931132141680930865)
      ·
        refine ⟨25517287448349106260698149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34023049931132141680930865 25517287448349106260698149)
        ·
          refine ⟨4784491396565457423880903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25517287448349106260698149 4784491396565457423880903)
          ·
            refine ⟨7176737094848186135821355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784491396565457423880903 7176737094848186135821355)
            ·
              refine ⟨10765105642272279203732033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7176737094848186135821355 10765105642272279203732033)
              ·
                refine ⟨8073829231704209402799025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10765105642272279203732033 8073829231704209402799025)
                ·
                  refine ⟨6055371923778157052099269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8073829231704209402799025 6055371923778157052099269)
                  ·
                    refine ⟨1135382235708404447268613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6055371923778157052099269 1135382235708404447268613)
                    ·
                      rfl

theorem cell23_6633447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_6633447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633447 prefixEnd_6633447 := by exact prefixLift 6633447
  have htrace : WordTrace (prefixWord ++ tailWord_6633447) baseStart_6633447 baseEnd_6633447 := by
    simpa [prefixWord, tailWord_6633447, baseEnd_6633447] using wordTrace_append hprefix tailTrace_6633447
  have hstable : (prefixWord ++ tailWord_6633447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633447).length < 2 ^ (prefixWord ++ tailWord_6633447).sum := by decide
  have hdescent : baseEnd_6633447 < baseStart_6633447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633459 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4]
def baseStart_6633459 : Nat := 118140960795 + 6633459 * 2 ^ 59
def prefixEnd_6633459 : Nat := 4983230072969 + 3 ^ 40 * 6633459 * 2
def baseEnd_6633459 : Nat := 3406152868893067294855783

theorem tailTrace_6633459 : CollatzResearch.WordTrace tailWord_6633459 prefixEnd_6633459 3406152868893067294855783 := by
  unfold tailWord_6633459
  simp only [CollatzResearch.WordTrace]
  refine ⟨241942126075118422447167431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161294750716745614964778287 241942126075118422447167431)
  ·
    refine ⟨362913189112677633670751147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241942126075118422447167431 362913189112677633670751147)
    ·
      refine ⟨544369783669016450506126721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362913189112677633670751147 544369783669016450506126721)
      ·
        refine ⟨408277337751762337879595041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 544369783669016450506126721 408277337751762337879595041)
        ·
          refine ⟨306208003313821753409696281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408277337751762337879595041 306208003313821753409696281)
          ·
            refine ⟨229656002485366315057272211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306208003313821753409696281 229656002485366315057272211)
            ·
              refine ⟨344484003728049472585908317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229656002485366315057272211 344484003728049472585908317)
              ·
                refine ⟨129181501398018552219715619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 344484003728049472585908317 129181501398018552219715619)
                ·
                  refine ⟨193772252097027828329573429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129181501398018552219715619 193772252097027828329573429)
                  ·
                    refine ⟨18166148634096358905897509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 193772252097027828329573429 18166148634096358905897509)
                    ·
                      refine ⟨3406152868893067294855783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18166148634096358905897509 3406152868893067294855783)
                      ·
                        rfl

theorem cell23_6633459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_6633459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633459 prefixEnd_6633459 := by exact prefixLift 6633459
  have htrace : WordTrace (prefixWord ++ tailWord_6633459) baseStart_6633459 baseEnd_6633459 := by
    simpa [prefixWord, tailWord_6633459, baseEnd_6633459] using wordTrace_append hprefix tailTrace_6633459
  have hstable : (prefixWord ++ tailWord_6633459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633459).length < 2 ^ (prefixWord ++ tailWord_6633459).sum := by decide
  have hdescent : baseEnd_6633459 < baseStart_6633459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633470 : List Nat := [4, 2, 2, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_6633470 : Nat := 118140960795 + 6633470 * 2 ^ 59
def prefixEnd_6633470 : Nat := 4983230072969 + 3 ^ 40 * 6633470 * 2
def baseEnd_6633470 : Nat := 3406158517180266751818233

theorem tailTrace_6633470 : CollatzResearch.WordTrace tailWord_6633470 prefixEnd_6633470 3406158517180266751818233 := by
  unfold tailWord_6633470
  simp only [CollatzResearch.WordTrace]
  refine ⟨30242815909759821415727233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161295018185385714217211909 30242815909759821415727233)
  ·
    refine ⟨22682111932319866061795425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30242815909759821415727233 22682111932319866061795425)
    ·
      refine ⟨17011583949239899546346569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22682111932319866061795425 17011583949239899546346569)
      ·
        refine ⟨12758687961929924659759927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17011583949239899546346569 12758687961929924659759927)
        ·
          refine ⟨19138031942894886989639891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12758687961929924659759927 19138031942894886989639891)
          ·
            refine ⟨28707047914342330484459837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19138031942894886989639891 28707047914342330484459837)
            ·
              refine ⟨10765142967878373931672439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28707047914342330484459837 10765142967878373931672439)
              ·
                refine ⟨16147714451817560897508659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10765142967878373931672439 16147714451817560897508659)
                ·
                  refine ⟨24221571677726341346262989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16147714451817560897508659 24221571677726341346262989)
                  ·
                    refine ⟨9083089379147378004848621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24221571677726341346262989 9083089379147378004848621)
                    ·
                      refine ⟨3406158517180266751818233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9083089379147378004848621 3406158517180266751818233)
                      ·
                        rfl

theorem cell23_6633470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_6633470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633470 prefixEnd_6633470 := by exact prefixLift 6633470
  have htrace : WordTrace (prefixWord ++ tailWord_6633470) baseStart_6633470 baseEnd_6633470 := by
    simpa [prefixWord, tailWord_6633470, baseEnd_6633470] using wordTrace_append hprefix tailTrace_6633470
  have hstable : (prefixWord ++ tailWord_6633470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633470).length < 2 ^ (prefixWord ++ tailWord_6633470).sum := by decide
  have hdescent : baseEnd_6633470 < baseStart_6633470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633480 : List Nat := [2, 1, 3, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_6633480 : Nat := 118140960795 + 6633480 * 2 ^ 59
def prefixEnd_6633480 : Nat := 4983230072969 + 3 ^ 40 * 6633480 * 2
def baseEnd_6633480 : Nat := 3406163651986811712693187

theorem tailTrace_6633480 : CollatzResearch.WordTrace tailWord_6633480 prefixEnd_6633480 3406163651986811712693187 := by
  unfold tailWord_6633480
  simp only [CollatzResearch.WordTrace]
  refine ⟨120971446004021171516840947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161295261338694895355787929 120971446004021171516840947)
  ·
    refine ⟨181457169006031757275261421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120971446004021171516840947 181457169006031757275261421)
    ·
      refine ⟨68046438377261908978223033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181457169006031757275261421 68046438377261908978223033)
      ·
        refine ⟨51034828782946431733667275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68046438377261908978223033 51034828782946431733667275)
        ·
          refine ⟨76552243174419647600500913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51034828782946431733667275 76552243174419647600500913)
          ·
            refine ⟨57414182380814735700375685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76552243174419647600500913 57414182380814735700375685)
            ·
              refine ⟨10765159196402762943820441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57414182380814735700375685 10765159196402762943820441)
              ·
                refine ⟨8073869397302072207865331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10765159196402762943820441 8073869397302072207865331)
                ·
                  refine ⟨12110804095953108311797997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8073869397302072207865331 12110804095953108311797997)
                  ·
                    refine ⟨4541551535982415616924249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12110804095953108311797997 4541551535982415616924249)
                    ·
                      refine ⟨3406163651986811712693187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541551535982415616924249 3406163651986811712693187)
                      ·
                        rfl

theorem cell23_6633480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_6633480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633480 prefixEnd_6633480 := by exact prefixLift 6633480
  have htrace : WordTrace (prefixWord ++ tailWord_6633480) baseStart_6633480 baseEnd_6633480 := by
    simpa [prefixWord, tailWord_6633480, baseEnd_6633480] using wordTrace_append hprefix tailTrace_6633480
  have hstable : (prefixWord ++ tailWord_6633480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633480).length < 2 ^ (prefixWord ++ tailWord_6633480).sum := by decide
  have hdescent : baseEnd_6633480 < baseStart_6633480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633496 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_6633496 : Nat := 118140960795 + 6633496 * 2 ^ 59
def prefixEnd_6633496 : Nat := 4983230072969 + 3 ^ 40 * 6633496 * 2
def baseEnd_6633496 : Nat := 3406171867677283650093113

theorem tailTrace_6633496 : CollatzResearch.WordTrace tailWord_6633496 prefixEnd_6633496 3406171867677283650093113 := by
  unfold tailWord_6633496
  simp only [CollatzResearch.WordTrace]
  refine ⟨120971737787992188883132171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161295650383989585177509561 120971737787992188883132171)
  ·
    refine ⟨181457606681988283324698257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120971737787992188883132171 181457606681988283324698257)
    ·
      refine ⟨136093205011491212493523693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181457606681988283324698257 136093205011491212493523693)
      ·
        refine ⟨51034951879309204685071385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136093205011491212493523693 51034951879309204685071385)
        ·
          refine ⟨38276213909481903513803539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51034951879309204685071385 38276213909481903513803539)
          ·
            refine ⟨57414320864222855270705309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38276213909481903513803539 57414320864222855270705309)
            ·
              refine ⟨21530370324083570726514491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57414320864222855270705309 21530370324083570726514491)
              ·
                refine ⟨32295555486125356089771737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21530370324083570726514491 32295555486125356089771737)
                ·
                  refine ⟨24221666614594017067328803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32295555486125356089771737 24221666614594017067328803)
                  ·
                    refine ⟨36332499921891025600993205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24221666614594017067328803 36332499921891025600993205)
                    ·
                      refine ⟨3406171867677283650093113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36332499921891025600993205 3406171867677283650093113)
                      ·
                        rfl

theorem cell23_6633496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_6633496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633496 prefixEnd_6633496 := by exact prefixLift 6633496
  have htrace : WordTrace (prefixWord ++ tailWord_6633496) baseStart_6633496 baseEnd_6633496 := by
    simpa [prefixWord, tailWord_6633496, baseEnd_6633496] using wordTrace_append hprefix tailTrace_6633496
  have hstable : (prefixWord ++ tailWord_6633496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633496).length < 2 ^ (prefixWord ++ tailWord_6633496).sum := by decide
  have hdescent : baseEnd_6633496 < baseStart_6633496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633519 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_6633519 : Nat := 118140960795 + 6633519 * 2 ^ 59
def prefixEnd_6633519 : Nat := 4983230072969 + 3 ^ 40 * 6633519 * 2
def baseEnd_6633519 : Nat := 3406183677732337060105507

theorem tailTrace_6633519 : CollatzResearch.WordTrace tailWord_6633519 prefixEnd_6633519 3406183677732337060105507 := by
  unfold tailWord_6633519
  simp only [CollatzResearch.WordTrace]
  refine ⟨241944314454901052694351611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161296209636600701796234407 241944314454901052694351611)
  ·
    refine ⟨362916471682351579041527417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241944314454901052694351611 362916471682351579041527417)
    ·
      refine ⟨272187353761763684281145563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362916471682351579041527417 272187353761763684281145563)
      ·
        refine ⟨408281030642645526421718345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272187353761763684281145563 408281030642645526421718345)
        ·
          refine ⟨306210772981984144816288759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408281030642645526421718345 306210772981984144816288759)
          ·
            refine ⟨459316159472976217224433139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306210772981984144816288759 459316159472976217224433139)
            ·
              refine ⟨688974239209464325836649709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459316159472976217224433139 688974239209464325836649709)
              ·
                refine ⟨258365339703549122188743641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 688974239209464325836649709 258365339703549122188743641)
                ·
                  refine ⟨193774004777661841641557731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 258365339703549122188743641 193774004777661841641557731)
                  ·
                    refine ⟨290661007166492762462336597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193774004777661841641557731 290661007166492762462336597)
                    ·
                      refine ⟨3406183677732337060105507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 290661007166492762462336597 3406183677732337060105507)
                      ·
                        rfl

theorem cell23_6633519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_6633519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633519 prefixEnd_6633519 := by exact prefixLift 6633519
  have htrace : WordTrace (prefixWord ++ tailWord_6633519) baseStart_6633519 baseEnd_6633519 := by
    simpa [prefixWord, tailWord_6633519, baseEnd_6633519] using wordTrace_append hprefix tailTrace_6633519
  have hstable : (prefixWord ++ tailWord_6633519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633519).length < 2 ^ (prefixWord ++ tailWord_6633519).sum := by decide
  have hdescent : baseEnd_6633519 < baseStart_6633519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633527 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 2, 2, 2]
def baseStart_6633527 : Nat := 118140960795 + 6633527 * 2 ^ 59
def prefixEnd_6633527 : Nat := 4983230072969 + 3 ^ 40 * 6633527 * 2
def baseEnd_6633527 : Nat := 3406187785577573028805471

theorem tailTrace_6633527 : CollatzResearch.WordTrace tailWord_6633527 prefixEnd_6633527 3406187785577573028805471 := by
  unfold tailWord_6633527
  simp only [CollatzResearch.WordTrace]
  refine ⟨241944606238872070060642835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161296404159248046707095223 241944606238872070060642835)
  ·
    refine ⟨362916909358308105090964253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241944606238872070060642835 362916909358308105090964253)
    ·
      refine ⟨136093841009365539409111595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362916909358308105090964253 136093841009365539409111595)
      ·
        refine ⟨204140761514048309113667393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136093841009365539409111595 204140761514048309113667393)
        ·
          refine ⟨153105571135536231835250545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204140761514048309113667393 153105571135536231835250545)
          ·
            refine ⟨114829178351652173876437909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153105571135536231835250545 114829178351652173876437909)
            ·
              refine ⟨5382617735233695650458027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114829178351652173876437909 5382617735233695650458027)
              ·
                refine ⟨8073926602850543475687041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382617735233695650458027 8073926602850543475687041)
                ·
                  refine ⟨6055444952137907606765281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8073926602850543475687041 6055444952137907606765281)
                  ·
                    refine ⟨4541583714103430705073961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6055444952137907606765281 4541583714103430705073961)
                    ·
                      refine ⟨3406187785577573028805471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541583714103430705073961 3406187785577573028805471)
                      ·
                        rfl

theorem cell23_6633527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_6633527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633527 prefixEnd_6633527 := by exact prefixLift 6633527
  have htrace : WordTrace (prefixWord ++ tailWord_6633527) baseStart_6633527 baseEnd_6633527 := by
    simpa [prefixWord, tailWord_6633527, baseEnd_6633527] using wordTrace_append hprefix tailTrace_6633527
  have hstable : (prefixWord ++ tailWord_6633527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633527).length < 2 ^ (prefixWord ++ tailWord_6633527).sum := by decide
  have hdescent : baseEnd_6633527 < baseStart_6633527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633583 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 1, 6, 2]
def baseStart_6633583 : Nat := 118140960795 + 6633583 * 2 ^ 59
def prefixEnd_6633583 : Nat := 4983230072969 + 3 ^ 40 * 6633583 * 2
def baseEnd_6633583 : Nat := 3406216540494224809705213

theorem tailTrace_6633583 : CollatzResearch.WordTrace tailWord_6633583 prefixEnd_6633583 3406216540494224809705213 := by
  unfold tailWord_6633583
  simp only [CollatzResearch.WordTrace]
  refine ⟨241946648726669191624681403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161297765817779461083120935 241946648726669191624681403)
  ·
    refine ⟨362919973090003787437022105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241946648726669191624681403 362919973090003787437022105)
    ·
      refine ⟨272189979817502840577766579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 362919973090003787437022105 272189979817502840577766579)
      ·
        refine ⟨408284969726254260866649869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272189979817502840577766579 408284969726254260866649869)
        ·
          refine ⟨153106863647345347824993701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408284969726254260866649869 153106863647345347824993701)
          ·
            refine ⟨28707536933877252717186319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153106863647345347824993701 28707536933877252717186319)
            ·
              refine ⟨43061305400815879075779479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28707536933877252717186319 43061305400815879075779479)
              ·
                refine ⟨64591958101223818613669219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43061305400815879075779479 64591958101223818613669219)
                ·
                  refine ⟨96887937151835727920503829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64591958101223818613669219 96887937151835727920503829)
                  ·
                    refine ⟨4541622053992299746273617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96887937151835727920503829 4541622053992299746273617)
                    ·
                      refine ⟨3406216540494224809705213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4541622053992299746273617 3406216540494224809705213)
                      ·
                        rfl

theorem cell23_6633583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6, 2].length) (baseStart_6633583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633583 prefixEnd_6633583 := by exact prefixLift 6633583
  have htrace : WordTrace (prefixWord ++ tailWord_6633583) baseStart_6633583 baseEnd_6633583 := by
    simpa [prefixWord, tailWord_6633583, baseEnd_6633583] using wordTrace_append hprefix tailTrace_6633583
  have hstable : (prefixWord ++ tailWord_6633583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633583).length < 2 ^ (prefixWord ++ tailWord_6633583).sum := by decide
  have hdescent : baseEnd_6633583 < baseStart_6633583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6633593 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 5, 4]
def baseStart_6633593 : Nat := 118140960795 + 6633593 * 2 ^ 59
def prefixEnd_6633593 : Nat := 4983230072969 + 3 ^ 40 * 6633593 * 2
def baseEnd_6633593 : Nat := 1135407225100256590193389

theorem tailTrace_6633593 : CollatzResearch.WordTrace tailWord_6633593 prefixEnd_6633593 1135407225100256590193389 := by
  unfold tailWord_6633593
  simp only [CollatzResearch.WordTrace]
  refine ⟨241947013456632963332545433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161298008971088642221696955 241947013456632963332545433)
  ·
    refine ⟨181460260092474722499409075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241947013456632963332545433 181460260092474722499409075)
    ·
      refine ⟨272190390138712083749113613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181460260092474722499409075 272190390138712083749113613)
      ·
        refine ⟨102071396302017031405917605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272190390138712083749113613 102071396302017031405917605)
        ·
          refine ⟨19138386806628193388609551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102071396302017031405917605 19138386806628193388609551)
          ·
            refine ⟨28707580209942290082914327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19138386806628193388609551 28707580209942290082914327)
            ·
              refine ⟨43061370314913435124371491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28707580209942290082914327 43061370314913435124371491)
              ·
                refine ⟨64592055472370152686557237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43061370314913435124371491 64592055472370152686557237)
                ·
                  refine ⟨6055505200534701814364741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64592055472370152686557237 6055505200534701814364741)
                  ·
                    refine ⟨1135407225100256590193389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6055505200534701814364741 1135407225100256590193389)
                    ·
                      rfl

theorem cell23_6633593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_6633593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6633593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6633593 prefixEnd_6633593 := by exact prefixLift 6633593
  have htrace : WordTrace (prefixWord ++ tailWord_6633593) baseStart_6633593 baseEnd_6633593 := by
    simpa [prefixWord, tailWord_6633593, baseEnd_6633593] using wordTrace_append hprefix tailTrace_6633593
  have hstable : (prefixWord ++ tailWord_6633593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6633593).length < 2 ^ (prefixWord ++ tailWord_6633593).sum := by decide
  have hdescent : baseEnd_6633593 < baseStart_6633593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6633593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
