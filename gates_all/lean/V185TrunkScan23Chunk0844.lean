import V185TrunkScan23Chunk0843

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4995041 : List Nat := [1, 2, 3, 1, 2, 1, 6, 2, 1, 1, 3]
def baseStart_4995041 : Nat := 118140960795 + 4995041 * 2 ^ 59
def prefixEnd_4995041 : Nat := 4983230072969 + 3 ^ 40 * 4995041 * 2
def baseEnd_4995041 : Nat := 2564856921914896612815731

theorem tailTrace_4995041 : CollatzResearch.WordTrace tailWord_4995041 prefixEnd_4995041 2564856921914896612815731 := by
  unfold tailWord_4995041
  simp only [CollatzResearch.WordTrace]
  refine ⟨182184112296827016930336977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121456074864551344620224651 182184112296827016930336977)
  ·
    refine ⟨136638084222620262697752733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182184112296827016930336977 136638084222620262697752733)
    ·
      refine ⟨51239281583482598511657275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136638084222620262697752733 51239281583482598511657275)
      ·
        refine ⟨76858922375223897767485913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51239281583482598511657275 76858922375223897767485913)
        ·
          refine ⟨57644191781417923325614435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76858922375223897767485913 57644191781417923325614435)
          ·
            refine ⟨86466287672126884988421653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57644191781417923325614435 86466287672126884988421653)
            ·
              refine ⟨4053107234630947733832265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86466287672126884988421653 4053107234630947733832265)
              ·
                refine ⟨3039830425973210800374199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4053107234630947733832265 3039830425973210800374199)
                ·
                  refine ⟨4559745638959816200561299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039830425973210800374199 4559745638959816200561299)
                  ·
                    refine ⟨6839618458439724300841949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559745638959816200561299 6839618458439724300841949)
                    ·
                      refine ⟨2564856921914896612815731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6839618458439724300841949 2564856921914896612815731)
                      ·
                        rfl

theorem cell23_4995041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_4995041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995041 prefixEnd_4995041 := by exact prefixLift 4995041
  have htrace : WordTrace (prefixWord ++ tailWord_4995041) baseStart_4995041 baseEnd_4995041 := by
    simpa [prefixWord, tailWord_4995041, baseEnd_4995041] using wordTrace_append hprefix tailTrace_4995041
  have hstable : (prefixWord ++ tailWord_4995041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995041).length < 2 ^ (prefixWord ++ tailWord_4995041).sum := by decide
  have hdescent : baseEnd_4995041 < baseStart_4995041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995050 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_4995050 : Nat := 118140960795 + 4995050 * 2 ^ 59
def prefixEnd_4995050 : Nat := 4983230072969 + 3 ^ 40 * 4995050 * 2
def baseEnd_4995050 : Nat := 2564861543240787077603189

theorem tailTrace_4995050 : CollatzResearch.WordTrace tailWord_4995050 prefixEnd_4995050 2564861543240787077603189 := by
  unfold tailWord_4995050
  simp only [CollatzResearch.WordTrace]
  refine ⟨45546110138448602866853651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121456293702529607644943069 45546110138448602866853651)
  ·
    refine ⟨68319165207672904300280477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45546110138448602866853651 68319165207672904300280477)
    ·
      refine ⟨25619686952877339112605179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68319165207672904300280477 25619686952877339112605179)
      ·
        refine ⟨38429530429316008668907769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25619686952877339112605179 38429530429316008668907769)
        ·
          refine ⟨28822147821987006501680827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38429530429316008668907769 28822147821987006501680827)
          ·
            refine ⟨43233221732980509752521241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28822147821987006501680827 43233221732980509752521241)
            ·
              refine ⟨32424916299735382314390931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43233221732980509752521241 32424916299735382314390931)
              ·
                refine ⟨48637374449603073471586397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32424916299735382314390931 48637374449603073471586397)
                ·
                  refine ⟨18239015418601152551844899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48637374449603073471586397 18239015418601152551844899)
                  ·
                    refine ⟨27358523127901728827767349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18239015418601152551844899 27358523127901728827767349)
                    ·
                      refine ⟨2564861543240787077603189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27358523127901728827767349 2564861543240787077603189)
                      ·
                        rfl

theorem cell23_4995050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_4995050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995050 prefixEnd_4995050 := by exact prefixLift 4995050
  have htrace : WordTrace (prefixWord ++ tailWord_4995050) baseStart_4995050 baseEnd_4995050 := by
    simpa [prefixWord, tailWord_4995050, baseEnd_4995050] using wordTrace_append hprefix tailTrace_4995050
  have hstable : (prefixWord ++ tailWord_4995050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995050).length < 2 ^ (prefixWord ++ tailWord_4995050).sum := by decide
  have hdescent : baseEnd_4995050 < baseStart_4995050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995057 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 1, 6]
def baseStart_4995057 : Nat := 118140960795 + 4995057 * 2 ^ 59
def prefixEnd_4995057 : Nat := 4983230072969 + 3 ^ 40 * 4995057 * 2
def baseEnd_4995057 : Nat := 854955045868456183405219

theorem tailTrace_4995057 : CollatzResearch.WordTrace tailWord_4995057 prefixEnd_4995057 854955045868456183405219 := by
  unfold tailWord_4995057
  simp only [CollatzResearch.WordTrace]
  refine ⟨182184695864769051662919425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121456463909846034441946283 182184695864769051662919425)
  ·
    refine ⟨136638521898576788747189569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182184695864769051662919425 136638521898576788747189569)
    ·
      refine ⟨102478891423932591560392177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136638521898576788747189569 102478891423932591560392177)
      ·
        refine ⟨76859168567949443670294133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102478891423932591560392177 76859168567949443670294133)
        ·
          refine ⟨7205547053245260344090075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76859168567949443670294133 7205547053245260344090075)
          ·
            refine ⟨10808320579867890516135113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7205547053245260344090075 10808320579867890516135113)
            ·
              refine ⟨8106240434900917887101335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10808320579867890516135113 8106240434900917887101335)
              ·
                refine ⟨12159360652351376830652003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8106240434900917887101335 12159360652351376830652003)
                ·
                  refine ⟨18239040978527065245978005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12159360652351376830652003 18239040978527065245978005)
                  ·
                    refine ⟨854955045868456183405219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18239040978527065245978005 854955045868456183405219)
                    ·
                      rfl

theorem cell23_4995057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_4995057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995057 prefixEnd_4995057 := by exact prefixLift 4995057
  have htrace : WordTrace (prefixWord ++ tailWord_4995057) baseStart_4995057 baseEnd_4995057 := by
    simpa [prefixWord, tailWord_4995057, baseEnd_4995057] using wordTrace_append hprefix tailTrace_4995057
  have hstable : (prefixWord ++ tailWord_4995057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995057).length < 2 ^ (prefixWord ++ tailWord_4995057).sum := by decide
  have hdescent : baseEnd_4995057 < baseStart_4995057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995063 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_4995063 : Nat := 118140960795 + 4995063 * 2 ^ 59
def prefixEnd_4995063 : Nat := 4983230072969 + 3 ^ 40 * 4995063 * 2
def baseEnd_4995063 : Nat := 2564868218489295526740629

theorem tailTrace_4995063 : CollatzResearch.WordTrace tailWord_4995063 prefixEnd_4995063 2564868218489295526740629 := by
  unfold tailWord_4995063
  simp only [CollatzResearch.WordTrace]
  refine ⟨182184914702747314687637843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121456609801831543125091895 182184914702747314687637843)
  ·
    refine ⟨273277372054120972031456765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182184914702747314687637843 273277372054120972031456765)
    ·
      refine ⟨102479014520295364511796287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273277372054120972031456765 102479014520295364511796287)
      ·
        refine ⟨153718521780443046767694431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102479014520295364511796287 153718521780443046767694431)
        ·
          refine ⟨230577782670664570151541647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153718521780443046767694431 230577782670664570151541647)
          ·
            refine ⟨345866674005996855227312471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230577782670664570151541647 345866674005996855227312471)
            ·
              refine ⟨518800011008995282840968707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345866674005996855227312471 518800011008995282840968707)
              ·
                refine ⟨778200016513492924261453061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518800011008995282840968707 778200016513492924261453061)
                ·
                  refine ⟨145912503096279923299022449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 778200016513492924261453061 145912503096279923299022449)
                  ·
                    refine ⟨109434377322209942474266837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145912503096279923299022449 109434377322209942474266837)
                    ·
                      refine ⟨2564868218489295526740629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109434377322209942474266837 2564868218489295526740629)
                      ·
                        rfl

theorem cell23_4995063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_4995063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995063 prefixEnd_4995063 := by exact prefixLift 4995063
  have htrace : WordTrace (prefixWord ++ tailWord_4995063) baseStart_4995063 baseEnd_4995063 := by
    simpa [prefixWord, tailWord_4995063, baseEnd_4995063] using wordTrace_append hprefix tailTrace_4995063
  have hstable : (prefixWord ++ tailWord_4995063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995063).length < 2 ^ (prefixWord ++ tailWord_4995063).sum := by decide
  have hdescent : baseEnd_4995063 < baseStart_4995063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995111 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4995111 : Nat := 118140960795 + 4995111 * 2 ^ 59
def prefixEnd_4995111 : Nat := 4983230072969 + 3 ^ 40 * 4995111 * 2
def baseEnd_4995111 : Nat := 2564892865560711338940409

theorem tailTrace_4995111 : CollatzResearch.WordTrace tailWord_4995111 prefixEnd_4995111 2564892865560711338940409 := by
  unfold tailWord_4995111
  simp only [CollatzResearch.WordTrace]
  refine ⟨182186665406573418885385187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121457776937715612590256791 182186665406573418885385187)
  ·
    refine ⟨273279998109860128328077781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182186665406573418885385187 273279998109860128328077781)
    ·
      refine ⟨6404999955699846757689323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 273279998109860128328077781 6404999955699846757689323)
      ·
        refine ⟨9607499933549770136533985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6404999955699846757689323 9607499933549770136533985)
        ·
          refine ⟨7205624950162327602400489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9607499933549770136533985 7205624950162327602400489)
          ·
            refine ⟨5404218712621745701800367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7205624950162327602400489 5404218712621745701800367)
            ·
              refine ⟨8106328068932618552700551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404218712621745701800367 8106328068932618552700551)
              ·
                refine ⟨12159492103398927829050827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8106328068932618552700551 12159492103398927829050827)
                ·
                  refine ⟨18239238155098391743576241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12159492103398927829050827 18239238155098391743576241)
                  ·
                    refine ⟨13679428616323793807682181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18239238155098391743576241 13679428616323793807682181)
                    ·
                      refine ⟨2564892865560711338940409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13679428616323793807682181 2564892865560711338940409)
                      ·
                        rfl

theorem cell23_4995111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4995111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995111 prefixEnd_4995111 := by exact prefixLift 4995111
  have htrace : WordTrace (prefixWord ++ tailWord_4995111) baseStart_4995111 baseEnd_4995111 := by
    simpa [prefixWord, tailWord_4995111, baseEnd_4995111] using wordTrace_append hprefix tailTrace_4995111
  have hstable : (prefixWord ++ tailWord_4995111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995111).length < 2 ^ (prefixWord ++ tailWord_4995111).sum := by decide
  have hdescent : baseEnd_4995111 < baseStart_4995111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995114 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4995114 : Nat := 118140960795 + 4995114 * 2 ^ 59
def prefixEnd_4995114 : Nat := 4983230072969 + 3 ^ 40 * 4995114 * 2
def baseEnd_4995114 : Nat := 2564894406002674827202895

theorem tailTrace_4995114 : CollatzResearch.WordTrace tailWord_4995114 prefixEnd_4995114 2564894406002674827202895 := by
  unfold tailWord_4995114
  simp only [CollatzResearch.WordTrace]
  refine ⟨45546693706390637599436099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121457849883708366931829597 45546693706390637599436099)
  ·
    refine ⟨68320040559585956399154149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45546693706390637599436099 68320040559585956399154149)
    ·
      refine ⟨12810007604922366824841403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68320040559585956399154149 12810007604922366824841403)
      ·
        refine ⟨19215011407383550237262105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12810007604922366824841403 19215011407383550237262105)
        ·
          refine ⟨14411258555537662677946579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19215011407383550237262105 14411258555537662677946579)
          ·
            refine ⟨21616887833306494016919869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14411258555537662677946579 21616887833306494016919869)
            ·
              refine ⟨8106332937489935256344951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21616887833306494016919869 8106332937489935256344951)
              ·
                refine ⟨12159499406234902884517427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8106332937489935256344951 12159499406234902884517427)
                ·
                  refine ⟨18239249109352354326776141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12159499406234902884517427 18239249109352354326776141)
                  ·
                    refine ⟨6839718416007132872541053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18239249109352354326776141 6839718416007132872541053)
                    ·
                      refine ⟨2564894406002674827202895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6839718416007132872541053 2564894406002674827202895)
                      ·
                        rfl

theorem cell23_4995114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4995114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995114 prefixEnd_4995114 := by exact prefixLift 4995114
  have htrace : WordTrace (prefixWord ++ tailWord_4995114) baseStart_4995114 baseEnd_4995114 := by
    simpa [prefixWord, tailWord_4995114, baseEnd_4995114] using wordTrace_append hprefix tailTrace_4995114
  have hstable : (prefixWord ++ tailWord_4995114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995114).length < 2 ^ (prefixWord ++ tailWord_4995114).sum := by decide
  have hdescent : baseEnd_4995114 < baseStart_4995114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995165 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4995165 : Nat := 118140960795 + 4995165 * 2 ^ 59
def prefixEnd_4995165 : Nat := 4983230072969 + 3 ^ 40 * 4995165 * 2
def baseEnd_4995165 : Nat := 2564920593516054127665161

theorem tailTrace_4995165 : CollatzResearch.WordTrace tailWord_4995165 prefixEnd_4995165 2564920593516054127665161 := by
  unfold tailWord_4995165
  simp only [CollatzResearch.WordTrace]
  refine ⟨182188634948377786107850949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121459089965585190738567299 182188634948377786107850949)
  ·
    refine ⟨34160369052820834895222053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182188634948377786107850949 34160369052820834895222053)
    ·
      refine ⟨6405069197403906542854135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34160369052820834895222053 6405069197403906542854135)
      ·
        refine ⟨9607603796105859814281203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6405069197403906542854135 9607603796105859814281203)
        ·
          refine ⟨14411405694158789721421805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9607603796105859814281203 14411405694158789721421805)
          ·
            refine ⟨5404277135309546145533177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14411405694158789721421805 5404277135309546145533177)
            ·
              refine ⟨4053207851482159609149883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5404277135309546145533177 4053207851482159609149883)
              ·
                refine ⟨6079811777223239413724825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053207851482159609149883 6079811777223239413724825)
                ·
                  refine ⟨4559858832917429560293619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079811777223239413724825 4559858832917429560293619)
                  ·
                    refine ⟨6839788249376144340440429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4559858832917429560293619 6839788249376144340440429)
                    ·
                      refine ⟨2564920593516054127665161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6839788249376144340440429 2564920593516054127665161)
                      ·
                        rfl

theorem cell23_4995165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4995165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995165 prefixEnd_4995165 := by exact prefixLift 4995165
  have htrace : WordTrace (prefixWord ++ tailWord_4995165) baseStart_4995165 baseEnd_4995165 := by
    simpa [prefixWord, tailWord_4995165, baseEnd_4995165] using wordTrace_append hprefix tailTrace_4995165
  have hstable : (prefixWord ++ tailWord_4995165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995165).length < 2 ^ (prefixWord ++ tailWord_4995165).sum := by decide
  have hdescent : baseEnd_4995165 < baseStart_4995165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995207 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 2, 5]
def baseStart_4995207 : Nat := 118140960795 + 4995207 * 2 ^ 59
def prefixEnd_4995207 : Nat := 4983230072969 + 3 ^ 40 * 4995207 * 2
def baseEnd_4995207 : Nat := 854980719901180987779989

theorem tailTrace_4995207 : CollatzResearch.WordTrace tailWord_4995207 prefixEnd_4995207 854980719901180987779989 := by
  unfold tailWord_4995207
  simp only [CollatzResearch.WordTrace]
  refine ⟨182190166814225627280879875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121460111209483751520586583 182190166814225627280879875)
  ·
    refine ⟨273285250221338440921319813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182190166814225627280879875 273285250221338440921319813)
    ·
      refine ⟨51240984416500957672747465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273285250221338440921319813 51240984416500957672747465)
      ·
        refine ⟨38430738312375718254560599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51240984416500957672747465 38430738312375718254560599)
        ·
          refine ⟨57646107468563577381840899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38430738312375718254560599 57646107468563577381840899)
          ·
            refine ⟨86469161202845366072761349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57646107468563577381840899 86469161202845366072761349)
            ·
              refine ⟨16212967725533506138642753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86469161202845366072761349 16212967725533506138642753)
              ·
                refine ⟨12159725794150129603982065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16212967725533506138642753 12159725794150129603982065)
                ·
                  refine ⟨9119794345612597202986549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12159725794150129603982065 9119794345612597202986549)
                  ·
                    refine ⟨854980719901180987779989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9119794345612597202986549 854980719901180987779989)
                    ·
                      rfl

theorem cell23_4995207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_4995207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995207 prefixEnd_4995207 := by exact prefixLift 4995207
  have htrace : WordTrace (prefixWord ++ tailWord_4995207) baseStart_4995207 baseEnd_4995207 := by
    simpa [prefixWord, tailWord_4995207, baseEnd_4995207] using wordTrace_append hprefix tailTrace_4995207
  have hstable : (prefixWord ++ tailWord_4995207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995207).length < 2 ^ (prefixWord ++ tailWord_4995207).sum := by decide
  have hdescent : baseEnd_4995207 < baseStart_4995207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995335 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 6]
def baseStart_4995335 : Nat := 118140960795 + 4995335 * 2 ^ 59
def prefixEnd_4995335 : Nat := 4983230072969 + 3 ^ 40 * 4995335 * 2
def baseEnd_4995335 : Nat := 285000876136368718059931

theorem tailTrace_4995335 : CollatzResearch.WordTrace tailWord_4995335 prefixEnd_4995335 285000876136368718059931 := by
  unfold tailWord_4995335
  simp only [CollatzResearch.WordTrace]
  refine ⟨182194835357761905141539459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121463223571841270094359639 182194835357761905141539459)
  ·
    refine ⟨273292253036642857712309189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182194835357761905141539459 273292253036642857712309189)
    ·
      refine ⟨51242297444370535821057973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273292253036642857712309189 51242297444370535821057973)
      ·
        refine ⟨4803965385409737733224185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51242297444370535821057973 4803965385409737733224185)
        ·
          refine ⟨3602974039057303299918139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4803965385409737733224185 3602974039057303299918139)
          ·
            refine ⟨5404461058585954949877209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602974039057303299918139 5404461058585954949877209)
            ·
              refine ⟨4053345793939466212407907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5404461058585954949877209 4053345793939466212407907)
              ·
                refine ⟨6080018690909199318611861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053345793939466212407907 6080018690909199318611861)
                ·
                  refine ⟨285000876136368718059931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6080018690909199318611861 285000876136368718059931)
                  ·
                    rfl

theorem cell23_4995335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 6].length) (baseStart_4995335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995335 prefixEnd_4995335 := by exact prefixLift 4995335
  have htrace : WordTrace (prefixWord ++ tailWord_4995335) baseStart_4995335 baseEnd_4995335 := by
    simpa [prefixWord, tailWord_4995335, baseEnd_4995335] using wordTrace_append hprefix tailTrace_4995335
  have hstable : (prefixWord ++ tailWord_4995335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995335).length < 2 ^ (prefixWord ++ tailWord_4995335).sum := by decide
  have hdescent : baseEnd_4995335 < baseStart_4995335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995347 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4]
def baseStart_4995347 : Nat := 118140960795 + 4995347 * 2 ^ 59
def prefixEnd_4995347 : Nat := 4983230072969 + 3 ^ 40 * 4995347 * 2
def baseEnd_4995347 : Nat := 2565014046995172415589323

theorem tailTrace_4995347 : CollatzResearch.WordTrace tailWord_4995347 prefixEnd_4995347 2565014046995172415589323 := by
  unfold tailWord_4995347
  simp only [CollatzResearch.WordTrace]
  refine ⟨182195273033718431190976295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121463515355812287460650863 182195273033718431190976295)
  ·
    refine ⟨273292909550577646786464443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182195273033718431190976295 273292909550577646786464443)
    ·
      refine ⟨409939364325866470179696665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273292909550577646786464443 409939364325866470179696665)
      ·
        refine ⟨307454523244399852634772499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409939364325866470179696665 307454523244399852634772499)
        ·
          refine ⟨461181784866599778952158749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307454523244399852634772499 461181784866599778952158749)
          ·
            refine ⟨172943169324974917107059531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461181784866599778952158749 172943169324974917107059531)
            ·
              refine ⟨259414753987462375660589297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172943169324974917107059531 259414753987462375660589297)
              ·
                refine ⟨194561065490596781745441973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259414753987462375660589297 194561065490596781745441973)
                ·
                  refine ⟨18240099889743448288635185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194561065490596781745441973 18240099889743448288635185)
                  ·
                    refine ⟨13680074917307586216476389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18240099889743448288635185 13680074917307586216476389)
                    ·
                      refine ⟨2565014046995172415589323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13680074917307586216476389 2565014046995172415589323)
                      ·
                        rfl

theorem cell23_4995347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_4995347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995347 prefixEnd_4995347 := by exact prefixLift 4995347
  have htrace : WordTrace (prefixWord ++ tailWord_4995347) baseStart_4995347 baseEnd_4995347 := by
    simpa [prefixWord, tailWord_4995347, baseEnd_4995347] using wordTrace_append hprefix tailTrace_4995347
  have hstable : (prefixWord ++ tailWord_4995347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995347).length < 2 ^ (prefixWord ++ tailWord_4995347).sum := by decide
  have hdescent : baseEnd_4995347 < baseStart_4995347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995351 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4995351 : Nat := 118140960795 + 4995351 * 2 ^ 59
def prefixEnd_4995351 : Nat := 4983230072969 + 3 ^ 40 * 4995351 * 2
def baseEnd_4995351 : Nat := 2565016100917790399939305

theorem tailTrace_4995351 : CollatzResearch.WordTrace tailWord_4995351 prefixEnd_4995351 2565016100917790399939305 := by
  unfold tailWord_4995351
  simp only [CollatzResearch.WordTrace]
  refine ⟨182195418925703939874121907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121463612617135959916081271 182195418925703939874121907)
  ·
    refine ⟨273293128388555909811182861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182195418925703939874121907 273293128388555909811182861)
    ·
      refine ⟨102484923145708466179193573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273293128388555909811182861 102484923145708466179193573)
      ·
        refine ⟨19215923089820337408598795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102484923145708466179193573 19215923089820337408598795)
        ·
          refine ⟨28823884634730506112898193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19215923089820337408598795 28823884634730506112898193)
          ·
            refine ⟨21617913476047879584673645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28823884634730506112898193 21617913476047879584673645)
            ·
              refine ⟨8106717553517954844252617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21617913476047879584673645 8106717553517954844252617)
              ·
                refine ⟨6080038165138466133189463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8106717553517954844252617 6080038165138466133189463)
                ·
                  refine ⟨9120057247707699199784195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6080038165138466133189463 9120057247707699199784195)
                  ·
                    refine ⟨13680085871561548799676293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9120057247707699199784195 13680085871561548799676293)
                    ·
                      refine ⟨2565016100917790399939305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13680085871561548799676293 2565016100917790399939305)
                      ·
                        rfl

theorem cell23_4995351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4995351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995351 prefixEnd_4995351 := by exact prefixLift 4995351
  have htrace : WordTrace (prefixWord ++ tailWord_4995351) baseStart_4995351 baseEnd_4995351 := by
    simpa [prefixWord, tailWord_4995351, baseEnd_4995351] using wordTrace_append hprefix tailTrace_4995351
  have hstable : (prefixWord ++ tailWord_4995351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995351).length < 2 ^ (prefixWord ++ tailWord_4995351).sum := by decide
  have hdescent : baseEnd_4995351 < baseStart_4995351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995364 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4995364 : Nat := 118140960795 + 4995364 * 2 ^ 59
def prefixEnd_4995364 : Nat := 4983230072969 + 3 ^ 40 * 4995364 * 2
def baseEnd_4995364 : Nat := 2565022776166298849076745

theorem tailTrace_4995364 : CollatzResearch.WordTrace tailWord_4995364 prefixEnd_4995364 2565022776166298849076745 := by
  unfold tailWord_4995364
  simp only [CollatzResearch.WordTrace]
  refine ⟨91097946537328421547172573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121463928716437895396230097 91097946537328421547172573)
  ·
    refine ⟨34161729951498158080189715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91097946537328421547172573 34161729951498158080189715)
    ·
      refine ⟨51242594927247237120284573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34161729951498158080189715 51242594927247237120284573)
      ·
        refine ⟨19215973097717713920106715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51242594927247237120284573 19215973097717713920106715)
        ·
          refine ⟨28823959646576570880160073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19215973097717713920106715 28823959646576570880160073)
          ·
            refine ⟨21617969734932428160120055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28823959646576570880160073 21617969734932428160120055)
            ·
              refine ⟨32426954602398642240180083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21617969734932428160120055 32426954602398642240180083)
              ·
                refine ⟨48640431903597963360270125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32426954602398642240180083 48640431903597963360270125)
                ·
                  refine ⟨18240161963849236260101297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48640431903597963360270125 18240161963849236260101297)
                  ·
                    refine ⟨13680121472886927195075973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18240161963849236260101297 13680121472886927195075973)
                    ·
                      refine ⟨2565022776166298849076745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13680121472886927195075973 2565022776166298849076745)
                      ·
                        rfl

theorem cell23_4995364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4995364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995364 prefixEnd_4995364 := by exact prefixLift 4995364
  have htrace : WordTrace (prefixWord ++ tailWord_4995364) baseStart_4995364 baseEnd_4995364 := by
    simpa [prefixWord, tailWord_4995364, baseEnd_4995364] using wordTrace_append hprefix tailTrace_4995364
  have hstable : (prefixWord ++ tailWord_4995364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995364).length < 2 ^ (prefixWord ++ tailWord_4995364).sum := by decide
  have hdescent : baseEnd_4995364 < baseStart_4995364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995374 : List Nat := [4, 1, 3, 3, 12]
def baseStart_4995374 : Nat := 118140960795 + 4995374 * 2 ^ 59
def prefixEnd_4995374 : Nat := 4983230072969 + 3 ^ 40 * 4995374 * 2
def baseEnd_4995374 : Nat := 3518556805175368737931

theorem tailTrace_4995374 : CollatzResearch.WordTrace tailWord_4995374 prefixEnd_4995374 3518556805175368737931 := by
  unfold tailWord_4995374
  simp only [CollatzResearch.WordTrace]
  refine ⟨22774532225577576850276147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121464171869747076534806117 22774532225577576850276147)
  ·
    refine ⟨34161798338366365275414221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22774532225577576850276147 34161798338366365275414221)
    ·
      refine ⟨12810674376887386978280333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34161798338366365275414221 12810674376887386978280333)
      ·
        refine ⟨4804002891332770116855125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12810674376887386978280333 4804002891332770116855125)
        ·
          refine ⟨3518556805175368737931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4804002891332770116855125 3518556805175368737931)
          ·
            rfl

theorem cell23_4995374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 12].length) (baseStart_4995374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995374 prefixEnd_4995374 := by exact prefixLift 4995374
  have htrace : WordTrace (prefixWord ++ tailWord_4995374) baseStart_4995374 baseEnd_4995374 := by
    simpa [prefixWord, tailWord_4995374, baseEnd_4995374] using wordTrace_append hprefix tailTrace_4995374
  have hstable : (prefixWord ++ tailWord_4995374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995374).length < 2 ^ (prefixWord ++ tailWord_4995374).sum := by decide
  have hdescent : baseEnd_4995374 < baseStart_4995374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995378 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 2, 4]
def baseStart_4995378 : Nat := 118140960795 + 4995378 * 2 ^ 59
def prefixEnd_4995378 : Nat := 4983230072969 + 3 ^ 40 * 4995378 * 2
def baseEnd_4995378 : Nat := 855009988298487264767227

theorem tailTrace_4995378 : CollatzResearch.WordTrace tailWord_4995378 prefixEnd_4995378 855009988298487264767227 := by
  unfold tailWord_4995378
  simp only [CollatzResearch.WordTrace]
  refine ⟨45549100924151530871338697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121464269131070748990236525 45549100924151530871338697)
  ·
    refine ⟨34161825693113648153504023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45549100924151530871338697 34161825693113648153504023)
    ·
      refine ⟨51242738539670472230256035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34161825693113648153504023 51242738539670472230256035)
      ·
        refine ⟨76864107809505708345384053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51242738539670472230256035 76864107809505708345384053)
        ·
          refine ⟨7206010107141160157379755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76864107809505708345384053 7206010107141160157379755)
          ·
            refine ⟨10809015160711740236069633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7206010107141160157379755 10809015160711740236069633)
            ·
              refine ⟨8106761370533805177052225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10809015160711740236069633 8106761370533805177052225)
              ·
                refine ⟨6080071027900353882789169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8106761370533805177052225 6080071027900353882789169)
                ·
                  refine ⟨4560053270925265412091877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6080071027900353882789169 4560053270925265412091877)
                  ·
                    refine ⟨855009988298487264767227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560053270925265412091877 855009988298487264767227)
                    ·
                      rfl

theorem cell23_4995378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_4995378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995378 prefixEnd_4995378 := by exact prefixLift 4995378
  have htrace : WordTrace (prefixWord ++ tailWord_4995378) baseStart_4995378 baseEnd_4995378 := by
    simpa [prefixWord, tailWord_4995378, baseEnd_4995378] using wordTrace_append hprefix tailTrace_4995378
  have hstable : (prefixWord ++ tailWord_4995378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995378).length < 2 ^ (prefixWord ++ tailWord_4995378).sum := by decide
  have hdescent : baseEnd_4995378 < baseStart_4995378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995397 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_4995397 : Nat := 118140960795 + 4995397 * 2 ^ 59
def prefixEnd_4995397 : Nat := 4983230072969 + 3 ^ 40 * 4995397 * 2
def baseEnd_4995397 : Nat := 2565039721027897219964093

theorem tailTrace_4995397 : CollatzResearch.WordTrace tailWord_4995397 prefixEnd_4995397 2565039721027897219964093 := by
  unfold tailWord_4995397
  simp only [CollatzResearch.WordTrace]
  refine ⟨182197096683537289730296445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121464731122358193153530963 182197096683537289730296445)
  ·
    refine ⟨68323911256326483648861167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182197096683537289730296445 68323911256326483648861167)
    ·
      refine ⟨102485866884489725473291751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68323911256326483648861167 102485866884489725473291751)
      ·
        refine ⟨153728800326734588209937627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102485866884489725473291751 153728800326734588209937627)
        ·
          refine ⟨230593200490101882314906441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153728800326734588209937627 230593200490101882314906441)
          ·
            refine ⟨172944900367576411736179831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230593200490101882314906441 172944900367576411736179831)
            ·
              refine ⟨259417350551364617604269747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172944900367576411736179831 259417350551364617604269747)
              ·
                refine ⟨389126025827046926406404621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259417350551364617604269747 389126025827046926406404621)
                ·
                  refine ⟨145922259685142597402401733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389126025827046926406404621 145922259685142597402401733)
                  ·
                    refine ⟨27360423690964237012950325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145922259685142597402401733 27360423690964237012950325)
                    ·
                      refine ⟨2565039721027897219964093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27360423690964237012950325 2565039721027897219964093)
                      ·
                        rfl

theorem cell23_4995397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_4995397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995397 prefixEnd_4995397 := by exact prefixLift 4995397
  have htrace : WordTrace (prefixWord ++ tailWord_4995397) baseStart_4995397 baseEnd_4995397 := by
    simpa [prefixWord, tailWord_4995397, baseEnd_4995397] using wordTrace_append hprefix tailTrace_4995397
  have hstable : (prefixWord ++ tailWord_4995397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995397).length < 2 ^ (prefixWord ++ tailWord_4995397).sum := by decide
  have hdescent : baseEnd_4995397 < baseStart_4995397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995417 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 3, 8]
def baseStart_4995417 : Nat := 118140960795 + 4995417 * 2 ^ 59
def prefixEnd_4995417 : Nat := 4983230072969 + 3 ^ 40 * 4995417 * 2
def baseEnd_4995417 : Nat := 855016663546995713904667

theorem tailTrace_4995417 : CollatzResearch.WordTrace tailWord_4995417 prefixEnd_4995417 855016663546995713904667 := by
  unfold tailWord_4995417
  simp only [CollatzResearch.WordTrace]
  refine ⟨182197826143464833146024505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121465217428976555430683003 182197826143464833146024505)
  ·
    refine ⟨136648369607598624859518379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182197826143464833146024505 136648369607598624859518379)
    ·
      refine ⟨204972554411397937289277569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136648369607598624859518379 204972554411397937289277569)
      ·
        refine ⟨153729415808548452966958177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204972554411397937289277569 153729415808548452966958177)
        ·
          refine ⟨115297061856411339725218633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153729415808548452966958177 115297061856411339725218633)
          ·
            refine ⟨86472796392308504793913975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115297061856411339725218633 86472796392308504793913975)
            ·
              refine ⟨129709194588462757190870963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86472796392308504793913975 129709194588462757190870963)
              ·
                refine ⟨194563791882694135786306445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129709194588462757190870963 194563791882694135786306445)
                ·
                  refine ⟨72961421956010300919864917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194563791882694135786306445 72961421956010300919864917)
                  ·
                    refine ⟨855016663546995713904667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72961421956010300919864917 855016663546995713904667)
                    ·
                      rfl

theorem cell23_4995417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_4995417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995417 prefixEnd_4995417 := by exact prefixLift 4995417
  have htrace : WordTrace (prefixWord ++ tailWord_4995417) baseStart_4995417 baseEnd_4995417 := by
    simpa [prefixWord, tailWord_4995417, baseEnd_4995417] using wordTrace_append hprefix tailTrace_4995417
  have hstable : (prefixWord ++ tailWord_4995417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995417).length < 2 ^ (prefixWord ++ tailWord_4995417).sum := by decide
  have hdescent : baseEnd_4995417 < baseStart_4995417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995428 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 1, 3, 2]
def baseStart_4995428 : Nat := 118140960795 + 4995428 * 2 ^ 59
def prefixEnd_4995428 : Nat := 4983230072969 + 3 ^ 40 * 4995428 * 2
def baseEnd_4995428 : Nat := 2565055638928186598676451

theorem tailTrace_4995428 : CollatzResearch.WordTrace tailWord_4995428 prefixEnd_4995428 2565055638928186598676451 := by
  unfold tailWord_4995428
  simp only [CollatzResearch.WordTrace]
  refine ⟨91099113673212491012337469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121465484897616654683116625 91099113673212491012337469)
  ·
    refine ⟨34162167627454684129626551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91099113673212491012337469 34162167627454684129626551)
    ·
      refine ⟨51243251441182026194439827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34162167627454684129626551 51243251441182026194439827)
      ·
        refine ⟨76864877161773039291659741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51243251441182026194439827 76864877161773039291659741)
        ·
          refine ⟨28824328935664889734372403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76864877161773039291659741 28824328935664889734372403)
          ·
            refine ⟨43236493403497334601558605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28824328935664889734372403 43236493403497334601558605)
            ·
              refine ⟨16213685026311500475584477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43236493403497334601558605 16213685026311500475584477)
              ·
                refine ⟨6080131884866812678344179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16213685026311500475584477 6080131884866812678344179)
                ·
                  refine ⟨9120197827300219017516269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6080131884866812678344179 9120197827300219017516269)
                  ·
                    refine ⟨3420074185237582131568601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9120197827300219017516269 3420074185237582131568601)
                    ·
                      refine ⟨2565055638928186598676451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420074185237582131568601 2565055638928186598676451)
                      ·
                        rfl

theorem cell23_4995428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_4995428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995428 prefixEnd_4995428 := by exact prefixLift 4995428
  have htrace : WordTrace (prefixWord ++ tailWord_4995428) baseStart_4995428 baseEnd_4995428 := by
    simpa [prefixWord, tailWord_4995428, baseEnd_4995428] using wordTrace_append hprefix tailTrace_4995428
  have hstable : (prefixWord ++ tailWord_4995428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995428).length < 2 ^ (prefixWord ++ tailWord_4995428).sum := by decide
  have hdescent : baseEnd_4995428 < baseStart_4995428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995464 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 7]
def baseStart_4995464 : Nat := 118140960795 + 4995464 * 2 ^ 59
def prefixEnd_4995464 : Nat := 4983230072969 + 3 ^ 40 * 4995464 * 2
def baseEnd_4995464 : Nat := 285008236025749828647365

theorem tailTrace_4995464 : CollatzResearch.WordTrace tailWord_4995464 prefixEnd_4995464 285008236025749828647365 := by
  unfold tailWord_4995464
  simp only [CollatzResearch.WordTrace]
  refine ⟨91099770187147280086492723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121466360249529706781990297 91099770187147280086492723)
  ·
    refine ⟨136649655280720920129739085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91099770187147280086492723 136649655280720920129739085)
    ·
      refine ⟨51243620730270345048652157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136649655280720920129739085 51243620730270345048652157)
      ·
        refine ⟨19216357773851379393244559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51243620730270345048652157 19216357773851379393244559)
        ·
          refine ⟨28824536660777069089866839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19216357773851379393244559 28824536660777069089866839)
          ·
            refine ⟨43236804991165603634800259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28824536660777069089866839 43236804991165603634800259)
            ·
              refine ⟨64855207486748405452200389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43236804991165603634800259 64855207486748405452200389)
              ·
                refine ⟨12160351403765326022287573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64855207486748405452200389 12160351403765326022287573)
                ·
                  refine ⟨285008236025749828647365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12160351403765326022287573 285008236025749828647365)
                  ·
                    rfl

theorem cell23_4995464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 7].length) (baseStart_4995464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995464 prefixEnd_4995464 := by exact prefixLift 4995464
  have htrace : WordTrace (prefixWord ++ tailWord_4995464) baseStart_4995464 baseEnd_4995464 := by
    simpa [prefixWord, tailWord_4995464, baseEnd_4995464] using wordTrace_append hprefix tailTrace_4995464
  have hstable : (prefixWord ++ tailWord_4995464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995464).length < 2 ^ (prefixWord ++ tailWord_4995464).sum := by decide
  have hdescent : baseEnd_4995464 < baseStart_4995464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995509 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_4995509 : Nat := 118140960795 + 4995509 * 2 ^ 59
def prefixEnd_4995509 : Nat := 4983230072969 + 3 ^ 40 * 4995509 * 2
def baseEnd_4995509 : Nat := 2565097230861200781763579

theorem tailTrace_4995509 : CollatzResearch.WordTrace tailWord_4995509 prefixEnd_4995509 2565097230861200781763579 := by
  unfold tailWord_4995509
  simp only [CollatzResearch.WordTrace]
  refine ⟨182201181659131532858373581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121467454439421021905582387 182201181659131532858373581)
  ·
    refine ⟨68325443122174324821890093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182201181659131532858373581 68325443122174324821890093)
    ·
      refine ⟨25622041170815371808208785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68325443122174324821890093 25622041170815371808208785)
      ·
        refine ⟨19216530878111528856156589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25622041170815371808208785 19216530878111528856156589)
        ·
          refine ⟨7206199079291823321058721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19216530878111528856156589 7206199079291823321058721)
          ·
            refine ⟨5404649309468867490794041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7206199079291823321058721 5404649309468867490794041)
            ·
              refine ⟨4053486982101650618095531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5404649309468867490794041 4053486982101650618095531)
              ·
                refine ⟨6080230473152475927143297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053486982101650618095531 6080230473152475927143297)
                ·
                  refine ⟨4560172854864356945357473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6080230473152475927143297 4560172854864356945357473)
                  ·
                    refine ⟨3420129641148267709018105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4560172854864356945357473 3420129641148267709018105)
                    ·
                      refine ⟨2565097230861200781763579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420129641148267709018105 2565097230861200781763579)
                      ·
                        rfl

theorem cell23_4995509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_4995509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995509 prefixEnd_4995509 := by exact prefixLift 4995509
  have htrace : WordTrace (prefixWord ++ tailWord_4995509) baseStart_4995509 baseEnd_4995509 := by
    simpa [prefixWord, tailWord_4995509, baseEnd_4995509] using wordTrace_append hprefix tailTrace_4995509
  have hstable : (prefixWord ++ tailWord_4995509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995509).length < 2 ^ (prefixWord ++ tailWord_4995509).sum := by decide
  have hdescent : baseEnd_4995509 < baseStart_4995509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995514 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_4995514 : Nat := 118140960795 + 4995514 * 2 ^ 59
def prefixEnd_4995514 : Nat := 4983230072969 + 3 ^ 40 * 4995514 * 2
def baseEnd_4995514 : Nat := 2565099798264473262201055

theorem tailTrace_4995514 : CollatzResearch.WordTrace tailWord_4995514 prefixEnd_4995514 2565099798264473262201055 := by
  unfold tailWord_4995514
  simp only [CollatzResearch.WordTrace]
  refine ⟨45550341006028354678076399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121467576016075612474870397 45550341006028354678076399)
  ·
    refine ⟨68325511509042532017114599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45550341006028354678076399 68325511509042532017114599)
    ·
      refine ⟨102488267263563798025671899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68325511509042532017114599 102488267263563798025671899)
      ·
        refine ⟨153732400895345697038507849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102488267263563798025671899 153732400895345697038507849)
        ·
          refine ⟨115299300671509272778880887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153732400895345697038507849 115299300671509272778880887)
          ·
            refine ⟨172948951007263909168321331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115299300671509272778880887 172948951007263909168321331)
            ·
              refine ⟨259423426510895863752481997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172948951007263909168321331 259423426510895863752481997)
              ·
                refine ⟨97283784941585948907180749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259423426510895863752481997 97283784941585948907180749)
                ·
                  refine ⟨36481419353094730840192781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97283784941585948907180749 36481419353094730840192781)
                  ·
                    refine ⟨13680532257410524065072293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36481419353094730840192781 13680532257410524065072293)
                    ·
                      refine ⟨2565099798264473262201055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13680532257410524065072293 2565099798264473262201055)
                      ·
                        rfl

theorem cell23_4995514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_4995514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995514 prefixEnd_4995514 := by exact prefixLift 4995514
  have htrace : WordTrace (prefixWord ++ tailWord_4995514) baseStart_4995514 baseEnd_4995514 := by
    simpa [prefixWord, tailWord_4995514, baseEnd_4995514] using wordTrace_append hprefix tailTrace_4995514
  have hstable : (prefixWord ++ tailWord_4995514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995514).length < 2 ^ (prefixWord ++ tailWord_4995514).sum := by decide
  have hdescent : baseEnd_4995514 < baseStart_4995514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995531 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 4, 4, 2]
def baseStart_4995531 : Nat := 118140960795 + 4995531 * 2 ^ 59
def prefixEnd_4995531 : Nat := 4983230072969 + 3 ^ 40 * 4995531 * 2
def baseEnd_4995531 : Nat := 2565108527435599695688477

theorem tailTrace_4995531 : CollatzResearch.WordTrace tailWord_4995531 prefixEnd_4995531 2565108527435599695688477 := by
  unfold tailWord_4995531
  simp only [CollatzResearch.WordTrace]
  refine ⟨182201984065051830615674447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121467989376701220410449631 182201984065051830615674447)
  ·
    refine ⟨273302976097577745923511671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182201984065051830615674447 273302976097577745923511671)
    ·
      refine ⟨409954464146366618885267507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273302976097577745923511671 409954464146366618885267507)
      ·
        refine ⟨614931696219549928327901261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409954464146366618885267507 614931696219549928327901261)
        ·
          refine ⟨230599386082331223122962973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 614931696219549928327901261 230599386082331223122962973)
          ·
            refine ⟨86474769780874208671111115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230599386082331223122962973 86474769780874208671111115)
            ·
              refine ⟨129712154671311313006666673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86474769780874208671111115 129712154671311313006666673)
              ·
                refine ⟨97284116003483484755000005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129712154671311313006666673 97284116003483484755000005)
                ·
                  refine ⟨18240771750653153391562501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97284116003483484755000005 18240771750653153391562501)
                  ·
                    refine ⟨3420144703247466260917969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18240771750653153391562501 3420144703247466260917969)
                    ·
                      refine ⟨2565108527435599695688477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420144703247466260917969 2565108527435599695688477)
                      ·
                        rfl

theorem cell23_4995531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 4, 2].length) (baseStart_4995531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995531 prefixEnd_4995531 := by exact prefixLift 4995531
  have htrace : WordTrace (prefixWord ++ tailWord_4995531) baseStart_4995531 baseEnd_4995531 := by
    simpa [prefixWord, tailWord_4995531, baseEnd_4995531] using wordTrace_append hprefix tailTrace_4995531
  have hstable : (prefixWord ++ tailWord_4995531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995531).length < 2 ^ (prefixWord ++ tailWord_4995531).sum := by decide
  have hdescent : baseEnd_4995531 < baseStart_4995531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995544 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_4995544 : Nat := 118140960795 + 4995544 * 2 ^ 59
def prefixEnd_4995544 : Nat := 4983230072969 + 3 ^ 40 * 4995544 * 2
def baseEnd_4995544 : Nat := 2565115202684108144825917

theorem tailTrace_4995544 : CollatzResearch.WordTrace tailWord_4995544 prefixEnd_4995544 2565115202684108144825917 := by
  unfold tailWord_4995544
  simp only [CollatzResearch.WordTrace]
  refine ⟨91101229107002366917948843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121468305476003155890598457 91101229107002366917948843)
  ·
    refine ⟨136651843660503550376923265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91101229107002366917948843 136651843660503550376923265)
    ·
      refine ⟨102488882745377662782692449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136651843660503550376923265 102488882745377662782692449)
      ·
        refine ⟨76866662059033247087019337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102488882745377662782692449 76866662059033247087019337)
        ·
          refine ⟨57649996544274935315264503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76866662059033247087019337 57649996544274935315264503)
          ·
            refine ⟨86474994816412402972896755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57649996544274935315264503 86474994816412402972896755)
            ·
              refine ⟨129712492224618604459345133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86474994816412402972896755 129712492224618604459345133)
              ·
                refine ⟨48642184584231976672254425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129712492224618604459345133 48642184584231976672254425)
                ·
                  refine ⟨36481638438173982504190819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48642184584231976672254425 36481638438173982504190819)
                  ·
                    refine ⟨54722457657260973756286229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36481638438173982504190819 54722457657260973756286229)
                    ·
                      refine ⟨2565115202684108144825917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54722457657260973756286229 2565115202684108144825917)
                      ·
                        rfl

theorem cell23_4995544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_4995544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995544 prefixEnd_4995544 := by exact prefixLift 4995544
  have htrace : WordTrace (prefixWord ++ tailWord_4995544) baseStart_4995544 baseEnd_4995544 := by
    simpa [prefixWord, tailWord_4995544, baseEnd_4995544] using wordTrace_append hprefix tailTrace_4995544
  have hstable : (prefixWord ++ tailWord_4995544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995544).length < 2 ^ (prefixWord ++ tailWord_4995544).sum := by decide
  have hdescent : baseEnd_4995544 < baseStart_4995544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995565 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4995565 : Nat := 118140960795 + 4995565 * 2 ^ 59
def prefixEnd_4995565 : Nat := 4983230072969 + 3 ^ 40 * 4995565 * 2
def baseEnd_4995565 : Nat := 2565125985777852562663321

theorem tailTrace_4995565 : CollatzResearch.WordTrace tailWord_4995565 prefixEnd_4995565 2565125985777852562663321 := by
  unfold tailWord_4995565
  simp only [CollatzResearch.WordTrace]
  refine ⟨182203224146928654422412149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121468816097952436281608099 182203224146928654422412149)
  ·
    refine ⟨17081552263774561352101139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182203224146928654422412149 17081552263774561352101139)
    ·
      refine ⟨25622328395661842028151709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17081552263774561352101139 25622328395661842028151709)
      ·
        refine ⟨9608373148373190760556891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25622328395661842028151709 9608373148373190760556891)
        ·
          refine ⟨14412559722559786140835337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9608373148373190760556891 14412559722559786140835337)
          ·
            refine ⟨10809419791919839605626503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14412559722559786140835337 10809419791919839605626503)
            ·
              refine ⟨16214129687879759408439755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10809419791919839605626503 16214129687879759408439755)
              ·
                refine ⟨24321194531819639112659633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16214129687879759408439755 24321194531819639112659633)
                ·
                  refine ⟨18240895898864729334494725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24321194531819639112659633 18240895898864729334494725)
                  ·
                    refine ⟨3420167981037136750217761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18240895898864729334494725 3420167981037136750217761)
                    ·
                      refine ⟨2565125985777852562663321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420167981037136750217761 2565125985777852562663321)
                      ·
                        rfl

theorem cell23_4995565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4995565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995565 prefixEnd_4995565 := by exact prefixLift 4995565
  have htrace : WordTrace (prefixWord ++ tailWord_4995565) baseStart_4995565 baseEnd_4995565 := by
    simpa [prefixWord, tailWord_4995565, baseEnd_4995565] using wordTrace_append hprefix tailTrace_4995565
  have hstable : (prefixWord ++ tailWord_4995565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995565).length < 2 ^ (prefixWord ++ tailWord_4995565).sum := by decide
  have hdescent : baseEnd_4995565 < baseStart_4995565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995585 : List Nat := [1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_4995585 : Nat := 118140960795 + 4995585 * 2 ^ 59
def prefixEnd_4995585 : Nat := 4983230072969 + 3 ^ 40 * 4995585 * 2
def baseEnd_4995585 : Nat := 2565136255390942484413229

theorem tailTrace_4995585 : CollatzResearch.WordTrace tailWord_4995585 prefixEnd_4995585 2565136255390942484413229 := by
  unfold tailWord_4995585
  simp only [CollatzResearch.WordTrace]
  refine ⟨182203953606856197838140209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121469302404570798558760139 182203953606856197838140209)
  ·
    refine ⟨136652965205142148378605157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182203953606856197838140209 136652965205142148378605157)
    ·
      refine ⟨25622430975964152820988467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136652965205142148378605157 25622430975964152820988467)
      ·
        refine ⟨38433646463946229231482701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25622430975964152820988467 38433646463946229231482701)
        ·
          refine ⟨14412617423979835961806013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38433646463946229231482701 14412617423979835961806013)
          ·
            refine ⟨5404731533992438485677255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14412617423979835961806013 5404731533992438485677255)
            ·
              refine ⟨8107097300988657728515883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404731533992438485677255 8107097300988657728515883)
              ·
                refine ⟨12160645951482986592773825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8107097300988657728515883 12160645951482986592773825)
                ·
                  refine ⟨9120484463612239944580369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12160645951482986592773825 9120484463612239944580369)
                  ·
                    refine ⟨6840363347709179958435277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9120484463612239944580369 6840363347709179958435277)
                    ·
                      refine ⟨2565136255390942484413229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6840363347709179958435277 2565136255390942484413229)
                      ·
                        rfl

theorem cell23_4995585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_4995585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995585 prefixEnd_4995585 := by exact prefixLift 4995585
  have htrace : WordTrace (prefixWord ++ tailWord_4995585) baseStart_4995585 baseEnd_4995585 := by
    simpa [prefixWord, tailWord_4995585, baseEnd_4995585] using wordTrace_append hprefix tailTrace_4995585
  have hstable : (prefixWord ++ tailWord_4995585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995585).length < 2 ^ (prefixWord ++ tailWord_4995585).sum := by decide
  have hdescent : baseEnd_4995585 < baseStart_4995585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995621 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_4995621 : Nat := 118140960795 + 4995621 * 2 ^ 59
def prefixEnd_4995621 : Nat := 4983230072969 + 3 ^ 40 * 4995621 * 2
def baseEnd_4995621 : Nat := 2565154740694504343563063

theorem tailTrace_4995621 : CollatzResearch.WordTrace tailWord_4995621 prefixEnd_4995621 2565154740694504343563063 := by
  unfold tailWord_4995621
  simp only [CollatzResearch.WordTrace]
  refine ⟨182205266634725775986450717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121470177756483850657633811 182205266634725775986450717)
  ·
    refine ⟨68326974988022165994919019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182205266634725775986450717 68326974988022165994919019)
    ·
      refine ⟨102490462482033248992378529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68326974988022165994919019 102490462482033248992378529)
      ·
        refine ⟨76867846861524936744283897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102490462482033248992378529 76867846861524936744283897)
        ·
          refine ⟨57650885146143702558212923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76867846861524936744283897 57650885146143702558212923)
          ·
            refine ⟨86476327719215553837319385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57650885146143702558212923 86476327719215553837319385)
            ·
              refine ⟨64857245789411665377989539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86476327719215553837319385 64857245789411665377989539)
              ·
                refine ⟨97285868684117498066984309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64857245789411665377989539 97285868684117498066984309)
                ·
                  refine ⟨9120550189136015443779779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97285868684117498066984309 9120550189136015443779779)
                  ·
                    refine ⟨13680825283704023165669669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9120550189136015443779779 13680825283704023165669669)
                    ·
                      refine ⟨2565154740694504343563063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13680825283704023165669669 2565154740694504343563063)
                      ·
                        rfl

theorem cell23_4995621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_4995621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995621 prefixEnd_4995621 := by exact prefixLift 4995621
  have htrace : WordTrace (prefixWord ++ tailWord_4995621) baseStart_4995621 baseEnd_4995621 := by
    simpa [prefixWord, tailWord_4995621, baseEnd_4995621] using wordTrace_append hprefix tailTrace_4995621
  have hstable : (prefixWord ++ tailWord_4995621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995621).length < 2 ^ (prefixWord ++ tailWord_4995621).sum := by decide
  have hdescent : baseEnd_4995621 < baseStart_4995621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995641 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4995641 : Nat := 118140960795 + 4995641 * 2 ^ 59
def prefixEnd_4995641 : Nat := 4983230072969 + 3 ^ 40 * 4995641 * 2
def baseEnd_4995641 : Nat := 2565165010307594265312971

theorem tailTrace_4995641 : CollatzResearch.WordTrace tailWord_4995641 prefixEnd_4995641 2565165010307594265312971 := by
  unfold tailWord_4995641
  simp only [CollatzResearch.WordTrace]
  refine ⟨182205996094653319402178777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121470664063102212934785851 182205996094653319402178777)
  ·
    refine ⟨136654497070989989551634083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182205996094653319402178777 136654497070989989551634083)
    ·
      refine ⟨204981745606484984327451125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136654497070989989551634083 204981745606484984327451125)
      ·
        refine ⟨19217038650607967280698543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204981745606484984327451125 19217038650607967280698543)
        ·
          refine ⟨28825557975911950921047815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19217038650607967280698543 28825557975911950921047815)
          ·
            refine ⟨43238336963867926381571723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28825557975911950921047815 43238336963867926381571723)
            ·
              refine ⟨64857505445801889572357585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43238336963867926381571723 64857505445801889572357585)
              ·
                refine ⟨48643129084351417179268189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64857505445801889572357585 48643129084351417179268189)
                ·
                  refine ⟨18241173406631781442225571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48643129084351417179268189 18241173406631781442225571)
                  ·
                    refine ⟨27361760109947672163338357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18241173406631781442225571 27361760109947672163338357)
                    ·
                      refine ⟨2565165010307594265312971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27361760109947672163338357 2565165010307594265312971)
                      ·
                        rfl

theorem cell23_4995641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4995641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995641 prefixEnd_4995641 := by exact prefixLift 4995641
  have htrace : WordTrace (prefixWord ++ tailWord_4995641) baseStart_4995641 baseEnd_4995641 := by
    simpa [prefixWord, tailWord_4995641, baseEnd_4995641] using wordTrace_append hprefix tailTrace_4995641
  have hstable : (prefixWord ++ tailWord_4995641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995641).length < 2 ^ (prefixWord ++ tailWord_4995641).sum := by decide
  have hdescent : baseEnd_4995641 < baseStart_4995641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995649 : List Nat := [1, 2, 5, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_4995649 : Nat := 118140960795 + 4995649 * 2 ^ 59
def prefixEnd_4995649 : Nat := 4983230072969 + 3 ^ 40 * 4995649 * 2
def baseEnd_4995649 : Nat := 2565169118152830234012935

theorem tailTrace_4995649 : CollatzResearch.WordTrace tailWord_4995649 prefixEnd_4995649 2565169118152830234012935 := by
  unfold tailWord_4995649
  simp only [CollatzResearch.WordTrace]
  refine ⟨182206287878624336768470001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121470858585749557845646667 182206287878624336768470001)
  ·
    refine ⟨136654715908968252576352501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182206287878624336768470001 136654715908968252576352501)
    ·
      refine ⟨12811379616465773679033047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136654715908968252576352501 12811379616465773679033047)
      ·
        refine ⟨19217069424698660518549571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12811379616465773679033047 19217069424698660518549571)
        ·
          refine ⟨28825604137047990777824357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19217069424698660518549571 28825604137047990777824357)
          ·
            refine ⟨5404800775696498270842067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28825604137047990777824357 5404800775696498270842067)
            ·
              refine ⟨8107201163544747406263101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404800775696498270842067 8107201163544747406263101)
              ·
                refine ⟨3040200436329280277348663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8107201163544747406263101 3040200436329280277348663)
                ·
                  refine ⟨4560300654493920416022995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040200436329280277348663 4560300654493920416022995)
                  ·
                    refine ⟨6840450981740880624034493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4560300654493920416022995 6840450981740880624034493)
                    ·
                      refine ⟨2565169118152830234012935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6840450981740880624034493 2565169118152830234012935)
                      ·
                        rfl

theorem cell23_4995649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_4995649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995649 prefixEnd_4995649 := by exact prefixLift 4995649
  have htrace : WordTrace (prefixWord ++ tailWord_4995649) baseStart_4995649 baseEnd_4995649 := by
    simpa [prefixWord, tailWord_4995649, baseEnd_4995649] using wordTrace_append hprefix tailTrace_4995649
  have hstable : (prefixWord ++ tailWord_4995649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995649).length < 2 ^ (prefixWord ++ tailWord_4995649).sum := by decide
  have hdescent : baseEnd_4995649 < baseStart_4995649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995651 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4]
def baseStart_4995651 : Nat := 118140960795 + 4995651 * 2 ^ 59
def prefixEnd_4995651 : Nat := 4983230072969 + 3 ^ 40 * 4995651 * 2
def baseEnd_4995651 : Nat := 2565170145114139226187925

theorem tailTrace_4995651 : CollatzResearch.WordTrace tailWord_4995651 prefixEnd_4995651 2565170145114139226187925 := by
  unfold tailWord_4995651
  simp only [CollatzResearch.WordTrace]
  refine ⟨182206360824617091110042807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121470907216411394073361871 182206360824617091110042807)
  ·
    refine ⟨273309541236925636665064211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182206360824617091110042807 273309541236925636665064211)
    ·
      refine ⟨409964311855388454997596317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273309541236925636665064211 409964311855388454997596317)
      ·
        refine ⟨153736616945770670624098619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409964311855388454997596317 153736616945770670624098619)
        ·
          refine ⟨230604925418656005936147929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153736616945770670624098619 230604925418656005936147929)
          ·
            refine ⟨172953694063992004452110947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230604925418656005936147929 172953694063992004452110947)
            ·
              refine ⟨259430541095988006678166421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172953694063992004452110947 259430541095988006678166421)
              ·
                refine ⟨12160806613874437813039051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 259430541095988006678166421 12160806613874437813039051)
                ·
                  refine ⟨18241209920811656719558577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12160806613874437813039051 18241209920811656719558577)
                  ·
                    refine ⟨13680907440608742539668933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18241209920811656719558577 13680907440608742539668933)
                    ·
                      refine ⟨2565170145114139226187925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13680907440608742539668933 2565170145114139226187925)
                      ·
                        rfl

theorem cell23_4995651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_4995651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995651 prefixEnd_4995651 := by exact prefixLift 4995651
  have htrace : WordTrace (prefixWord ++ tailWord_4995651) baseStart_4995651 baseEnd_4995651 := by
    simpa [prefixWord, tailWord_4995651, baseEnd_4995651] using wordTrace_append hprefix tailTrace_4995651
  have hstable : (prefixWord ++ tailWord_4995651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995651).length < 2 ^ (prefixWord ++ tailWord_4995651).sum := by decide
  have hdescent : baseEnd_4995651 < baseStart_4995651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995658 : List Nat := [3, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_4995658 : Nat := 118140960795 + 4995658 * 2 ^ 59
def prefixEnd_4995658 : Nat := 4983230072969 + 3 ^ 40 * 4995658 * 2
def baseEnd_4995658 : Nat := 2565173739478720698800393

theorem tailTrace_4995658 : CollatzResearch.WordTrace tailWord_4995658 prefixEnd_4995658 2565173739478720698800393 := by
  unfold tailWord_4995658
  simp only [CollatzResearch.WordTrace]
  refine ⟨45551654033897932826386907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121471077423727820870365085 45551654033897932826386907)
  ·
    refine ⟨68327481050846899239580361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45551654033897932826386907 68327481050846899239580361)
    ·
      refine ⟨51245610788135174429685271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68327481050846899239580361 51245610788135174429685271)
      ·
        refine ⟨76868416182202761644527907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51245610788135174429685271 76868416182202761644527907)
        ·
          refine ⟨115302624273304142466791861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76868416182202761644527907 115302624273304142466791861)
          ·
            refine ⟨10809621025622263356261737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115302624273304142466791861 10809621025622263356261737)
            ·
              refine ⟨8107215769216697517196303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10809621025622263356261737 8107215769216697517196303)
              ·
                refine ⟨12160823653825046275794455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8107215769216697517196303 12160823653825046275794455)
                ·
                  refine ⟨18241235480737569413691683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12160823653825046275794455 18241235480737569413691683)
                  ·
                    refine ⟨27361853221106354120537525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18241235480737569413691683 27361853221106354120537525)
                    ·
                      refine ⟨2565173739478720698800393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27361853221106354120537525 2565173739478720698800393)
                      ·
                        rfl

theorem cell23_4995658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_4995658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995658 prefixEnd_4995658 := by exact prefixLift 4995658
  have htrace : WordTrace (prefixWord ++ tailWord_4995658) baseStart_4995658 baseEnd_4995658 := by
    simpa [prefixWord, tailWord_4995658, baseEnd_4995658] using wordTrace_append hprefix tailTrace_4995658
  have hstable : (prefixWord ++ tailWord_4995658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995658).length < 2 ^ (prefixWord ++ tailWord_4995658).sum := by decide
  have hdescent : baseEnd_4995658 < baseStart_4995658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995672 : List Nat := [2, 1, 2, 2, 1, 2, 2, 6, 1, 2, 2]
def baseStart_4995672 : Nat := 118140960795 + 4995672 * 2 ^ 59
def prefixEnd_4995672 : Nat := 4983230072969 + 3 ^ 40 * 4995672 * 2
def baseEnd_4995672 : Nat := 2565180928207883644025329

theorem tailTrace_4995672 : CollatzResearch.WordTrace tailWord_4995672 prefixEnd_4995672 2565180928207883644025329 := by
  unfold tailWord_4995672
  simp only [CollatzResearch.WordTrace]
  refine ⟨91103563378770505848278635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121471417838360674464371513 91103563378770505848278635)
  ·
    refine ⟨136655345068155758772417953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91103563378770505848278635 136655345068155758772417953)
    ·
      refine ⟨102491508801116819079313465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136655345068155758772417953 102491508801116819079313465)
      ·
        refine ⟨76868631600837614309485099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102491508801116819079313465 76868631600837614309485099)
        ·
          refine ⟨115302947401256421464227649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76868631600837614309485099 115302947401256421464227649)
          ·
            refine ⟨86477210550942316098170737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115302947401256421464227649 86477210550942316098170737)
            ·
              refine ⟨64857907913206737073628053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86477210550942316098170737 64857907913206737073628053)
              ·
                refine ⟨3040214433431565800326315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64857907913206737073628053 3040214433431565800326315)
                ·
                  refine ⟨4560321650147348700489473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040214433431565800326315 4560321650147348700489473)
                  ·
                    refine ⟨3420241237610511525367105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4560321650147348700489473 3420241237610511525367105)
                    ·
                      refine ⟨2565180928207883644025329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420241237610511525367105 2565180928207883644025329)
                      ·
                        rfl

theorem cell23_4995672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_4995672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995672 prefixEnd_4995672 := by exact prefixLift 4995672
  have htrace : WordTrace (prefixWord ++ tailWord_4995672) baseStart_4995672 baseEnd_4995672 := by
    simpa [prefixWord, tailWord_4995672, baseEnd_4995672] using wordTrace_append hprefix tailTrace_4995672
  have hstable : (prefixWord ++ tailWord_4995672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995672).length < 2 ^ (prefixWord ++ tailWord_4995672).sum := by decide
  have hdescent : baseEnd_4995672 < baseStart_4995672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995715 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 1, 3, 2]
def baseStart_4995715 : Nat := 118140960795 + 4995715 * 2 ^ 59
def prefixEnd_4995715 : Nat := 4983230072969 + 3 ^ 40 * 4995715 * 2
def baseEnd_4995715 : Nat := 2565203007876026975787631

theorem tailTrace_4995715 : CollatzResearch.WordTrace tailWord_4995715 prefixEnd_4995715 2565203007876026975787631 := by
  unfold tailWord_4995715
  simp only [CollatzResearch.WordTrace]
  refine ⟨182208695096385230040372599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121472463397590153360248399 182208695096385230040372599)
  ·
    refine ⟨273313042644577845060558899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182208695096385230040372599 273313042644577845060558899)
    ·
      refine ⟨409969563966866767590838349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273313042644577845060558899 409969563966866767590838349)
      ·
        refine ⟨153738586487575037846564381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409969563966866767590838349 153738586487575037846564381)
        ·
          refine ⟨57651969932840639192461643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153738586487575037846564381 57651969932840639192461643)
          ·
            refine ⟨86477954899260958788692465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57651969932840639192461643 86477954899260958788692465)
            ·
              refine ⟨64858466174445719091519349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86477954899260958788692465 64858466174445719091519349)
              ·
                refine ⟨6080481203854286164829939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64858466174445719091519349 6080481203854286164829939)
                ·
                  refine ⟨9120721805781429247244909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6080481203854286164829939 9120721805781429247244909)
                  ·
                    refine ⟨3420270677168035967716841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9120721805781429247244909 3420270677168035967716841)
                    ·
                      refine ⟨2565203007876026975787631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420270677168035967716841 2565203007876026975787631)
                      ·
                        rfl

theorem cell23_4995715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_4995715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995715 prefixEnd_4995715 := by exact prefixLift 4995715
  have htrace : WordTrace (prefixWord ++ tailWord_4995715) baseStart_4995715 baseEnd_4995715 := by
    simpa [prefixWord, tailWord_4995715, baseEnd_4995715] using wordTrace_append hprefix tailTrace_4995715
  have hstable : (prefixWord ++ tailWord_4995715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995715).length < 2 ^ (prefixWord ++ tailWord_4995715).sum := by decide
  have hdescent : baseEnd_4995715 < baseStart_4995715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995721 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 2, 6]
def baseStart_4995721 : Nat := 118140960795 + 4995721 * 2 ^ 59
def prefixEnd_4995721 : Nat := 4983230072969 + 3 ^ 40 * 4995721 * 2
def baseEnd_4995721 : Nat := 855068696253317984104201

theorem tailTrace_4995721 : CollatzResearch.WordTrace tailWord_4995721 prefixEnd_4995721 855068696253317984104201 := by
  unfold tailWord_4995721
  simp only [CollatzResearch.WordTrace]
  refine ⟨182208913934363493065091017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121472609289575662043394011 182208913934363493065091017)
  ·
    refine ⟨136656685450772619798818263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182208913934363493065091017 136656685450772619798818263)
    ·
      refine ⟨204985028176158929698227395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136656685450772619798818263 204985028176158929698227395)
      ·
        refine ⟨307477542264238394547341093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204985028176158929698227395 307477542264238394547341093)
        ·
          refine ⟨57652039174544698977626455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307477542264238394547341093 57652039174544698977626455)
          ·
            refine ⟨86478058761817048466439683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57652039174544698977626455 86478058761817048466439683)
            ·
              refine ⟨129717088142725572699659525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86478058761817048466439683 129717088142725572699659525)
              ·
                refine ⟨24321954026761044881186161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129717088142725572699659525 24321954026761044881186161)
                ·
                  refine ⟨18241465520070783660889621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24321954026761044881186161 18241465520070783660889621)
                  ·
                    refine ⟨855068696253317984104201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18241465520070783660889621 855068696253317984104201)
                    ·
                      rfl

theorem cell23_4995721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_4995721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995721 prefixEnd_4995721 := by exact prefixLift 4995721
  have htrace : WordTrace (prefixWord ++ tailWord_4995721) baseStart_4995721 baseEnd_4995721 := by
    simpa [prefixWord, tailWord_4995721, baseEnd_4995721] using wordTrace_append hprefix tailTrace_4995721
  have hstable : (prefixWord ++ tailWord_4995721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995721).length < 2 ^ (prefixWord ++ tailWord_4995721).sum := by decide
  have hdescent : baseEnd_4995721 < baseStart_4995721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995732 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4995732 : Nat := 118140960795 + 4995732 * 2 ^ 59
def prefixEnd_4995732 : Nat := 4983230072969 + 3 ^ 40 * 4995732 * 2
def baseEnd_4995732 : Nat := 2565211737047153409275053

theorem tailTrace_4995732 : CollatzResearch.WordTrace tailWord_4995732 prefixEnd_4995732 2565211737047153409275053 := by
  unfold tailWord_4995732
  simp only [CollatzResearch.WordTrace]
  refine ⟨91104657568661820971870725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121472876758215761295827633 91104657568661820971870725)
  ·
    refine ⟨17082123294124091432225761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91104657568661820971870725 17082123294124091432225761)
    ·
      refine ⟨12811592470593068574169321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17082123294124091432225761 12811592470593068574169321)
      ·
        refine ⟨9608694352944801430626991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12811592470593068574169321 9608694352944801430626991)
        ·
          refine ⟨14413041529417202145940487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9608694352944801430626991 14413041529417202145940487)
          ·
            refine ⟨21619562294125803218910731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14413041529417202145940487 21619562294125803218910731)
            ·
              refine ⟨32429343441188704828366097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21619562294125803218910731 32429343441188704828366097)
              ·
                refine ⟨24322007580891528621274573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32429343441188704828366097 24322007580891528621274573)
                ·
                  refine ⟨9120752842834323232977965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24322007580891528621274573 9120752842834323232977965)
                  ·
                    refine ⟨3420282316062871212366737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9120752842834323232977965 3420282316062871212366737)
                    ·
                      refine ⟨2565211737047153409275053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420282316062871212366737 2565211737047153409275053)
                      ·
                        rfl

theorem cell23_4995732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4995732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995732 prefixEnd_4995732 := by exact prefixLift 4995732
  have htrace : WordTrace (prefixWord ++ tailWord_4995732) baseStart_4995732 baseEnd_4995732 := by
    simpa [prefixWord, tailWord_4995732, baseEnd_4995732] using wordTrace_append hprefix tailTrace_4995732
  have hstable : (prefixWord ++ tailWord_4995732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995732).length < 2 ^ (prefixWord ++ tailWord_4995732).sum := by decide
  have hdescent : baseEnd_4995732 < baseStart_4995732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995748 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_4995748 : Nat := 118140960795 + 4995748 * 2 ^ 59
def prefixEnd_4995748 : Nat := 4983230072969 + 3 ^ 40 * 4995748 * 2
def baseEnd_4995748 : Nat := 2565219952737625346674979

theorem tailTrace_4995748 : CollatzResearch.WordTrace tailWord_4995748 prefixEnd_4995748 2565219952737625346674979 := by
  unfold tailWord_4995748
  simp only [CollatzResearch.WordTrace]
  refine ⟨91104949352632838338161949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121473265803510451117549265 91104949352632838338161949)
  ·
    refine ⟨34164356007237314376810731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91104949352632838338161949 34164356007237314376810731)
    ·
      refine ⟨51246534010855971565216097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34164356007237314376810731 51246534010855971565216097)
      ·
        refine ⟨38434900508141978673912073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51246534010855971565216097 38434900508141978673912073)
        ·
          refine ⟨28826175381106484005434055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38434900508141978673912073 28826175381106484005434055)
          ·
            refine ⟨43239263071659726008151083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28826175381106484005434055 43239263071659726008151083)
            ·
              refine ⟨64858894607489589012226625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43239263071659726008151083 64858894607489589012226625)
              ·
                refine ⟨48644170955617191759169969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64858894607489589012226625 48644170955617191759169969)
                ·
                  refine ⟨36483128216712893819377477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48644170955617191759169969 36483128216712893819377477)
                  ·
                    refine ⟨6840586540633667591133277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36483128216712893819377477 6840586540633667591133277)
                    ·
                      refine ⟨2565219952737625346674979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6840586540633667591133277 2565219952737625346674979)
                      ·
                        rfl

theorem cell23_4995748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_4995748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995748 prefixEnd_4995748 := by exact prefixLift 4995748
  have htrace : WordTrace (prefixWord ++ tailWord_4995748) baseStart_4995748 baseEnd_4995748 := by
    simpa [prefixWord, tailWord_4995748, baseEnd_4995748] using wordTrace_append hprefix tailTrace_4995748
  have hstable : (prefixWord ++ tailWord_4995748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995748).length < 2 ^ (prefixWord ++ tailWord_4995748).sum := by decide
  have hdescent : baseEnd_4995748 < baseStart_4995748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995766 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_4995766 : Nat := 118140960795 + 4995766 * 2 ^ 59
def prefixEnd_4995766 : Nat := 4983230072969 + 3 ^ 40 * 4995766 * 2
def baseEnd_4995766 : Nat := 2565229195389406276249897

theorem tailTrace_4995766 : CollatzResearch.WordTrace tailWord_4995766 prefixEnd_4995766 2565229195389406276249897 := by
  unfold tailWord_4995766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11388159701200029109404947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121473703479466977166986101 11388159701200029109404947)
  ·
    refine ⟨17082239551800043664107421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11388159701200029109404947 17082239551800043664107421)
    ·
      refine ⟨6405839831925016374040283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17082239551800043664107421 6405839831925016374040283)
      ·
        refine ⟨9608759747887524561060425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6405839831925016374040283 9608759747887524561060425)
        ·
          refine ⟨7206569810915643420795319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9608759747887524561060425 7206569810915643420795319)
          ·
            refine ⟨10809854716373465131192979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7206569810915643420795319 10809854716373465131192979)
            ·
              refine ⟨16214782074560197696789469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10809854716373465131192979 16214782074560197696789469)
              ·
                refine ⟨6080543277960074136296051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16214782074560197696789469 6080543277960074136296051)
                ·
                  refine ⟨9120814916940111204444077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6080543277960074136296051 9120814916940111204444077)
                  ·
                    refine ⟨3420305593852541701666529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9120814916940111204444077 3420305593852541701666529)
                    ·
                      refine ⟨2565229195389406276249897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420305593852541701666529 2565229195389406276249897)
                      ·
                        rfl

theorem cell23_4995766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_4995766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995766 prefixEnd_4995766 := by exact prefixLift 4995766
  have htrace : WordTrace (prefixWord ++ tailWord_4995766) baseStart_4995766 baseEnd_4995766 := by
    simpa [prefixWord, tailWord_4995766, baseEnd_4995766] using wordTrace_append hprefix tailTrace_4995766
  have hstable : (prefixWord ++ tailWord_4995766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995766).length < 2 ^ (prefixWord ++ tailWord_4995766).sum := by decide
  have hdescent : baseEnd_4995766 < baseStart_4995766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995781 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_4995781 : Nat := 118140960795 + 4995781 * 2 ^ 59
def prefixEnd_4995781 : Nat := 4983230072969 + 3 ^ 40 * 4995781 * 2
def baseEnd_4995781 : Nat := 855078965866407905854109

theorem tailTrace_4995781 : CollatzResearch.WordTrace tailWord_4995781 prefixEnd_4995781 855078965866407905854109 := by
  unfold tailWord_4995781
  simp only [CollatzResearch.WordTrace]
  refine ⟨182211102314146123312275197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121474068209430748874850131 182211102314146123312275197)
  ·
    refine ⟨68329163367804796242103199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182211102314146123312275197 68329163367804796242103199)
    ·
      refine ⟨102493745051707194363154799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68329163367804796242103199 102493745051707194363154799)
      ·
        refine ⟨153740617577560791544732199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102493745051707194363154799 153740617577560791544732199)
        ·
          refine ⟨230610926366341187317098299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153740617577560791544732199 230610926366341187317098299)
          ·
            refine ⟨345916389549511780975647449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230610926366341187317098299 345916389549511780975647449)
            ·
              refine ⟨259437292162133835731735587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345916389549511780975647449 259437292162133835731735587)
              ·
                refine ⟨389155938243200753597603381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259437292162133835731735587 389155938243200753597603381)
                ·
                  refine ⟨36483369210300070649775317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 389155938243200753597603381 36483369210300070649775317)
                  ·
                    refine ⟨855078965866407905854109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36483369210300070649775317 855078965866407905854109)
                    ·
                      rfl

theorem cell23_4995781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_4995781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995781 prefixEnd_4995781 := by exact prefixLift 4995781
  have htrace : WordTrace (prefixWord ++ tailWord_4995781) baseStart_4995781 baseEnd_4995781 := by
    simpa [prefixWord, tailWord_4995781, baseEnd_4995781] using wordTrace_append hprefix tailTrace_4995781
  have hstable : (prefixWord ++ tailWord_4995781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995781).length < 2 ^ (prefixWord ++ tailWord_4995781).sum := by decide
  have hdescent : baseEnd_4995781 < baseStart_4995781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995796 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4995796 : Nat := 118140960795 + 4995796 * 2 ^ 59
def prefixEnd_4995796 : Nat := 4983230072969 + 3 ^ 40 * 4995796 * 2
def baseEnd_4995796 : Nat := 2565244599809041158874759

theorem tailTrace_4995796 : CollatzResearch.WordTrace tailWord_4995796 prefixEnd_4995796 2565244599809041158874759 := by
  unfold tailWord_4995796
  simp only [CollatzResearch.WordTrace]
  refine ⟨91105824704545890437035621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121474432939394520582714161 91105824704545890437035621)
  ·
    refine ⟨17082342132102354456944179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91105824704545890437035621 17082342132102354456944179)
    ·
      refine ⟨25623513198153531685416269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17082342132102354456944179 25623513198153531685416269)
      ·
        refine ⟨9608817449307574382031101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25623513198153531685416269 9608817449307574382031101)
        ·
          refine ⟨3603306543490340393261663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9608817449307574382031101 3603306543490340393261663)
          ·
            refine ⟨5404959815235510589892495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603306543490340393261663 5404959815235510589892495)
            ·
              refine ⟨8107439722853265884838743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404959815235510589892495 8107439722853265884838743)
              ·
                refine ⟨12161159584279898827258115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8107439722853265884838743 12161159584279898827258115)
                ·
                  refine ⟨18241739376419848240887173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12161159584279898827258115 18241739376419848240887173)
                  ·
                    refine ⟨3420326133078721545166345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18241739376419848240887173 3420326133078721545166345)
                    ·
                      refine ⟨2565244599809041158874759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420326133078721545166345 2565244599809041158874759)
                      ·
                        rfl

theorem cell23_4995796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4995796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995796 prefixEnd_4995796 := by exact prefixLift 4995796
  have htrace : WordTrace (prefixWord ++ tailWord_4995796) baseStart_4995796 baseEnd_4995796 := by
    simpa [prefixWord, tailWord_4995796, baseEnd_4995796] using wordTrace_append hprefix tailTrace_4995796
  have hstable : (prefixWord ++ tailWord_4995796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995796).length < 2 ^ (prefixWord ++ tailWord_4995796).sum := by decide
  have hdescent : baseEnd_4995796 < baseStart_4995796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995869 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4995869 : Nat := 118140960795 + 4995869 * 2 ^ 59
def prefixEnd_4995869 : Nat := 4983230072969 + 3 ^ 40 * 4995869 * 2
def baseEnd_4995869 : Nat := 2565282083896819373261923

theorem tailTrace_4995869 : CollatzResearch.WordTrace tailWord_4995869 prefixEnd_4995869 2565282083896819373261923 := by
  unfold tailWord_4995869
  simp only [CollatzResearch.WordTrace]
  refine ⟨182214311937827314341478661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121476207958551542894319107 182214311937827314341478661)
  ·
    refine ⟨34165183488342621439027249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182214311937827314341478661 34165183488342621439027249)
    ·
      refine ⟨25623887616256966079270437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34165183488342621439027249 25623887616256966079270437)
      ·
        refine ⟨4804478928048181139863207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25623887616256966079270437 4804478928048181139863207)
        ·
          refine ⟨7206718392072271709794811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4804478928048181139863207 7206718392072271709794811)
          ·
            refine ⟨10810077588108407564692217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7206718392072271709794811 10810077588108407564692217)
            ·
              refine ⟨8107558191081305673519163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10810077588108407564692217 8107558191081305673519163)
              ·
                refine ⟨12161337286621958510278745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8107558191081305673519163 12161337286621958510278745)
                ·
                  refine ⟨9121002964966468882709059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12161337286621958510278745 9121002964966468882709059)
                  ·
                    refine ⟨13681504447449703324063589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9121002964966468882709059 13681504447449703324063589)
                    ·
                      refine ⟨2565282083896819373261923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13681504447449703324063589 2565282083896819373261923)
                      ·
                        rfl

theorem cell23_4995869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4995869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995869 prefixEnd_4995869 := by exact prefixLift 4995869
  have htrace : WordTrace (prefixWord ++ tailWord_4995869) baseStart_4995869 baseEnd_4995869 := by
    simpa [prefixWord, tailWord_4995869, baseEnd_4995869] using wordTrace_append hprefix tailTrace_4995869
  have hstable : (prefixWord ++ tailWord_4995869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995869).length < 2 ^ (prefixWord ++ tailWord_4995869).sum := by decide
  have hdescent : baseEnd_4995869 < baseStart_4995869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995872 : List Nat := [2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3]
def baseStart_4995872 : Nat := 118140960795 + 4995872 * 2 ^ 59
def prefixEnd_4995872 : Nat := 4983230072969 + 3 ^ 40 * 4995872 * 2
def baseEnd_4995872 : Nat := 2565283624338782861524409

theorem tailTrace_4995872 : CollatzResearch.WordTrace tailWord_4995872 prefixEnd_4995872 2565283624338782861524409 := by
  unfold tailWord_4995872
  simp only [CollatzResearch.WordTrace]
  refine ⟨91107210678408222926918935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121476280904544297235891913 91107210678408222926918935)
  ·
    refine ⟨136660816017612334390378403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91107210678408222926918935 136660816017612334390378403)
    ·
      refine ⟨204991224026418501585567605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136660816017612334390378403 204991224026418501585567605)
      ·
        refine ⟨19217927252476734523646963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204991224026418501585567605 19217927252476734523646963)
        ·
          refine ⟨28826890878715101785470445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19217927252476734523646963 28826890878715101785470445)
          ·
            refine ⟨10810084079518163169551417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28826890878715101785470445 10810084079518163169551417)
            ·
              refine ⟨8107563059638622377163563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10810084079518163169551417 8107563059638622377163563)
              ·
                refine ⟨12161344589457933565745345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8107563059638622377163563 12161344589457933565745345)
                ·
                  refine ⟨9121008442093450174309009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12161344589457933565745345 9121008442093450174309009)
                  ·
                    refine ⟨6840756331570087630731757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9121008442093450174309009 6840756331570087630731757)
                    ·
                      refine ⟨2565283624338782861524409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6840756331570087630731757 2565283624338782861524409)
                      ·
                        rfl

theorem cell23_4995872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_4995872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995872 prefixEnd_4995872 := by exact prefixLift 4995872
  have htrace : WordTrace (prefixWord ++ tailWord_4995872) baseStart_4995872 baseEnd_4995872 := by
    simpa [prefixWord, tailWord_4995872, baseEnd_4995872] using wordTrace_append hprefix tailTrace_4995872
  have hstable : (prefixWord ++ tailWord_4995872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995872).length < 2 ^ (prefixWord ++ tailWord_4995872).sum := by decide
  have hdescent : baseEnd_4995872 < baseStart_4995872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995925 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4995925 : Nat := 118140960795 + 4995925 * 2 ^ 59
def prefixEnd_4995925 : Nat := 4983230072969 + 3 ^ 40 * 4995925 * 2
def baseEnd_4995925 : Nat := 2565310838813471154161665

theorem tailTrace_4995925 : CollatzResearch.WordTrace tailWord_4995925 prefixEnd_4995925 2565310838813471154161665 := by
  unfold tailWord_4995925
  simp only [CollatzResearch.WordTrace]
  refine ⟨182216354425624435905517229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121477569617082957270344819 182216354425624435905517229)
  ·
    refine ⟨68331132909609163464568961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182216354425624435905517229 68331132909609163464568961)
    ·
      refine ⟨51248349682206872598426721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68331132909609163464568961 51248349682206872598426721)
      ·
        refine ⟨38436262261655154448820041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51248349682206872598426721 38436262261655154448820041)
        ·
          refine ⟨28827196696241365836615031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38436262261655154448820041 28827196696241365836615031)
          ·
            refine ⟨43240795044362048754922547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28827196696241365836615031 43240795044362048754922547)
            ·
              refine ⟨64861192566543073132383821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43240795044362048754922547 64861192566543073132383821)
              ·
                refine ⟨24322947212453652424643933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64861192566543073132383821 24322947212453652424643933)
                ·
                  refine ⟨9121105204670119659241475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24322947212453652424643933 9121105204670119659241475)
                  ·
                    refine ⟨13681657807005179488862213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9121105204670119659241475 13681657807005179488862213)
                    ·
                      refine ⟨2565310838813471154161665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13681657807005179488862213 2565310838813471154161665)
                      ·
                        rfl

theorem cell23_4995925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4995925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995925 prefixEnd_4995925 := by exact prefixLift 4995925
  have htrace : WordTrace (prefixWord ++ tailWord_4995925) baseStart_4995925 baseEnd_4995925 := by
    simpa [prefixWord, tailWord_4995925, baseEnd_4995925] using wordTrace_append hprefix tailTrace_4995925
  have hstable : (prefixWord ++ tailWord_4995925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995925).length < 2 ^ (prefixWord ++ tailWord_4995925).sum := by decide
  have hdescent : baseEnd_4995925 < baseStart_4995925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995929 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 2, 3, 2]
def baseStart_4995929 : Nat := 118140960795 + 4995929 * 2 ^ 59
def prefixEnd_4995929 : Nat := 4983230072969 + 3 ^ 40 * 4995929 * 2
def baseEnd_4995929 : Nat := 2565312892736089138511647

theorem tailTrace_4995929 : CollatzResearch.WordTrace tailWord_4995929 prefixEnd_4995929 2565312892736089138511647 := by
  unfold tailWord_4995929
  simp only [CollatzResearch.WordTrace]
  refine ⟨182216500317609944588662841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121477666878406629725775227 182216500317609944588662841)
  ·
    refine ⟨136662375238207458441497131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182216500317609944588662841 136662375238207458441497131)
    ·
      refine ⟨204993562857311187662245697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136662375238207458441497131 204993562857311187662245697)
      ·
        refine ⟨153745172142983390746684273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204993562857311187662245697 153745172142983390746684273)
        ·
          refine ⟨115308879107237543060013205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153745172142983390746684273 115308879107237543060013205)
          ·
            refine ⟨5405103708151759830938119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115308879107237543060013205 5405103708151759830938119)
            ·
              refine ⟨8107655562227639746407179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5405103708151759830938119 8107655562227639746407179)
              ·
                refine ⟨12161483343341459619610769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8107655562227639746407179 12161483343341459619610769)
                ·
                  refine ⟨9121112507506094714708077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12161483343341459619610769 9121112507506094714708077)
                  ·
                    refine ⟨3420417190314785518015529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9121112507506094714708077 3420417190314785518015529)
                    ·
                      refine ⟨2565312892736089138511647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420417190314785518015529 2565312892736089138511647)
                      ·
                        rfl

theorem cell23_4995929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_4995929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995929 prefixEnd_4995929 := by exact prefixLift 4995929
  have htrace : WordTrace (prefixWord ++ tailWord_4995929) baseStart_4995929 baseEnd_4995929 := by
    simpa [prefixWord, tailWord_4995929, baseEnd_4995929] using wordTrace_append hprefix tailTrace_4995929
  have hstable : (prefixWord ++ tailWord_4995929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995929).length < 2 ^ (prefixWord ++ tailWord_4995929).sum := by decide
  have hdescent : baseEnd_4995929 < baseStart_4995929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995935 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 4, 4]
def baseStart_4995935 : Nat := 118140960795 + 4995935 * 2 ^ 59
def prefixEnd_4995935 : Nat := 4983230072969 + 3 ^ 40 * 4995935 * 2
def baseEnd_4995935 : Nat := 855105324540005371678873

theorem tailTrace_4995935 : CollatzResearch.WordTrace tailWord_4995935 prefixEnd_4995935 855105324540005371678873 := by
  unfold tailWord_4995935
  simp only [CollatzResearch.WordTrace]
  refine ⟨182216719155588207613381259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121477812770392138408920839 182216719155588207613381259)
  ·
    refine ⟨273325078733382311420071889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182216719155588207613381259 273325078733382311420071889)
    ·
      refine ⟨204993809050036733565053917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273325078733382311420071889 204993809050036733565053917)
      ·
        refine ⟨76872678393763775086895219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204993809050036733565053917 76872678393763775086895219)
        ·
          refine ⟨115309017590645662630342829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76872678393763775086895219 115309017590645662630342829)
          ·
            refine ⟨43240881596492123486378561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115309017590645662630342829 43240881596492123486378561)
            ·
              refine ⟨32430661197369092614783921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43240881596492123486378561 32430661197369092614783921)
              ·
                refine ⟨24322995898026819461087941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32430661197369092614783921 24322995898026819461087941)
                ·
                  refine ⟨4560561730880028648953989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24322995898026819461087941 4560561730880028648953989)
                  ·
                    refine ⟨855105324540005371678873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560561730880028648953989 855105324540005371678873)
                    ·
                      rfl

theorem cell23_4995935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_4995935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995935 prefixEnd_4995935 := by exact prefixLift 4995935
  have htrace : WordTrace (prefixWord ++ tailWord_4995935) baseStart_4995935 baseEnd_4995935 := by
    simpa [prefixWord, tailWord_4995935, baseEnd_4995935] using wordTrace_append hprefix tailTrace_4995935
  have hstable : (prefixWord ++ tailWord_4995935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995935).length < 2 ^ (prefixWord ++ tailWord_4995935).sum := by decide
  have hdescent : baseEnd_4995935 < baseStart_4995935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995939 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 1, 5]
def baseStart_4995939 : Nat := 118140960795 + 4995939 * 2 ^ 59
def prefixEnd_4995939 : Nat := 4983230072969 + 3 ^ 40 * 4995939 * 2
def baseEnd_4995939 : Nat := 855106009180878033128867

theorem tailTrace_4995939 : CollatzResearch.WordTrace tailWord_4995939 prefixEnd_4995939 855106009180878033128867 := by
  unfold tailWord_4995939
  simp only [CollatzResearch.WordTrace]
  refine ⟨182216865047573716296526871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121477910031715810864351247 182216865047573716296526871)
  ·
    refine ⟨273325297571360574444790307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182216865047573716296526871 273325297571360574444790307)
    ·
      refine ⟨409987946357040861667185461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273325297571360574444790307 409987946357040861667185461)
      ·
        refine ⟨38436369970972580781298637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 409987946357040861667185461 38436369970972580781298637)
        ·
          refine ⟨14413638739114717792986989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38436369970972580781298637 14413638739114717792986989)
          ·
            refine ⟨5405114527168019172370121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14413638739114717792986989 5405114527168019172370121)
            ·
              refine ⟨4053835895376014379277591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5405114527168019172370121 4053835895376014379277591)
              ·
                refine ⟨6080753843064021568916387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053835895376014379277591 6080753843064021568916387)
                ·
                  refine ⟨9121130764596032353374581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6080753843064021568916387 9121130764596032353374581)
                  ·
                    refine ⟨855106009180878033128867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9121130764596032353374581 855106009180878033128867)
                    ·
                      rfl

theorem cell23_4995939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 1, 5].length) (baseStart_4995939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995939 prefixEnd_4995939 := by exact prefixLift 4995939
  have htrace : WordTrace (prefixWord ++ tailWord_4995939) baseStart_4995939 baseEnd_4995939 := by
    simpa [prefixWord, tailWord_4995939, baseEnd_4995939] using wordTrace_append hprefix tailTrace_4995939
  have hstable : (prefixWord ++ tailWord_4995939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995939).length < 2 ^ (prefixWord ++ tailWord_4995939).sum := by decide
  have hdescent : baseEnd_4995939 < baseStart_4995939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995948 : List Nat := [2, 2, 1, 1, 4, 1, 12]
def baseStart_4995948 : Nat := 118140960795 + 4995948 * 2 ^ 59
def prefixEnd_4995948 : Nat := 4983230072969 + 3 ^ 40 * 4995948 * 2
def baseEnd_4995948 : Nat := 31670649986031167458939

theorem tailTrace_4995948 : CollatzResearch.WordTrace tailWord_4995948 prefixEnd_4995948 31670649986031167458939 := by
  unfold tailWord_4995948
  simp only [CollatzResearch.WordTrace]
  refine ⟨91108596652270555416802249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121478128869694073889069665 91108596652270555416802249)
  ·
    refine ⟨68331447489202916562601687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91108596652270555416802249 68331447489202916562601687)
    ·
      refine ⟨102497171233804374843902531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68331447489202916562601687 102497171233804374843902531)
      ·
        refine ⟨153745756850706562265853797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102497171233804374843902531 153745756850706562265853797)
        ·
          refine ⟨28827329409507480424847587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153745756850706562265853797 28827329409507480424847587)
          ·
            refine ⟨43240994114261220637271381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28827329409507480424847587 43240994114261220637271381)
            ·
              refine ⟨31670649986031167458939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 43240994114261220637271381 31670649986031167458939)
              ·
                rfl

theorem cell23_4995948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 12].length) (baseStart_4995948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995948 prefixEnd_4995948 := by exact prefixLift 4995948
  have htrace : WordTrace (prefixWord ++ tailWord_4995948) baseStart_4995948 baseEnd_4995948 := by
    simpa [prefixWord, tailWord_4995948, baseEnd_4995948] using wordTrace_append hprefix tailTrace_4995948
  have hstable : (prefixWord ++ tailWord_4995948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995948).length < 2 ^ (prefixWord ++ tailWord_4995948).sum := by decide
  have hdescent : baseEnd_4995948 < baseStart_4995948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995952 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 2, 4]
def baseStart_4995952 : Nat := 118140960795 + 4995952 * 2 ^ 59
def prefixEnd_4995952 : Nat := 4983230072969 + 3 ^ 40 * 4995952 * 2
def baseEnd_4995952 : Nat := 855108234263714182841347

theorem tailTrace_4995952 : CollatzResearch.WordTrace tailWord_4995952 prefixEnd_4995952 855108234263714182841347 := by
  unfold tailWord_4995952
  simp only [CollatzResearch.WordTrace]
  refine ⟨91108669598263309758375055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121478226131017746344500073 91108669598263309758375055)
  ·
    refine ⟨136663004397394964637562583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91108669598263309758375055 136663004397394964637562583)
    ·
      refine ⟨204994506596092446956343875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136663004397394964637562583 204994506596092446956343875)
      ·
        refine ⟨307491759894138670434515813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204994506596092446956343875 307491759894138670434515813)
        ·
          refine ⟨57654704980151000706471715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307491759894138670434515813 57654704980151000706471715)
          ·
            refine ⟨86482057470226501059707573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57654704980151000706471715 86482057470226501059707573)
            ·
              refine ⟨8107692887833734474347585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86482057470226501059707573 8107692887833734474347585)
              ·
                refine ⟨6080769665875300855760689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8107692887833734474347585 6080769665875300855760689)
                ·
                  refine ⟨4560577249406475641820517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6080769665875300855760689 4560577249406475641820517)
                  ·
                    refine ⟨855108234263714182841347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560577249406475641820517 855108234263714182841347)
                    ·
                      rfl

theorem cell23_4995952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2, 4].length) (baseStart_4995952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995952 prefixEnd_4995952 := by exact prefixLift 4995952
  have htrace : WordTrace (prefixWord ++ tailWord_4995952) baseStart_4995952 baseEnd_4995952 := by
    simpa [prefixWord, tailWord_4995952, baseEnd_4995952] using wordTrace_append hprefix tailTrace_4995952
  have hstable : (prefixWord ++ tailWord_4995952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995952).length < 2 ^ (prefixWord ++ tailWord_4995952).sum := by decide
  have hdescent : baseEnd_4995952 < baseStart_4995952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4995968 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_4995968 : Nat := 118140960795 + 4995968 * 2 ^ 59
def prefixEnd_4995968 : Nat := 4983230072969 + 3 ^ 40 * 4995968 * 2
def baseEnd_4995968 : Nat := 2565332918481614485923967

theorem tailTrace_4995968 : CollatzResearch.WordTrace tailWord_4995968 prefixEnd_4995968 2565332918481614485923967 := by
  unfold tailWord_4995968
  simp only [CollatzResearch.WordTrace]
  refine ⟨91108961382234327124666279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121478615176312436166221705 91108961382234327124666279)
  ·
    refine ⟨136663442073351490686999419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91108961382234327124666279 136663442073351490686999419)
    ·
      refine ⟨204995163110027236030499129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136663442073351490686999419 204995163110027236030499129)
      ·
        refine ⟨153746372332520427022874347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204995163110027236030499129 153746372332520427022874347)
        ·
          refine ⟨230619558498780640534311521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153746372332520427022874347 230619558498780640534311521)
          ·
            refine ⟨172964668874085480400733641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230619558498780640534311521 172964668874085480400733641)
            ·
              refine ⟨129723501655564110300550231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172964668874085480400733641 129723501655564110300550231)
              ·
                refine ⟨194585252483346165450825347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129723501655564110300550231 194585252483346165450825347)
                ·
                  refine ⟨291877878725019248176238021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194585252483346165450825347 291877878725019248176238021)
                  ·
                    refine ⟨54727102260941109033044629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291877878725019248176238021 54727102260941109033044629)
                    ·
                      refine ⟨2565332918481614485923967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54727102260941109033044629 2565332918481614485923967)
                      ·
                        rfl

theorem cell23_4995968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_4995968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4995968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4995968 prefixEnd_4995968 := by exact prefixLift 4995968
  have htrace : WordTrace (prefixWord ++ tailWord_4995968) baseStart_4995968 baseEnd_4995968 := by
    simpa [prefixWord, tailWord_4995968, baseEnd_4995968] using wordTrace_append hprefix tailTrace_4995968
  have hstable : (prefixWord ++ tailWord_4995968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4995968).length < 2 ^ (prefixWord ++ tailWord_4995968).sum := by decide
  have hdescent : baseEnd_4995968 < baseStart_4995968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4995968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996035 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 3]
def baseStart_4996035 : Nat := 118140960795 + 4996035 * 2 ^ 59
def prefixEnd_4996035 : Nat := 4983230072969 + 3 ^ 40 * 4996035 * 2
def baseEnd_4996035 : Nat := 2565367321685465723786159

theorem tailTrace_4996035 : CollatzResearch.WordTrace tailWord_4996035 prefixEnd_4996035 2565367321685465723786159 := by
  unfold tailWord_4996035
  simp only [CollatzResearch.WordTrace]
  refine ⟨182220366455225924692021559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121480244303483949794681039 182220366455225924692021559)
  ·
    refine ⟨273330549682838887038032339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182220366455225924692021559 273330549682838887038032339)
    ·
      refine ⟨409995824524258330557048509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273330549682838887038032339 409995824524258330557048509)
      ·
        refine ⟨153748434196596873958893191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409995824524258330557048509 153748434196596873958893191)
        ·
          refine ⟨230622651294895310938339787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153748434196596873958893191 230622651294895310938339787)
          ·
            refine ⟨345933976942342966407509681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230622651294895310938339787 345933976942342966407509681)
            ·
              refine ⟨259450482706757224805632261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345933976942342966407509681 259450482706757224805632261)
              ·
                refine ⟨48646965507516979651056049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259450482706757224805632261 48646965507516979651056049)
                ·
                  refine ⟨36485224130637734738292037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48646965507516979651056049 36485224130637734738292037)
                  ·
                    refine ⟨6840979524494575263429757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36485224130637734738292037 6840979524494575263429757)
                    ·
                      refine ⟨2565367321685465723786159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6840979524494575263429757 2565367321685465723786159)
                      ·
                        rfl

theorem cell23_4996035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_4996035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996035 prefixEnd_4996035 := by exact prefixLift 4996035
  have htrace : WordTrace (prefixWord ++ tailWord_4996035) baseStart_4996035 baseEnd_4996035 := by
    simpa [prefixWord, tailWord_4996035, baseEnd_4996035] using wordTrace_append hprefix tailTrace_4996035
  have hstable : (prefixWord ++ tailWord_4996035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996035).length < 2 ^ (prefixWord ++ tailWord_4996035).sum := by decide
  have hdescent : baseEnd_4996035 < baseStart_4996035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996052 : List Nat := [2, 4, 1, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4996052 : Nat := 118140960795 + 4996052 * 2 ^ 59
def prefixEnd_4996052 : Nat := 4983230072969 + 3 ^ 40 * 4996052 * 2
def baseEnd_4996052 : Nat := 2565376050856592157273581

theorem tailTrace_4996052 : CollatzResearch.WordTrace tailWord_4996052 prefixEnd_4996052 2565376050856592157273581 := by
  unfold tailWord_4996052
  simp only [CollatzResearch.WordTrace]
  refine ⟨91110493248082168297695205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121480657664109557730260273 91110493248082168297695205)
  ·
    refine ⟨17083217484015406555817851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91110493248082168297695205 17083217484015406555817851)
    ·
      refine ⟨25624826226023109833726777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17083217484015406555817851 25624826226023109833726777)
      ·
        refine ⟨19218619669517332375295083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25624826226023109833726777 19218619669517332375295083)
        ·
          refine ⟨28827929504275998562942625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19218619669517332375295083 28827929504275998562942625)
          ·
            refine ⟨21620947128206998922206969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28827929504275998562942625 21620947128206998922206969)
            ·
              refine ⟨16215710346155249191655227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21620947128206998922206969 16215710346155249191655227)
              ·
                refine ⟨24323565519232873787482841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16215710346155249191655227 24323565519232873787482841)
                ·
                  refine ⟨18242674139424655340612131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24323565519232873787482841 18242674139424655340612131)
                  ·
                    refine ⟨27364011209136983010918197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18242674139424655340612131 27364011209136983010918197)
                    ·
                      refine ⟨2565376050856592157273581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27364011209136983010918197 2565376050856592157273581)
                      ·
                        rfl

theorem cell23_4996052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4996052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996052 prefixEnd_4996052 := by exact prefixLift 4996052
  have htrace : WordTrace (prefixWord ++ tailWord_4996052) baseStart_4996052 baseEnd_4996052 := by
    simpa [prefixWord, tailWord_4996052, baseEnd_4996052] using wordTrace_append hprefix tailTrace_4996052
  have hstable : (prefixWord ++ tailWord_4996052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996052).length < 2 ^ (prefixWord ++ tailWord_4996052).sum := by decide
  have hdescent : baseEnd_4996052 < baseStart_4996052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996053 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4996053 : Nat := 118140960795 + 4996053 * 2 ^ 59
def prefixEnd_4996053 : Nat := 4983230072969 + 3 ^ 40 * 4996053 * 2
def baseEnd_4996053 : Nat := 2565376564337246653361077

theorem tailTrace_4996053 : CollatzResearch.WordTrace tailWord_4996053 prefixEnd_4996053 2565376564337246653361077 := by
  unfold tailWord_4996053
  simp only [CollatzResearch.WordTrace]
  refine ⟨182221022969160713766176813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121480681979440475844117875 182221022969160713766176813)
  ·
    refine ⟨68332883613435267662316305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182221022969160713766176813 68332883613435267662316305)
    ·
      refine ⟨51249662710076450746737229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68332883613435267662316305 51249662710076450746737229)
      ·
        refine ⟨19218623516278669030026461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51249662710076450746737229 19218623516278669030026461)
        ·
          refine ⟨7206983818604500886259923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19218623516278669030026461 7206983818604500886259923)
          ·
            refine ⟨10810475727906751329389885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7206983818604500886259923 10810475727906751329389885)
            ·
              refine ⟨4053928397965031748521207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10810475727906751329389885 4053928397965031748521207)
              ·
                refine ⟨6080892596947547622781811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053928397965031748521207 6080892596947547622781811)
                ·
                  refine ⟨9121338895421321434172717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6080892596947547622781811 9121338895421321434172717)
                  ·
                    refine ⟨3420502085782995537814769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9121338895421321434172717 3420502085782995537814769)
                    ·
                      refine ⟨2565376564337246653361077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420502085782995537814769 2565376564337246653361077)
                      ·
                        rfl

theorem cell23_4996053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4996053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996053 prefixEnd_4996053 := by exact prefixLift 4996053
  have htrace : WordTrace (prefixWord ++ tailWord_4996053) baseStart_4996053 baseEnd_4996053 := by
    simpa [prefixWord, tailWord_4996053, baseEnd_4996053] using wordTrace_append hprefix tailTrace_4996053
  have hstable : (prefixWord ++ tailWord_4996053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996053).length < 2 ^ (prefixWord ++ tailWord_4996053).sum := by decide
  have hdescent : baseEnd_4996053 < baseStart_4996053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996122 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4996122 : Nat := 118140960795 + 4996122 * 2 ^ 59
def prefixEnd_4996122 : Nat := 4983230072969 + 3 ^ 40 * 4996122 * 2
def baseEnd_4996122 : Nat := 2565411994502406883398259

theorem tailTrace_4996122 : CollatzResearch.WordTrace tailWord_4996122 prefixEnd_4996122 2565411994502406883398259 := by
  unfold tailWord_4996122
  simp only [CollatzResearch.WordTrace]
  refine ⟨45555884901477684637609655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121482359737273825700292413 45555884901477684637609655)
  ·
    refine ⟨68333827352216526956414483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45555884901477684637609655 68333827352216526956414483)
    ·
      refine ⟨102500741028324790434621725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68333827352216526956414483 102500741028324790434621725)
      ·
        refine ⟨38437777885621796412983147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102500741028324790434621725 38437777885621796412983147)
        ·
          refine ⟨57656666828432694619474721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38437777885621796412983147 57656666828432694619474721)
          ·
            refine ⟨43242500121324520964606041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57656666828432694619474721 43242500121324520964606041)
            ·
              refine ⟨32431875090993390723454531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43242500121324520964606041 32431875090993390723454531)
              ·
                refine ⟨48647812636490086085181797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32431875090993390723454531 48647812636490086085181797)
                ·
                  refine ⟨9121464869341891140971587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48647812636490086085181797 9121464869341891140971587)
                  ·
                    refine ⟨13682197304012836711457381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9121464869341891140971587 13682197304012836711457381)
                    ·
                      refine ⟨2565411994502406883398259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13682197304012836711457381 2565411994502406883398259)
                      ·
                        rfl

theorem cell23_4996122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4996122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996122 prefixEnd_4996122 := by exact prefixLift 4996122
  have htrace : WordTrace (prefixWord ++ tailWord_4996122) baseStart_4996122 baseEnd_4996122 := by
    simpa [prefixWord, tailWord_4996122, baseEnd_4996122] using wordTrace_append hprefix tailTrace_4996122
  have hstable : (prefixWord ++ tailWord_4996122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996122).length < 2 ^ (prefixWord ++ tailWord_4996122).sum := by decide
  have hdescent : baseEnd_4996122 < baseStart_4996122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996192 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 3, 5]
def baseStart_4996192 : Nat := 118140960795 + 4996192 * 2 ^ 59
def prefixEnd_4996192 : Nat := 4983230072969 + 3 ^ 40 * 4996192 * 2
def baseEnd_4996192 : Nat := 855149312716073869840979

theorem tailTrace_4996192 : CollatzResearch.WordTrace tailWord_4996192 prefixEnd_4996192 855149312716073869840979 := by
  unfold tailWord_4996192
  simp only [CollatzResearch.WordTrace]
  refine ⟨91113046357828570252743415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121484061810438093670324553 91113046357828570252743415)
  ·
    refine ⟨136669569536742855379115123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91113046357828570252743415 136669569536742855379115123)
    ·
      refine ⟨205004354305114283068672685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136669569536742855379115123 205004354305114283068672685)
      ·
        refine ⟨76876632864417856150752257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205004354305114283068672685 76876632864417856150752257)
        ·
          refine ⟨57657474648313392113064193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76876632864417856150752257 57657474648313392113064193)
          ·
            refine ⟨43243105986235044084798145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57657474648313392113064193 43243105986235044084798145)
            ·
              refine ⟨32432329489676283063598609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43243105986235044084798145 32432329489676283063598609)
              ·
                refine ⟨24324247117257212297698957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32432329489676283063598609 24324247117257212297698957)
                ·
                  refine ⟨9121592668971454611637109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24324247117257212297698957 9121592668971454611637109)
                  ·
                    refine ⟨855149312716073869840979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9121592668971454611637109 855149312716073869840979)
                    ·
                      rfl

theorem cell23_4996192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_4996192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996192 prefixEnd_4996192 := by exact prefixLift 4996192
  have htrace : WordTrace (prefixWord ++ tailWord_4996192) baseStart_4996192 baseEnd_4996192 := by
    simpa [prefixWord, tailWord_4996192, baseEnd_4996192] using wordTrace_append hprefix tailTrace_4996192
  have hstable : (prefixWord ++ tailWord_4996192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996192).length < 2 ^ (prefixWord ++ tailWord_4996192).sum := by decide
  have hdescent : baseEnd_4996192 < baseStart_4996192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996263 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4996263 : Nat := 118140960795 + 4996263 * 2 ^ 59
def prefixEnd_4996263 : Nat := 4983230072969 + 3 ^ 40 * 4996263 * 2
def baseEnd_4996263 : Nat := 2565484395274690831735111

theorem tailTrace_4996263 : CollatzResearch.WordTrace tailWord_4996263 prefixEnd_4996263 2565484395274690831735111 := by
  unfold tailWord_4996263
  simp only [CollatzResearch.WordTrace]
  refine ⟨182228682298399919631321443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121485788198933279754214295 182228682298399919631321443)
  ·
    refine ⟨273343023447599879446982165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182228682298399919631321443 273343023447599879446982165)
    ·
      refine ⟨12812954224106244349077289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 273343023447599879446982165 12812954224106244349077289)
      ·
        refine ⟨9609715668079683261807967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12812954224106244349077289 9609715668079683261807967)
        ·
          refine ⟨14414573502119524892711951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9609715668079683261807967 14414573502119524892711951)
          ·
            refine ⟨21621860253179287339067927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14414573502119524892711951 21621860253179287339067927)
            ·
              refine ⟨32432790379768931008601891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21621860253179287339067927 32432790379768931008601891)
              ·
                refine ⟨48649185569653396512902837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32432790379768931008601891 48649185569653396512902837)
                ·
                  refine ⟨4560861147155005923084641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48649185569653396512902837 4560861147155005923084641)
                  ·
                    refine ⟨3420645860366254442313481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4560861147155005923084641 3420645860366254442313481)
                    ·
                      refine ⟨2565484395274690831735111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420645860366254442313481 2565484395274690831735111)
                      ·
                        rfl

theorem cell23_4996263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4996263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996263 prefixEnd_4996263 := by exact prefixLift 4996263
  have htrace : WordTrace (prefixWord ++ tailWord_4996263) baseStart_4996263 baseEnd_4996263 := by
    simpa [prefixWord, tailWord_4996263, baseEnd_4996263] using wordTrace_append hprefix tailTrace_4996263
  have hstable : (prefixWord ++ tailWord_4996263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996263).length < 2 ^ (prefixWord ++ tailWord_4996263).sum := by decide
  have hdescent : baseEnd_4996263 < baseStart_4996263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996279 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_4996279 : Nat := 118140960795 + 4996279 * 2 ^ 59
def prefixEnd_4996279 : Nat := 4983230072969 + 3 ^ 40 * 4996279 * 2
def baseEnd_4996279 : Nat := 2565492610965162769135037

theorem tailTrace_4996279 : CollatzResearch.WordTrace tailWord_4996279 prefixEnd_4996279 2565492610965162769135037 := by
  unfold tailWord_4996279
  simp only [CollatzResearch.WordTrace]
  refine ⟨182229265866341954363903891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121486177244227969575935927 182229265866341954363903891)
  ·
    refine ⟨273343898799512931545855837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182229265866341954363903891 273343898799512931545855837)
    ·
      refine ⟨102503962049817349329695939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273343898799512931545855837 102503962049817349329695939)
      ·
        refine ⟨153755943074726023994543909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102503962049817349329695939 153755943074726023994543909)
        ·
          refine ⟨28829239326511129498976983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153755943074726023994543909 28829239326511129498976983)
          ·
            refine ⟨43243858989766694248465475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28829239326511129498976983 43243858989766694248465475)
            ·
              refine ⟨64865788484650041372698213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43243858989766694248465475 64865788484650041372698213)
              ·
                refine ⟨12162335340871882757380915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64865788484650041372698213 12162335340871882757380915)
                ·
                  refine ⟨18243503011307824136071373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12162335340871882757380915 18243503011307824136071373)
                  ·
                    refine ⟨6841313629240434051026765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18243503011307824136071373 6841313629240434051026765)
                    ·
                      refine ⟨2565492610965162769135037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6841313629240434051026765 2565492610965162769135037)
                      ·
                        rfl

theorem cell23_4996279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_4996279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996279 prefixEnd_4996279 := by exact prefixLift 4996279
  have htrace : WordTrace (prefixWord ++ tailWord_4996279) baseStart_4996279 baseEnd_4996279 := by
    simpa [prefixWord, tailWord_4996279, baseEnd_4996279] using wordTrace_append hprefix tailTrace_4996279
  have hstable : (prefixWord ++ tailWord_4996279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996279).length < 2 ^ (prefixWord ++ tailWord_4996279).sum := by decide
  have hdescent : baseEnd_4996279 < baseStart_4996279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996290 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_4996290 : Nat := 118140960795 + 4996290 * 2 ^ 59
def prefixEnd_4996290 : Nat := 4983230072969 + 3 ^ 40 * 4996290 * 2
def baseEnd_4996290 : Nat := 855166086417454075365829

theorem tailTrace_4996290 : CollatzResearch.WordTrace tailWord_4996290 prefixEnd_4996290 855166086417454075365829 := by
  unfold tailWord_4996290
  simp only [CollatzResearch.WordTrace]
  refine ⟨45557416767325525810638581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121486444712868068828369549 45557416767325525810638581)
  ·
    refine ⟨4271007821936768044747367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45557416767325525810638581 4271007821936768044747367)
    ·
      refine ⟨6406511732905152067121051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4271007821936768044747367 6406511732905152067121051)
      ·
        refine ⟨9609767599357728100681577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6406511732905152067121051 9609767599357728100681577)
        ·
          refine ⟨7207325699518296075511183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9609767599357728100681577 7207325699518296075511183)
          ·
            refine ⟨10810988549277444113266775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207325699518296075511183 10810988549277444113266775)
            ·
              refine ⟨16216482823916166169900163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10810988549277444113266775 16216482823916166169900163)
              ·
                refine ⟨24324724235874249254850245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16216482823916166169900163 24324724235874249254850245)
                ·
                  refine ⟨4560885794226421735284421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24324724235874249254850245 4560885794226421735284421)
                  ·
                    refine ⟨855166086417454075365829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560885794226421735284421 855166086417454075365829)
                    ·
                      rfl

theorem cell23_4996290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_4996290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996290 prefixEnd_4996290 := by exact prefixLift 4996290
  have htrace : WordTrace (prefixWord ++ tailWord_4996290) baseStart_4996290 baseEnd_4996290 := by
    simpa [prefixWord, tailWord_4996290, baseEnd_4996290] using wordTrace_append hprefix tailTrace_4996290
  have hstable : (prefixWord ++ tailWord_4996290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996290).length < 2 ^ (prefixWord ++ tailWord_4996290).sum := by decide
  have hdescent : baseEnd_4996290 < baseStart_4996290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996310 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4996310 : Nat := 118140960795 + 4996310 * 2 ^ 59
def prefixEnd_4996310 : Nat := 4983230072969 + 3 ^ 40 * 4996310 * 2
def baseEnd_4996310 : Nat := 2565508528865452147847395

theorem tailTrace_4996310 : CollatzResearch.WordTrace tailWord_4996310 prefixEnd_4996310 2565508528865452147847395 := by
  unfold tailWord_4996310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389399783076852916142649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121486931019486431105521589 11389399783076852916142649)
  ·
    refine ⟨8542049837307639687106987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11389399783076852916142649 8542049837307639687106987)
    ·
      refine ⟨12813074755961459530660481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8542049837307639687106987 12813074755961459530660481)
      ·
        refine ⟨9609806066971094647995361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12813074755961459530660481 9609806066971094647995361)
        ·
          refine ⟨7207354550228320985996521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9609806066971094647995361 7207354550228320985996521)
          ·
            refine ⟨5405515912671240739497391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7207354550228320985996521 5405515912671240739497391)
            ·
              refine ⟨8108273869006861109246087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5405515912671240739497391 8108273869006861109246087)
              ·
                refine ⟨12162410803510291663869131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8108273869006861109246087 12162410803510291663869131)
                ·
                  refine ⟨18243616205265437495803697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12162410803510291663869131 18243616205265437495803697)
                  ·
                    refine ⟨13682712153949078121852773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18243616205265437495803697 13682712153949078121852773)
                    ·
                      refine ⟨2565508528865452147847395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13682712153949078121852773 2565508528865452147847395)
                      ·
                        rfl

theorem cell23_4996310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4996310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996310 prefixEnd_4996310 := by exact prefixLift 4996310
  have htrace : WordTrace (prefixWord ++ tailWord_4996310) baseStart_4996310 baseEnd_4996310 := by
    simpa [prefixWord, tailWord_4996310, baseEnd_4996310] using wordTrace_append hprefix tailTrace_4996310
  have hstable : (prefixWord ++ tailWord_4996310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996310).length < 2 ^ (prefixWord ++ tailWord_4996310).sum := by decide
  have hdescent : baseEnd_4996310 < baseStart_4996310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996339 : List Nat := [1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5]
def baseStart_4996339 : Nat := 118140960795 + 4996339 * 2 ^ 59
def prefixEnd_4996339 : Nat := 4983230072969 + 3 ^ 40 * 4996339 * 2
def baseEnd_4996339 : Nat := 2565523419804432534384761

theorem tailTrace_4996339 : CollatzResearch.WordTrace tailWord_4996339 prefixEnd_4996339 2565523419804432534384761 := by
  unfold tailWord_4996339
  simp only [CollatzResearch.WordTrace]
  refine ⟨182231454246124584611088071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121487636164083056407392047 182231454246124584611088071)
  ·
    refine ⟨273347181369186876916632107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182231454246124584611088071 273347181369186876916632107)
    ·
      refine ⟨410020772053780315374948161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273347181369186876916632107 410020772053780315374948161)
      ·
        refine ⟨307515579040335236531211121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410020772053780315374948161 307515579040335236531211121)
        ·
          refine ⟨230636684280251427398408341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307515579040335236531211121 230636684280251427398408341)
          ·
            refine ⟨10811094575636785659300391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 230636684280251427398408341 10811094575636785659300391)
            ·
              refine ⟨16216641863455178488950587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10811094575636785659300391 16216641863455178488950587)
              ·
                refine ⟨24324962795182767733425881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16216641863455178488950587 24324962795182767733425881)
                ·
                  refine ⟨18243722096387075800069411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24324962795182767733425881 18243722096387075800069411)
                  ·
                    refine ⟨27365583144580613700104117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18243722096387075800069411 27365583144580613700104117)
                    ·
                      refine ⟨2565523419804432534384761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27365583144580613700104117 2565523419804432534384761)
                      ·
                        rfl

theorem cell23_4996339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_4996339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996339 prefixEnd_4996339 := by exact prefixLift 4996339
  have htrace : WordTrace (prefixWord ++ tailWord_4996339) baseStart_4996339 baseEnd_4996339 := by
    simpa [prefixWord, tailWord_4996339, baseEnd_4996339] using wordTrace_append hprefix tailTrace_4996339
  have hstable : (prefixWord ++ tailWord_4996339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996339).length < 2 ^ (prefixWord ++ tailWord_4996339).sum := by decide
  have hdescent : baseEnd_4996339 < baseStart_4996339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996352 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_4996352 : Nat := 118140960795 + 4996352 * 2 ^ 59
def prefixEnd_4996352 : Nat := 4983230072969 + 3 ^ 40 * 4996352 * 2
def baseEnd_4996352 : Nat := 2565530095052940983522201

theorem tailTrace_4996352 : CollatzResearch.WordTrace tailWord_4996352 prefixEnd_4996352 2565530095052940983522201 := by
  unfold tailWord_4996352
  simp only [CollatzResearch.WordTrace]
  refine ⟨91115964197538743915655655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121487952263384991887540873 91115964197538743915655655)
  ·
    refine ⟨136673946296308115873483483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91115964197538743915655655 136673946296308115873483483)
    ·
      refine ⟨205010919444462173810225225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136673946296308115873483483 205010919444462173810225225)
      ·
        refine ⟨153758189583346630357668919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205010919444462173810225225 153758189583346630357668919)
        ·
          refine ⟨230637284375019945536503379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153758189583346630357668919 230637284375019945536503379)
          ·
            refine ⟨345955926562529918304755069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230637284375019945536503379 345955926562529918304755069)
            ·
              refine ⟨129733472460948719364283151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345955926562529918304755069 129733472460948719364283151)
              ·
                refine ⟨194600208691423079046424727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129733472460948719364283151 194600208691423079046424727)
                ·
                  refine ⟨291900313037134618569637091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194600208691423079046424727 291900313037134618569637091)
                  ·
                    refine ⟨437850469555701927854455637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 291900313037134618569637091 437850469555701927854455637)
                    ·
                      refine ⟨2565530095052940983522201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 437850469555701927854455637 2565530095052940983522201)
                      ·
                        rfl

theorem cell23_4996352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_4996352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996352 prefixEnd_4996352 := by exact prefixLift 4996352
  have htrace : WordTrace (prefixWord ++ tailWord_4996352) baseStart_4996352 baseEnd_4996352 := by
    simpa [prefixWord, tailWord_4996352, baseEnd_4996352] using wordTrace_append hprefix tailTrace_4996352
  have hstable : (prefixWord ++ tailWord_4996352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996352).length < 2 ^ (prefixWord ++ tailWord_4996352).sum := by decide
  have hdescent : baseEnd_4996352 < baseStart_4996352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996353 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_4996353 : Nat := 118140960795 + 4996353 * 2 ^ 59
def prefixEnd_4996353 : Nat := 4983230072969 + 3 ^ 40 * 4996353 * 2
def baseEnd_4996353 : Nat := 2565530608533595479609697

theorem tailTrace_4996353 : CollatzResearch.WordTrace tailWord_4996353 prefixEnd_4996353 2565530608533595479609697 := by
  unfold tailWord_4996353
  simp only [CollatzResearch.WordTrace]
  refine ⟨182231964868073865002097713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121487976578715910001398475 182231964868073865002097713)
  ·
    refine ⟨136673973651055398751573285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182231964868073865002097713 136673973651055398751573285)
    ·
      refine ⟨25626370059572887265919991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136673973651055398751573285 25626370059572887265919991)
      ·
        refine ⟨38439555089359330898879987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25626370059572887265919991 38439555089359330898879987)
        ·
          refine ⟨57659332634038996348319981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38439555089359330898879987 57659332634038996348319981)
          ·
            refine ⟨21622249737764623630619993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57659332634038996348319981 21622249737764623630619993)
            ·
              refine ⟨16216687303323467722964995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21622249737764623630619993 16216687303323467722964995)
              ·
                refine ⟨24325030954985201584447493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16216687303323467722964995 24325030954985201584447493)
                ·
                  refine ⟨4560943304059725297083905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24325030954985201584447493 4560943304059725297083905)
                  ·
                    refine ⟨3420707478044793972812929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4560943304059725297083905 3420707478044793972812929)
                    ·
                      refine ⟨2565530608533595479609697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420707478044793972812929 2565530608533595479609697)
                      ·
                        rfl

theorem cell23_4996353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_4996353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996353 prefixEnd_4996353 := by exact prefixLift 4996353
  have htrace : WordTrace (prefixWord ++ tailWord_4996353) baseStart_4996353 baseEnd_4996353 := by
    simpa [prefixWord, tailWord_4996353, baseEnd_4996353] using wordTrace_append hprefix tailTrace_4996353
  have hstable : (prefixWord ++ tailWord_4996353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996353).length < 2 ^ (prefixWord ++ tailWord_4996353).sum := by decide
  have hdescent : baseEnd_4996353 < baseStart_4996353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996369 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 3]
def baseStart_4996369 : Nat := 118140960795 + 4996369 * 2 ^ 59
def prefixEnd_4996369 : Nat := 4983230072969 + 3 ^ 40 * 4996369 * 2
def baseEnd_4996369 : Nat := 2565538824224067417009623

theorem tailTrace_4996369 : CollatzResearch.WordTrace tailWord_4996369 prefixEnd_4996369 2565538824224067417009623 := by
  unfold tailWord_4996369
  simp only [CollatzResearch.WordTrace]
  refine ⟨182232548436015899734680161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121488365624010599823120107 182232548436015899734680161)
  ·
    refine ⟨136674411327011924801010121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182232548436015899734680161 136674411327011924801010121)
    ·
      refine ⟨102505808495258943600757591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136674411327011924801010121 102505808495258943600757591)
      ·
        refine ⟨153758712742888415401136387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102505808495258943600757591 153758712742888415401136387)
        ·
          refine ⟨230638069114332623101704581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153758712742888415401136387 230638069114332623101704581)
          ·
            refine ⟨43244637958937366831569609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230638069114332623101704581 43244637958937366831569609)
            ·
              refine ⟨32433478469203025123677207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43244637958937366831569609 32433478469203025123677207)
              ·
                refine ⟨48650217703804537685515811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32433478469203025123677207 48650217703804537685515811)
                ·
                  refine ⟨72975326555706806528273717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48650217703804537685515811 72975326555706806528273717)
                  ·
                    refine ⟨6841436864597513112025661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72975326555706806528273717 6841436864597513112025661)
                    ·
                      refine ⟨2565538824224067417009623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6841436864597513112025661 2565538824224067417009623)
                      ·
                        rfl

theorem cell23_4996369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 3].length) (baseStart_4996369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996369 prefixEnd_4996369 := by exact prefixLift 4996369
  have htrace : WordTrace (prefixWord ++ tailWord_4996369) baseStart_4996369 baseEnd_4996369 := by
    simpa [prefixWord, tailWord_4996369, baseEnd_4996369] using wordTrace_append hprefix tailTrace_4996369
  have hstable : (prefixWord ++ tailWord_4996369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996369).length < 2 ^ (prefixWord ++ tailWord_4996369).sum := by decide
  have hdescent : baseEnd_4996369 < baseStart_4996369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996483 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 6]
def baseStart_4996483 : Nat := 118140960795 + 4996483 * 2 ^ 59
def prefixEnd_4996483 : Nat := 4983230072969 + 3 ^ 40 * 4996483 * 2
def baseEnd_4996483 : Nat := 285066373446519996776011

theorem tailTrace_4996483 : CollatzResearch.WordTrace tailWord_4996483 prefixEnd_4996483 285066373446519996776011 := by
  unfold tailWord_4996483
  simp only [CollatzResearch.WordTrace]
  refine ⟨182236706357602897204330103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121491137571735264802886735 182236706357602897204330103)
  ·
    refine ⟨273355059536404345806495155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182236706357602897204330103 273355059536404345806495155)
    ·
      refine ⟨410032589304606518709742733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273355059536404345806495155 410032589304606518709742733)
      ·
        refine ⟨153762220989227444516153525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410032589304606518709742733 153762220989227444516153525)
        ·
          refine ⟨14415208217740072923389393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153762220989227444516153525 14415208217740072923389393)
          ·
            refine ⟨10811406163305054692542045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14415208217740072923389393 10811406163305054692542045)
            ·
              refine ⟨4054277311239395509703267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10811406163305054692542045 4054277311239395509703267)
              ·
                refine ⟨6081415966859093264554901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054277311239395509703267 6081415966859093264554901)
                ·
                  refine ⟨285066373446519996776011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6081415966859093264554901 285066373446519996776011)
                  ·
                    rfl

theorem cell23_4996483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 6].length) (baseStart_4996483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996483 prefixEnd_4996483 := by exact prefixLift 4996483
  have htrace : WordTrace (prefixWord ++ tailWord_4996483) baseStart_4996483 baseEnd_4996483 := by
    simpa [prefixWord, tailWord_4996483, baseEnd_4996483] using wordTrace_append hprefix tailTrace_4996483
  have hstable : (prefixWord ++ tailWord_4996483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996483).length < 2 ^ (prefixWord ++ tailWord_4996483).sum := by decide
  have hdescent : baseEnd_4996483 < baseStart_4996483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996499 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4]
def baseStart_4996499 : Nat := 118140960795 + 4996499 * 2 ^ 59
def prefixEnd_4996499 : Nat := 4983230072969 + 3 ^ 40 * 4996499 * 2
def baseEnd_4996499 : Nat := 2565605576709151908384025

theorem tailTrace_4996499 : CollatzResearch.WordTrace tailWord_4996499 prefixEnd_4996499 2565605576709151908384025 := by
  unfold tailWord_4996499
  simp only [CollatzResearch.WordTrace]
  refine ⟨182237289925544931936912551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121491526617029954624608367 182237289925544931936912551)
  ·
    refine ⟨273355934888317397905368827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182237289925544931936912551 273355934888317397905368827)
    ·
      refine ⟨410033902332476096858053241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273355934888317397905368827 410033902332476096858053241)
      ·
        refine ⟨307525426749357072643539931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410033902332476096858053241 307525426749357072643539931)
        ·
          refine ⟨461288140124035608965309897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307525426749357072643539931 461288140124035608965309897)
          ·
            refine ⟨345966105093026706723982423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461288140124035608965309897 345966105093026706723982423)
            ·
              refine ⟨518949157639540060085973635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345966105093026706723982423 518949157639540060085973635)
              ·
                refine ⟨778423736459310090128960453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518949157639540060085973635 778423736459310090128960453)
                ·
                  refine ⟨145954450586120641899180085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 778423736459310090128960453 145954450586120641899180085)
                  ·
                    refine ⟨13683229742448810178048133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 145954450586120641899180085 13683229742448810178048133)
                    ·
                      refine ⟨2565605576709151908384025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13683229742448810178048133 2565605576709151908384025)
                      ·
                        rfl

theorem cell23_4996499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_4996499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996499 prefixEnd_4996499 := by exact prefixLift 4996499
  have htrace : WordTrace (prefixWord ++ tailWord_4996499) baseStart_4996499 baseEnd_4996499 := by
    simpa [prefixWord, tailWord_4996499, baseEnd_4996499] using wordTrace_append hprefix tailTrace_4996499
  have hstable : (prefixWord ++ tailWord_4996499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996499).length < 2 ^ (prefixWord ++ tailWord_4996499).sum := by decide
  have hdescent : baseEnd_4996499 < baseStart_4996499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996503 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 2, 3, 2]
def baseStart_4996503 : Nat := 118140960795 + 4996503 * 2 ^ 59
def prefixEnd_4996503 : Nat := 4983230072969 + 3 ^ 40 * 4996503 * 2
def baseEnd_4996503 : Nat := 2565607630631769892734007

theorem tailTrace_4996503 : CollatzResearch.WordTrace tailWord_4996503 prefixEnd_4996503 2565607630631769892734007 := by
  unfold tailWord_4996503
  simp only [CollatzResearch.WordTrace]
  refine ⟨182237435817530440620058163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121491623878353627080038775 182237435817530440620058163)
  ·
    refine ⟨273356153726295660930087245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182237435817530440620058163 273356153726295660930087245)
    ·
      refine ⟨102508557647360872848782717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273356153726295660930087245 102508557647360872848782717)
      ·
        refine ⟨38440709117760327318293519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102508557647360872848782717 38440709117760327318293519)
        ·
          refine ⟨57661063676640490977440279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38440709117760327318293519 57661063676640490977440279)
          ·
            refine ⟨86491595514960736466160419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57661063676640490977440279 86491595514960736466160419)
            ·
              refine ⟨129737393272441104699240629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86491595514960736466160419 129737393272441104699240629)
              ·
                refine ⟨12162880619291353565553809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129737393272441104699240629 12162880619291353565553809)
                ·
                  refine ⟨9122160464468515174165357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12162880619291353565553809 9122160464468515174165357)
                  ·
                    refine ⟨3420810174175693190312009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9122160464468515174165357 3420810174175693190312009)
                    ·
                      refine ⟨2565607630631769892734007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420810174175693190312009 2565607630631769892734007)
                      ·
                        rfl

theorem cell23_4996503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_4996503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996503 prefixEnd_4996503 := by exact prefixLift 4996503
  have htrace : WordTrace (prefixWord ++ tailWord_4996503) baseStart_4996503 baseEnd_4996503 := by
    simpa [prefixWord, tailWord_4996503, baseEnd_4996503] using wordTrace_append hprefix tailTrace_4996503
  have hstable : (prefixWord ++ tailWord_4996503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996503).length < 2 ^ (prefixWord ++ tailWord_4996503).sum := by decide
  have hdescent : baseEnd_4996503 < baseStart_4996503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996504 : List Nat := [2, 1, 2, 5, 3, 1, 1, 3, 1, 4]
def baseStart_4996504 : Nat := 118140960795 + 4996504 * 2 ^ 59
def prefixEnd_4996504 : Nat := 4983230072969 + 3 ^ 40 * 4996504 * 2
def baseEnd_4996504 : Nat := 855202714704141462940501

theorem tailTrace_4996504 : CollatzResearch.WordTrace tailWord_4996504 prefixEnd_4996504 855202714704141462940501 := by
  unfold tailWord_4996504
  simp only [CollatzResearch.WordTrace]
  refine ⟨91118736145263408895422283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121491648193684545193896377 91118736145263408895422283)
  ·
    refine ⟨136678104217895113343133425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91118736145263408895422283 136678104217895113343133425)
    ·
      refine ⟨102508578163421335007350069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136678104217895113343133425 102508578163421335007350069)
      ·
        refine ⟨9610179202820750156939069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102508578163421335007350069 9610179202820750156939069)
        ·
          refine ⟨3603817201057781308852151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9610179202820750156939069 3603817201057781308852151)
          ·
            refine ⟨5405725801586671963278227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603817201057781308852151 5405725801586671963278227)
            ·
              refine ⟨8108588702380007944917341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5405725801586671963278227 8108588702380007944917341)
              ·
                refine ⟨3040720763392502979344003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8108588702380007944917341 3040720763392502979344003)
                ·
                  refine ⟨4561081145088754469016005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040720763392502979344003 4561081145088754469016005)
                  ·
                    refine ⟨855202714704141462940501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4561081145088754469016005 855202714704141462940501)
                    ·
                      rfl

theorem cell23_4996504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_4996504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996504 prefixEnd_4996504 := by exact prefixLift 4996504
  have htrace : WordTrace (prefixWord ++ tailWord_4996504) baseStart_4996504 baseEnd_4996504 := by
    simpa [prefixWord, tailWord_4996504, baseEnd_4996504] using wordTrace_append hprefix tailTrace_4996504
  have hstable : (prefixWord ++ tailWord_4996504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996504).length < 2 ^ (prefixWord ++ tailWord_4996504).sum := by decide
  have hdescent : baseEnd_4996504 < baseStart_4996504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996516 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_4996516 : Nat := 118140960795 + 4996516 * 2 ^ 59
def prefixEnd_4996516 : Nat := 4983230072969 + 3 ^ 40 * 4996516 * 2
def baseEnd_4996516 : Nat := 2565614305880278341871447

theorem tailTrace_4996516 : CollatzResearch.WordTrace tailWord_4996516 prefixEnd_4996516 2565614305880278341871447 := by
  unfold tailWord_4996516
  simp only [CollatzResearch.WordTrace]
  refine ⟨91118954983241671920140701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121491939977655562560187601 91118954983241671920140701)
  ·
    refine ⟨34169608118715626970052763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91118954983241671920140701 34169608118715626970052763)
    ·
      refine ⟨51254412178073440455079145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34169608118715626970052763 51254412178073440455079145)
      ·
        refine ⟨38440809133555080341309359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51254412178073440455079145 38440809133555080341309359)
        ·
          refine ⟨57661213700332620511964039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38440809133555080341309359 57661213700332620511964039)
          ·
            refine ⟨86491820550498930767946059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57661213700332620511964039 86491820550498930767946059)
            ·
              refine ⟨129737730825748396151919089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86491820550498930767946059 129737730825748396151919089)
              ·
                refine ⟨97303298119311297113939317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129737730825748396151919089 97303298119311297113939317)
                ·
                  refine ⟨9122184198685434104431811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97303298119311297113939317 9122184198685434104431811)
                  ·
                    refine ⟨13683276298028151156647717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9122184198685434104431811 13683276298028151156647717)
                    ·
                      refine ⟨2565614305880278341871447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13683276298028151156647717 2565614305880278341871447)
                      ·
                        rfl

theorem cell23_4996516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_4996516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996516 prefixEnd_4996516 := by exact prefixLift 4996516
  have htrace : WordTrace (prefixWord ++ tailWord_4996516) baseStart_4996516 baseEnd_4996516 := by
    simpa [prefixWord, tailWord_4996516, baseEnd_4996516] using wordTrace_append hprefix tailTrace_4996516
  have hstable : (prefixWord ++ tailWord_4996516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996516).length < 2 ^ (prefixWord ++ tailWord_4996516).sum := by decide
  have hdescent : baseEnd_4996516 < baseStart_4996516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996536 : List Nat := [2, 1, 2, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_4996536 : Nat := 118140960795 + 4996536 * 2 ^ 59
def prefixEnd_4996536 : Nat := 4983230072969 + 3 ^ 40 * 4996536 * 2
def baseEnd_4996536 : Nat := 2565624575493368263621355

theorem tailTrace_4996536 : CollatzResearch.WordTrace tailWord_4996536 prefixEnd_4996536 2565624575493368263621355 := by
  unfold tailWord_4996536
  simp only [CollatzResearch.WordTrace]
  refine ⟨91119319713205443628004731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121492426284273924837339641 91119319713205443628004731)
  ·
    refine ⟨136678979569808165442007097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91119319713205443628004731 136678979569808165442007097)
    ·
      refine ⟨102509234677356124081505323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136678979569808165442007097 102509234677356124081505323)
      ·
        refine ⟨153763852016034186122257985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102509234677356124081505323 153763852016034186122257985)
        ·
          refine ⟨115322889012025639591693489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153763852016034186122257985 115322889012025639591693489)
          ·
            refine ⟨86492166759019229693770117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115322889012025639591693489 86492166759019229693770117)
            ·
              refine ⟨16217281267316105567581897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86492166759019229693770117 16217281267316105567581897)
              ·
                refine ⟨12162960950487079175686423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16217281267316105567581897 12162960950487079175686423)
                ·
                  refine ⟨18244441425730618763529635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12162960950487079175686423 18244441425730618763529635)
                  ·
                    refine ⟨27366662138595928145294453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18244441425730618763529635 27366662138595928145294453)
                    ·
                      refine ⟨2565624575493368263621355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27366662138595928145294453 2565624575493368263621355)
                      ·
                        rfl

theorem cell23_4996536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_4996536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996536 prefixEnd_4996536 := by exact prefixLift 4996536
  have htrace : WordTrace (prefixWord ++ tailWord_4996536) baseStart_4996536 baseEnd_4996536 := by
    simpa [prefixWord, tailWord_4996536, baseEnd_4996536] using wordTrace_append hprefix tailTrace_4996536
  have hstable : (prefixWord ++ tailWord_4996536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996536).length < 2 ^ (prefixWord ++ tailWord_4996536).sum := by decide
  have hdescent : baseEnd_4996536 < baseStart_4996536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996556 : List Nat := [2, 2, 1, 4, 2, 1, 2, 9]
def baseStart_4996556 : Nat := 118140960795 + 4996556 * 2 ^ 59
def prefixEnd_4996556 : Nat := 4983230072969 + 3 ^ 40 * 4996556 * 2
def baseEnd_4996556 : Nat := 95023512781720673532269

theorem tailTrace_4996556 : CollatzResearch.WordTrace tailWord_4996556 prefixEnd_4996556 95023512781720673532269 := by
  unfold tailWord_4996556
  simp only [CollatzResearch.WordTrace]
  refine ⟨91119684443169215335868761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121492912590892287114491681 91119684443169215335868761)
  ·
    refine ⟨68339763332376911501901571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91119684443169215335868761 68339763332376911501901571)
    ·
      refine ⟨102509644998565367252852357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68339763332376911501901571 102509644998565367252852357)
      ·
        refine ⟨19220558437231006359909817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102509644998565367252852357 19220558437231006359909817)
        ·
          refine ⟨14415418827923254769932363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19220558437231006359909817 14415418827923254769932363)
          ·
            refine ⟨21623128241884882154898545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14415418827923254769932363 21623128241884882154898545)
            ·
              refine ⟨16217346181413661616173909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21623128241884882154898545 16217346181413661616173909)
              ·
                refine ⟨95023512781720673532269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16217346181413661616173909 95023512781720673532269)
                ·
                  rfl

theorem cell23_4996556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 9].length) (baseStart_4996556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996556 prefixEnd_4996556 := by exact prefixLift 4996556
  have htrace : WordTrace (prefixWord ++ tailWord_4996556) baseStart_4996556 baseEnd_4996556 := by
    simpa [prefixWord, tailWord_4996556, baseEnd_4996556] using wordTrace_append hprefix tailTrace_4996556
  have hstable : (prefixWord ++ tailWord_4996556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996556).length < 2 ^ (prefixWord ++ tailWord_4996556).sum := by decide
  have hdescent : baseEnd_4996556 < baseStart_4996556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996600 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 2, 1, 3]
def baseStart_4996600 : Nat := 118140960795 + 4996600 * 2 ^ 59
def prefixEnd_4996600 : Nat := 4983230072969 + 3 ^ 40 * 4996600 * 2
def baseEnd_4996600 : Nat := 2565657438255256013221061

theorem tailTrace_4996600 : CollatzResearch.WordTrace tailWord_4996600 prefixEnd_4996600 2565657438255256013221061 := by
  unfold tailWord_4996600
  simp only [CollatzResearch.WordTrace]
  refine ⟨91120486849089513093169627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121493982465452684124226169 91120486849089513093169627)
  ·
    refine ⟨136680730273634269639754441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91120486849089513093169627 136680730273634269639754441)
    ·
      refine ⟨102510547705225702229815831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136680730273634269639754441 102510547705225702229815831)
      ·
        refine ⟨153765821557838553344723747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102510547705225702229815831 153765821557838553344723747)
        ·
          refine ⟨230648732336757830017085621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153765821557838553344723747 230648732336757830017085621)
          ·
            refine ⟨21623318656571046564101777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230648732336757830017085621 21623318656571046564101777)
            ·
              refine ⟨16217488992428284923076333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21623318656571046564101777 16217488992428284923076333)
              ·
                refine ⟨6081558372160606846153625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16217488992428284923076333 6081558372160606846153625)
                ·
                  refine ⟨4561168779120455134615219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6081558372160606846153625 4561168779120455134615219)
                  ·
                    refine ⟨6841753168680682701922829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4561168779120455134615219 6841753168680682701922829)
                    ·
                      refine ⟨2565657438255256013221061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6841753168680682701922829 2565657438255256013221061)
                      ·
                        rfl

theorem cell23_4996600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_4996600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996600 prefixEnd_4996600 := by exact prefixLift 4996600
  have htrace : WordTrace (prefixWord ++ tailWord_4996600) baseStart_4996600 baseEnd_4996600 := by
    simpa [prefixWord, tailWord_4996600, baseEnd_4996600] using wordTrace_append hprefix tailTrace_4996600
  have hstable : (prefixWord ++ tailWord_4996600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996600).length < 2 ^ (prefixWord ++ tailWord_4996600).sum := by decide
  have hdescent : baseEnd_4996600 < baseStart_4996600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996627 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 1, 3, 2]
def baseStart_4996627 : Nat := 118140960795 + 4996627 * 2 ^ 59
def prefixEnd_4996627 : Nat := 4983230072969 + 3 ^ 40 * 4996627 * 2
def baseEnd_4996627 : Nat := 2565671302232927407583437

theorem tailTrace_4996627 : CollatzResearch.WordTrace tailWord_4996627 prefixEnd_4996627 2565671302232927407583437 := by
  unfold tailWord_4996627
  simp only [CollatzResearch.WordTrace]
  refine ⟨182241958469081209797572135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121494638979387473198381423 182241958469081209797572135)
  ·
    refine ⟨273362937703621814696358203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182241958469081209797572135 273362937703621814696358203)
    ·
      refine ⟨410044406555432722044537305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273362937703621814696358203 410044406555432722044537305)
      ·
        refine ⟨307533304916574541533402979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410044406555432722044537305 307533304916574541533402979)
        ·
          refine ⟨461299957374861812300104469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307533304916574541533402979 461299957374861812300104469)
          ·
            refine ⟨21623435501946647451567397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 461299957374861812300104469 21623435501946647451567397)
            ·
              refine ⟨4054394156614996397168887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21623435501946647451567397 4054394156614996397168887)
              ·
                refine ⟨6081591234922494595753331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054394156614996397168887 6081591234922494595753331)
                ·
                  refine ⟨9122386852383741893629997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6081591234922494595753331 9122386852383741893629997)
                  ·
                    refine ⟨3420895069643903210111249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9122386852383741893629997 3420895069643903210111249)
                    ·
                      refine ⟨2565671302232927407583437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420895069643903210111249 2565671302232927407583437)
                      ·
                        rfl

theorem cell23_4996627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 3, 2].length) (baseStart_4996627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996627 prefixEnd_4996627 := by exact prefixLift 4996627
  have htrace : WordTrace (prefixWord ++ tailWord_4996627) baseStart_4996627 baseEnd_4996627 := by
    simpa [prefixWord, tailWord_4996627, baseEnd_4996627] using wordTrace_append hprefix tailTrace_4996627
  have hstable : (prefixWord ++ tailWord_4996627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996627).length < 2 ^ (prefixWord ++ tailWord_4996627).sum := by decide
  have hdescent : baseEnd_4996627 < baseStart_4996627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996683 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 7, 2]
def baseStart_4996683 : Nat := 118140960795 + 4996683 * 2 ^ 59
def prefixEnd_4996683 : Nat := 4983230072969 + 3 ^ 40 * 4996683 * 2
def baseEnd_4996683 : Nat := 2565700057149579188483179

theorem tailTrace_4996683 : CollatzResearch.WordTrace tailWord_4996683 prefixEnd_4996683 2565700057149579188483179 := by
  unfold tailWord_4996683
  simp only [CollatzResearch.WordTrace]
  refine ⟨182244000956878331361610703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121496000637918887574407135 182244000956878331361610703)
  ·
    refine ⟨273366001435317497042416055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182244000956878331361610703 273366001435317497042416055)
    ·
      refine ⟨410049002152976245563624083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273366001435317497042416055 410049002152976245563624083)
      ·
        refine ⟨615073503229464368345436125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410049002152976245563624083 615073503229464368345436125)
        ·
          refine ⟨230652563711049138129538547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 615073503229464368345436125 230652563711049138129538547)
          ·
            refine ⟨345978845566573707194307821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230652563711049138129538547 345978845566573707194307821)
            ·
              refine ⟨129742067087465140197865433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345978845566573707194307821 129742067087465140197865433)
              ·
                refine ⟨97306550315598855148399075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129742067087465140197865433 97306550315598855148399075)
                ·
                  refine ⟨145959825473398282722598613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97306550315598855148399075 145959825473398282722598613)
                  ·
                    refine ⟨3420933409532772251310905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 145959825473398282722598613 3420933409532772251310905)
                    ·
                      refine ⟨2565700057149579188483179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3420933409532772251310905 2565700057149579188483179)
                      ·
                        rfl

theorem cell23_4996683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 7, 2].length) (baseStart_4996683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996683 prefixEnd_4996683 := by exact prefixLift 4996683
  have htrace : WordTrace (prefixWord ++ tailWord_4996683) baseStart_4996683 baseEnd_4996683 := by
    simpa [prefixWord, tailWord_4996683, baseEnd_4996683] using wordTrace_append hprefix tailTrace_4996683
  have hstable : (prefixWord ++ tailWord_4996683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996683).length < 2 ^ (prefixWord ++ tailWord_4996683).sum := by decide
  have hdescent : baseEnd_4996683 < baseStart_4996683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996783 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 3, 5]
def baseStart_4996783 : Nat := 118140960795 + 4996783 * 2 ^ 59
def prefixEnd_4996783 : Nat := 4983230072969 + 3 ^ 40 * 4996783 * 2
def baseEnd_4996783 : Nat := 855250468405009599077573

theorem tailTrace_4996783 : CollatzResearch.WordTrace tailWord_4996783 prefixEnd_4996783 855250468405009599077573 := by
  unfold tailWord_4996783
  simp only [CollatzResearch.WordTrace]
  refine ⟨182247648256516048440251003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121498432171010698960167335 182247648256516048440251003)
  ·
    refine ⟨273371472384774072660376505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182247648256516048440251003 273371472384774072660376505)
    ·
      refine ⟨205028604288580554495282379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273371472384774072660376505 205028604288580554495282379)
      ·
        refine ⟨307542906432870831742923569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205028604288580554495282379 307542906432870831742923569)
        ·
          refine ⟨230657179824653123807192677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307542906432870831742923569 230657179824653123807192677)
          ·
            refine ⟨43248221217122460713848627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230657179824653123807192677 43248221217122460713848627)
            ·
              refine ⟨64872331825683691070772941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43248221217122460713848627 64872331825683691070772941)
              ·
                refine ⟨24327124434631384151539853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64872331825683691070772941 24327124434631384151539853)
                ·
                  refine ⟨9122671662986769056827445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24327124434631384151539853 9122671662986769056827445)
                  ·
                    refine ⟨855250468405009599077573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9122671662986769056827445 855250468405009599077573)
                    ·
                      rfl

theorem cell23_4996783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_4996783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996783 prefixEnd_4996783 := by exact prefixLift 4996783
  have htrace : WordTrace (prefixWord ++ tailWord_4996783) baseStart_4996783 baseEnd_4996783 := by
    simpa [prefixWord, tailWord_4996783, baseEnd_4996783] using wordTrace_append hprefix tailTrace_4996783
  have hstable : (prefixWord ++ tailWord_4996783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996783).length < 2 ^ (prefixWord ++ tailWord_4996783).sum := by decide
  have hdescent : baseEnd_4996783 < baseStart_4996783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996800 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 1, 5]
def baseStart_4996800 : Nat := 118140960795 + 4996800 * 2 ^ 59
def prefixEnd_4996800 : Nat := 4983230072969 + 3 ^ 40 * 4996800 * 2
def baseEnd_4996800 : Nat := 855253378128718410240047

theorem tailTrace_4996800 : CollatzResearch.WordTrace tailWord_4996800 prefixEnd_4996800 855253378128718410240047 := by
  unfold tailWord_4996800
  simp only [CollatzResearch.WordTrace]
  refine ⟨91124134148727230171809927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121498845531636306895746569 91124134148727230171809927)
  ·
    refine ⟨136686201223090845257714891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91124134148727230171809927 136686201223090845257714891)
    ·
      refine ⟨205029301834636267886572337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136686201223090845257714891 205029301834636267886572337)
      ·
        refine ⟨153771976375977200914929253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205029301834636267886572337 153771976375977200914929253)
        ·
          refine ⟨28832245570495725171549235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153771976375977200914929253 28832245570495725171549235)
          ·
            refine ⟨43248368355743587757323853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28832245570495725171549235 43248368355743587757323853)
            ·
              refine ⟨16218138133403845408996445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43248368355743587757323853 16218138133403845408996445)
              ·
                refine ⟨6081801800026442028373667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16218138133403845408996445 6081801800026442028373667)
                ·
                  refine ⟨9122702700039663042560501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6081801800026442028373667 9122702700039663042560501)
                  ·
                    refine ⟨855253378128718410240047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9122702700039663042560501 855253378128718410240047)
                    ·
                      rfl

theorem cell23_4996800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_4996800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996800 prefixEnd_4996800 := by exact prefixLift 4996800
  have htrace : WordTrace (prefixWord ++ tailWord_4996800) baseStart_4996800 baseEnd_4996800 := by
    simpa [prefixWord, tailWord_4996800, baseEnd_4996800] using wordTrace_append hprefix tailTrace_4996800
  have hstable : (prefixWord ++ tailWord_4996800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996800).length < 2 ^ (prefixWord ++ tailWord_4996800).sum := by decide
  have hdescent : baseEnd_4996800 < baseStart_4996800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996814 : List Nat := [4, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_4996814 : Nat := 118140960795 + 4996814 * 2 ^ 59
def prefixEnd_4996814 : Nat := 4983230072969 + 3 ^ 40 * 4996814 * 2
def baseEnd_4996814 : Nat := 2565767323115318175945077

theorem tailTrace_4996814 : CollatzResearch.WordTrace tailWord_4996814 prefixEnd_4996814 2565767323115318175945077 := by
  unfold tailWord_4996814
  simp only [CollatzResearch.WordTrace]
  refine ⟨22781097364925467591828687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121499185946269160489752997 22781097364925467591828687)
  ·
    refine ⟨34171646047388201387743031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22781097364925467591828687 34171646047388201387743031)
    ·
      refine ⟨51257469071082302081614547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34171646047388201387743031 51257469071082302081614547)
      ·
        refine ⟨76886203606623453122421821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51257469071082302081614547 76886203606623453122421821)
        ·
          refine ⟨28832326352483794920908183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76886203606623453122421821 28832326352483794920908183)
          ·
            refine ⟨43248489528725692381362275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28832326352483794920908183 43248489528725692381362275)
            ·
              refine ⟨64872734293088538572043413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43248489528725692381362275 64872734293088538572043413)
              ·
                refine ⟨3040909419988525245564535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64872734293088538572043413 3040909419988525245564535)
                ·
                  refine ⟨4561364129982787868346803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040909419988525245564535 4561364129982787868346803)
                  ·
                    refine ⟨6842046194974181802520205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4561364129982787868346803 6842046194974181802520205)
                    ·
                      refine ⟨2565767323115318175945077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6842046194974181802520205 2565767323115318175945077)
                      ·
                        rfl

theorem cell23_4996814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_4996814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996814 prefixEnd_4996814 := by exact prefixLift 4996814
  have htrace : WordTrace (prefixWord ++ tailWord_4996814) baseStart_4996814 baseEnd_4996814 := by
    simpa [prefixWord, tailWord_4996814, baseEnd_4996814] using wordTrace_append hprefix tailTrace_4996814
  have hstable : (prefixWord ++ tailWord_4996814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996814).length < 2 ^ (prefixWord ++ tailWord_4996814).sum := by decide
  have hdescent : baseEnd_4996814 < baseStart_4996814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996837 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4996837 : Nat := 118140960795 + 4996837 * 2 ^ 59
def prefixEnd_4996837 : Nat := 4983230072969 + 3 ^ 40 * 4996837 * 2
def baseEnd_4996837 : Nat := 2565779133170371585957471

theorem tailTrace_4996837 : CollatzResearch.WordTrace tailWord_4996837 prefixEnd_4996837 2565779133170371585957471 := by
  unfold tailWord_4996837
  simp only [CollatzResearch.WordTrace]
  refine ⟨182249617798320415662716765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121499745198880277108477843 182249617798320415662716765)
  ·
    refine ⟨68343606674370155873518787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182249617798320415662716765 68343606674370155873518787)
    ·
      refine ⟨102515410011555233810278181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68343606674370155873518787 102515410011555233810278181)
      ·
        refine ⟨19221639377166606339427159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102515410011555233810278181 19221639377166606339427159)
        ·
          refine ⟨28832459065749909509140739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19221639377166606339427159 28832459065749909509140739)
          ·
            refine ⟨43248688598624864263711109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28832459065749909509140739 43248688598624864263711109)
            ·
              refine ⟨8109129112242162049445833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43248688598624864263711109 8109129112242162049445833)
              ·
                refine ⟨6081846834181621537084375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8109129112242162049445833 6081846834181621537084375)
                ·
                  refine ⟨9122770251272432305626563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6081846834181621537084375 9122770251272432305626563)
                  ·
                    refine ⟨13684155376908648458439845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9122770251272432305626563 13684155376908648458439845)
                    ·
                      refine ⟨2565779133170371585957471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13684155376908648458439845 2565779133170371585957471)
                      ·
                        rfl

theorem cell23_4996837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4996837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996837 prefixEnd_4996837 := by exact prefixLift 4996837
  have htrace : WordTrace (prefixWord ++ tailWord_4996837) baseStart_4996837 baseEnd_4996837 := by
    simpa [prefixWord, tailWord_4996837, baseEnd_4996837] using wordTrace_append hprefix tailTrace_4996837
  have hstable : (prefixWord ++ tailWord_4996837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996837).length < 2 ^ (prefixWord ++ tailWord_4996837).sum := by decide
  have hdescent : baseEnd_4996837 < baseStart_4996837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996850 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4996850 : Nat := 118140960795 + 4996850 * 2 ^ 59
def prefixEnd_4996850 : Nat := 4983230072969 + 3 ^ 40 * 4996850 * 2
def baseEnd_4996850 : Nat := 2565785808418880035094911

theorem tailTrace_4996850 : CollatzResearch.WordTrace tailWord_4996850 prefixEnd_4996850 2565785808418880035094911 := by
  unfold tailWord_4996850
  simp only [CollatzResearch.WordTrace]
  refine ⟨45562522986818329720735001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121500061298182212588626669 45562522986818329720735001)
  ·
    refine ⟨34171892240113747290551251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45562522986818329720735001 34171892240113747290551251)
    ·
      refine ⟨51257838360170620935826877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34171892240113747290551251 51257838360170620935826877)
      ·
        refine ⟨19221689385063982850935079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51257838360170620935826877 19221689385063982850935079)
        ·
          refine ⟨28832534077595974276402619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19221689385063982850935079 28832534077595974276402619)
          ·
            refine ⟨43248801116393961414603929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28832534077595974276402619 43248801116393961414603929)
            ·
              refine ⟨32436600837295471060952947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43248801116393961414603929 32436600837295471060952947)
              ·
                refine ⟨48654901255943206591429421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32436600837295471060952947 48654901255943206591429421)
                ·
                  refine ⟨18245587970978702471786033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48654901255943206591429421 18245587970978702471786033)
                  ·
                    refine ⟨13684190978234026853839525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18245587970978702471786033 13684190978234026853839525)
                    ·
                      refine ⟨2565785808418880035094911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13684190978234026853839525 2565785808418880035094911)
                      ·
                        rfl

theorem cell23_4996850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4996850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996850 prefixEnd_4996850 := by exact prefixLift 4996850
  have htrace : WordTrace (prefixWord ++ tailWord_4996850) baseStart_4996850 baseEnd_4996850 := by
    simpa [prefixWord, tailWord_4996850, baseEnd_4996850] using wordTrace_append hprefix tailTrace_4996850
  have hstable : (prefixWord ++ tailWord_4996850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996850).length < 2 ^ (prefixWord ++ tailWord_4996850).sum := by decide
  have hdescent : baseEnd_4996850 < baseStart_4996850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996873 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 2, 7]
def baseStart_4996873 : Nat := 118140960795 + 4996873 * 2 ^ 59
def prefixEnd_4996873 : Nat := 4983230072969 + 3 ^ 40 * 4996873 * 2
def baseEnd_4996873 : Nat := 855265872824644481702435

theorem tailTrace_4996873 : CollatzResearch.WordTrace tailWord_4996873 prefixEnd_4996873 855265872824644481702435 := by
  unfold tailWord_4996873
  simp only [CollatzResearch.WordTrace]
  refine ⟨182250930826189993811027273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121500620550793329207351515 182250930826189993811027273)
  ·
    refine ⟨136688198119642495358270455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182250930826189993811027273 136688198119642495358270455)
    ·
      refine ⟨205032297179463743037405683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136688198119642495358270455 205032297179463743037405683)
      ·
        refine ⟨307548445769195614556108525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205032297179463743037405683 307548445769195614556108525)
        ·
          refine ⟨115330667163448355458540697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307548445769195614556108525 115330667163448355458540697)
          ·
            refine ⟨86498000372586266593905523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115330667163448355458540697 86498000372586266593905523)
            ·
              refine ⟨129747000558879399890858285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86498000372586266593905523 129747000558879399890858285)
              ·
                refine ⟨48655125209579774959071857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129747000558879399890858285 48655125209579774959071857)
                ·
                  refine ⟨36491343907184831219303893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48655125209579774959071857 36491343907184831219303893)
                  ·
                    refine ⟨855265872824644481702435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36491343907184831219303893 855265872824644481702435)
                    ·
                      rfl

theorem cell23_4996873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_4996873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996873 prefixEnd_4996873 := by exact prefixLift 4996873
  have htrace : WordTrace (prefixWord ++ tailWord_4996873) baseStart_4996873 baseEnd_4996873 := by
    simpa [prefixWord, tailWord_4996873, baseEnd_4996873] using wordTrace_append hprefix tailTrace_4996873
  have hstable : (prefixWord ++ tailWord_4996873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996873).length < 2 ^ (prefixWord ++ tailWord_4996873).sum := by decide
  have hdescent : baseEnd_4996873 < baseStart_4996873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4996883 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5]
def baseStart_4996883 : Nat := 118140960795 + 4996883 * 2 ^ 59
def prefixEnd_4996883 : Nat := 4983230072969 + 3 ^ 40 * 4996883 * 2
def baseEnd_4996883 : Nat := 2565802753280478405982259

theorem tailTrace_4996883 : CollatzResearch.WordTrace tailWord_4996883 prefixEnd_4996883 2565802753280478405982259 := by
  unfold tailWord_4996883
  simp only [CollatzResearch.WordTrace]
  refine ⟨182251295556153765518891303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121500863704102510345927535 182251295556153765518891303)
  ·
    refine ⟨273376943334230648278336955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182251295556153765518891303 273376943334230648278336955)
    ·
      refine ⟨410065415001345972417505433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273376943334230648278336955 410065415001345972417505433)
      ·
        refine ⟨307549061251009479313129075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410065415001345972417505433 307549061251009479313129075)
        ·
          refine ⟨461323591876514218969693613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307549061251009479313129075 461323591876514218969693613)
          ·
            refine ⟨172996346953692832113635105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461323591876514218969693613 172996346953692832113635105)
            ·
              refine ⟨129747260215269624085226329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172996346953692832113635105 129747260215269624085226329)
              ·
                refine ⟨97310445161452218063919747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129747260215269624085226329 97310445161452218063919747)
                ·
                  refine ⟨145965667742178327095879621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97310445161452218063919747 145965667742178327095879621)
                  ·
                    refine ⟨27368562701658436330477429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145965667742178327095879621 27368562701658436330477429)
                    ·
                      refine ⟨2565802753280478405982259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27368562701658436330477429 2565802753280478405982259)
                      ·
                        rfl

theorem cell23_4996883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_4996883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4996883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4996883 prefixEnd_4996883 := by exact prefixLift 4996883
  have htrace : WordTrace (prefixWord ++ tailWord_4996883) baseStart_4996883 baseEnd_4996883 := by
    simpa [prefixWord, tailWord_4996883, baseEnd_4996883] using wordTrace_append hprefix tailTrace_4996883
  have hstable : (prefixWord ++ tailWord_4996883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4996883).length < 2 ^ (prefixWord ++ tailWord_4996883).sum := by decide
  have hdescent : baseEnd_4996883 < baseStart_4996883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4996883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997017 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 1, 6, 2]
def baseStart_4997017 : Nat := 118140960795 + 4997017 * 2 ^ 59
def prefixEnd_4997017 : Nat := 4983230072969 + 3 ^ 40 * 4997017 * 2
def baseEnd_4997017 : Nat := 2565871559688180881706643

theorem tailTrace_4997017 : CollatzResearch.WordTrace tailWord_4997017 prefixEnd_4997017 2565871559688180881706643 := by
  unfold tailWord_4997017
  simp only [CollatzResearch.WordTrace]
  refine ⟨182256182937668306404269305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121504121958445537602846203 182256182937668306404269305)
  ·
    refine ⟨136692137203251229803201979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182256182937668306404269305 136692137203251229803201979)
    ·
      refine ⟨205038205804876844704802969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136692137203251229803201979 205038205804876844704802969)
      ·
        refine ⟨153778654353657633528602227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205038205804876844704802969 153778654353657633528602227)
        ·
          refine ⟨230667981530486450292903341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153778654353657633528602227 230667981530486450292903341)
          ·
            refine ⟨86500493073932418859838753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230667981530486450292903341 86500493073932418859838753)
            ·
              refine ⟨64875369805449314144879065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86500493073932418859838753 64875369805449314144879065)
              ·
                refine ⟨48656527354086985608659299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64875369805449314144879065 48656527354086985608659299)
                ·
                  refine ⟨72984791031130478412988949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48656527354086985608659299 72984791031130478412988949)
                  ·
                    refine ⟨3421162079584241175608857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72984791031130478412988949 3421162079584241175608857)
                    ·
                      refine ⟨2565871559688180881706643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3421162079584241175608857 2565871559688180881706643)
                      ·
                        rfl

theorem cell23_4997017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_4997017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997017 prefixEnd_4997017 := by exact prefixLift 4997017
  have htrace : WordTrace (prefixWord ++ tailWord_4997017) baseStart_4997017 baseEnd_4997017 := by
    simpa [prefixWord, tailWord_4997017, baseEnd_4997017] using wordTrace_append hprefix tailTrace_4997017
  have hstable : (prefixWord ++ tailWord_4997017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997017).length < 2 ^ (prefixWord ++ tailWord_4997017).sum := by decide
  have hdescent : baseEnd_4997017 < baseStart_4997017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997095 : List Nat := [1, 1, 5, 2, 3, 2, 2, 2, 1, 4]
def baseStart_4997095 : Nat := 118140960795 + 4997095 * 2 ^ 59
def prefixEnd_4997095 : Nat := 4983230072969 + 3 ^ 40 * 4997095 * 2
def baseEnd_4997095 : Nat := 855303870393077192177095

theorem tailTrace_4997095 : CollatzResearch.WordTrace tailWord_4997095 prefixEnd_4997095 855303870393077192177095 := by
  unfold tailWord_4997095
  simp only [CollatzResearch.WordTrace]
  refine ⟨182259027831385725725608739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121506018554257150483739159 182259027831385725725608739)
  ·
    refine ⟨273388541747078588588413109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182259027831385725725608739 273388541747078588588413109)
    ·
      refine ⟨25630175788788617680163729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 273388541747078588588413109 25630175788788617680163729)
      ·
        refine ⟨19222631841591463260122797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25630175788788617680163729 19222631841591463260122797)
        ·
          refine ⟨7208486940596798722546049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19222631841591463260122797 7208486940596798722546049)
          ·
            refine ⟨5406365205447599041909537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7208486940596798722546049 5406365205447599041909537)
            ·
              refine ⟨4054773904085699281432153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5406365205447599041909537 4054773904085699281432153)
              ·
                refine ⟨3041080428064274461074115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4054773904085699281432153 3041080428064274461074115)
                ·
                  refine ⟨4561620642096411691611173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041080428064274461074115 4561620642096411691611173)
                  ·
                    refine ⟨855303870393077192177095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4561620642096411691611173 855303870393077192177095)
                    ·
                      rfl

theorem cell23_4997095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_4997095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997095 prefixEnd_4997095 := by exact prefixLift 4997095
  have htrace : WordTrace (prefixWord ++ tailWord_4997095) baseStart_4997095 baseEnd_4997095 := by
    simpa [prefixWord, tailWord_4997095, baseEnd_4997095] using wordTrace_append hprefix tailTrace_4997095
  have hstable : (prefixWord ++ tailWord_4997095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997095).length < 2 ^ (prefixWord ++ tailWord_4997095).sum := by decide
  have hdescent : baseEnd_4997095 < baseStart_4997095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997117 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_4997117 : Nat := 118140960795 + 4997117 * 2 ^ 59
def prefixEnd_4997117 : Nat := 4983230072969 + 3 ^ 40 * 4997117 * 2
def baseEnd_4997117 : Nat := 855307635917876830152061

theorem tailTrace_4997117 : CollatzResearch.WordTrace tailWord_4997117 prefixEnd_4997117 855307635917876830152061 := by
  unfold tailWord_4997117
  simp only [CollatzResearch.WordTrace]
  refine ⟨182259830237306023482909605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121506553491537348988606403 182259830237306023482909605)
  ·
    refine ⟨34173718169494879403045551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182259830237306023482909605 34173718169494879403045551)
    ·
      refine ⟨51260577254242319104568327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34173718169494879403045551 51260577254242319104568327)
      ·
        refine ⟨76890865881363478656852491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51260577254242319104568327 76890865881363478656852491)
        ·
          refine ⟨115336298822045217985278737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76890865881363478656852491 115336298822045217985278737)
          ·
            refine ⟨86502224116533913488959053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115336298822045217985278737 86502224116533913488959053)
            ·
              refine ⟨32438334043700217558359645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86502224116533913488959053 32438334043700217558359645)
              ·
                refine ⟨12164375266387581584384867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32438334043700217558359645 12164375266387581584384867)
                ·
                  refine ⟨18246562899581372376577301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12164375266387581584384867 18246562899581372376577301)
                  ·
                    refine ⟨855307635917876830152061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18246562899581372376577301 855307635917876830152061)
                    ·
                      rfl

theorem cell23_4997117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_4997117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997117 prefixEnd_4997117 := by exact prefixLift 4997117
  have htrace : WordTrace (prefixWord ++ tailWord_4997117) baseStart_4997117 baseEnd_4997117 := by
    simpa [prefixWord, tailWord_4997117, baseEnd_4997117] using wordTrace_append hprefix tailTrace_4997117
  have hstable : (prefixWord ++ tailWord_4997117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997117).length < 2 ^ (prefixWord ++ tailWord_4997117).sum := by decide
  have hdescent : baseEnd_4997117 < baseStart_4997117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997118 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4997118 : Nat := 118140960795 + 4997118 * 2 ^ 59
def prefixEnd_4997118 : Nat := 4983230072969 + 3 ^ 40 * 4997118 * 2
def baseEnd_4997118 : Nat := 2565923421234284986543679

theorem tailTrace_4997118 : CollatzResearch.WordTrace tailWord_4997118 prefixEnd_4997118 2565923421234284986543679 := by
  unfold tailWord_4997118
  simp only [CollatzResearch.WordTrace]
  refine ⟨22782483338787800081712001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121506577806868267102464005 22782483338787800081712001)
  ·
    refine ⟨17086862504090850061284001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22782483338787800081712001 17086862504090850061284001)
    ·
      refine ⟨12815146878068137545963001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17086862504090850061284001 12815146878068137545963001)
      ·
        refine ⟨9611360158551103159472251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12815146878068137545963001 9611360158551103159472251)
        ·
          refine ⟨14417040237826654739208377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9611360158551103159472251 14417040237826654739208377)
          ·
            refine ⟨10812780178369991054406283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14417040237826654739208377 10812780178369991054406283)
            ·
              refine ⟨16219170267554986581609425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10812780178369991054406283 16219170267554986581609425)
              ·
                refine ⟨12164377700666239936207069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16219170267554986581609425 12164377700666239936207069)
                ·
                  refine ⟨4561641637749839976077651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12164377700666239936207069 4561641637749839976077651)
                  ·
                    refine ⟨6842462456624759964116477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4561641637749839976077651 6842462456624759964116477)
                    ·
                      refine ⟨2565923421234284986543679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6842462456624759964116477 2565923421234284986543679)
                      ·
                        rfl

theorem cell23_4997118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4997118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997118 prefixEnd_4997118 := by exact prefixLift 4997118
  have htrace : WordTrace (prefixWord ++ tailWord_4997118) baseStart_4997118 baseEnd_4997118 := by
    simpa [prefixWord, tailWord_4997118, baseEnd_4997118] using wordTrace_append hprefix tailTrace_4997118
  have hstable : (prefixWord ++ tailWord_4997118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997118).length < 2 ^ (prefixWord ++ tailWord_4997118).sum := by decide
  have hdescent : baseEnd_4997118 < baseStart_4997118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997134 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_4997134 : Nat := 118140960795 + 4997134 * 2 ^ 59
def prefixEnd_4997134 : Nat := 4983230072969 + 3 ^ 40 * 4997134 * 2
def baseEnd_4997134 : Nat := 855310545641585641314535

theorem tailTrace_4997134 : CollatzResearch.WordTrace tailWord_4997134 prefixEnd_4997134 855310545641585641314535 := by
  unfold tailWord_4997134
  simp only [CollatzResearch.WordTrace]
  refine ⟨22782556284780554423284807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121506966852162956924185637 22782556284780554423284807)
  ·
    refine ⟨34173834427170831634927211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22782556284780554423284807 34173834427170831634927211)
    ·
      refine ⟨51260751640756247452390817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34173834427170831634927211 51260751640756247452390817)
      ·
        refine ⟨38445563730567185589293113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51260751640756247452390817 38445563730567185589293113)
        ·
          refine ⟨28834172797925389191969835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38445563730567185589293113 28834172797925389191969835)
          ·
            refine ⟨43251259196888083787954753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28834172797925389191969835 43251259196888083787954753)
            ·
              refine ⟨32438444397666062840966065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43251259196888083787954753 32438444397666062840966065)
              ·
                refine ⟨24328833298249547130724549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32438444397666062840966065 24328833298249547130724549)
                ·
                  refine ⟨4561656243421790087010853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24328833298249547130724549 4561656243421790087010853)
                  ·
                    refine ⟨855310545641585641314535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4561656243421790087010853 855310545641585641314535)
                    ·
                      rfl

theorem cell23_4997134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_4997134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997134 prefixEnd_4997134 := by exact prefixLift 4997134
  have htrace : WordTrace (prefixWord ++ tailWord_4997134) baseStart_4997134 baseEnd_4997134 := by
    simpa [prefixWord, tailWord_4997134, baseEnd_4997134] using wordTrace_append hprefix tailTrace_4997134
  have hstable : (prefixWord ++ tailWord_4997134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997134).length < 2 ^ (prefixWord ++ tailWord_4997134).sum := by decide
  have hdescent : baseEnd_4997134 < baseStart_4997134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997141 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_4997141 : Nat := 118140960795 + 4997141 * 2 ^ 59
def prefixEnd_4997141 : Nat := 4983230072969 + 3 ^ 40 * 4997141 * 2
def baseEnd_4997141 : Nat := 2565935231289338396556073

theorem tailTrace_4997141 : CollatzResearch.WordTrace tailWord_4997141 prefixEnd_4997141 2565935231289338396556073 := by
  unfold tailWord_4997141
  simp only [CollatzResearch.WordTrace]
  refine ⟨182260705589219075581783277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121507137059479383721188851 182260705589219075581783277)
  ·
    refine ⟨68347764595957153343168729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182260705589219075581783277 68347764595957153343168729)
    ·
      refine ⟨51260823446967865007376547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68347764595957153343168729 51260823446967865007376547)
      ·
        refine ⟨76891235170451797511064821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51260823446967865007376547 76891235170451797511064821)
        ·
          refine ⟨7208553297229856016662327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76891235170451797511064821 7208553297229856016662327)
          ·
            refine ⟨10812829945844784024993491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7208553297229856016662327 10812829945844784024993491)
            ·
              refine ⟨16219244918767176037490237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10812829945844784024993491 16219244918767176037490237)
              ·
                refine ⟨6082216844537691014058839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16219244918767176037490237 6082216844537691014058839)
                ·
                  refine ⟨9123325266806536521088259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6082216844537691014058839 9123325266806536521088259)
                  ·
                    refine ⟨13684987900209804781632389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9123325266806536521088259 13684987900209804781632389)
                    ·
                      refine ⟨2565935231289338396556073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13684987900209804781632389 2565935231289338396556073)
                      ·
                        rfl

theorem cell23_4997141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_4997141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997141 prefixEnd_4997141 := by exact prefixLift 4997141
  have htrace : WordTrace (prefixWord ++ tailWord_4997141) baseStart_4997141 baseEnd_4997141 := by
    simpa [prefixWord, tailWord_4997141, baseEnd_4997141] using wordTrace_append hprefix tailTrace_4997141
  have hstable : (prefixWord ++ tailWord_4997141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997141).length < 2 ^ (prefixWord ++ tailWord_4997141).sum := by decide
  have hdescent : baseEnd_4997141 < baseStart_4997141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997207 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 4, 6]
def baseStart_4997207 : Nat := 118140960795 + 4997207 * 2 ^ 59
def prefixEnd_4997207 : Nat := 4983230072969 + 3 ^ 40 * 4997207 * 2
def baseEnd_4997207 : Nat := 855323040337511712776923

theorem tailTrace_4997207 : CollatzResearch.WordTrace tailWord_4997207 prefixEnd_4997207 855323040337511712776923 := by
  unfold tailWord_4997207
  simp only [CollatzResearch.WordTrace]
  refine ⟨182263112806979968853685875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121508741871319979235790583 182263112806979968853685875)
  ·
    refine ⟨273394669210469953280528813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182263112806979968853685875 273394669210469953280528813)
    ·
      refine ⟨102523000953926232480198305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273394669210469953280528813 102523000953926232480198305)
      ·
        refine ⟨76892250715444674360148729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102523000953926232480198305 76892250715444674360148729)
        ·
          refine ⟨57669188036583505770111547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76892250715444674360148729 57669188036583505770111547)
          ·
            refine ⟨86503782054875258655167321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57669188036583505770111547 86503782054875258655167321)
            ·
              refine ⟨64877836541156443991375491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86503782054875258655167321 64877836541156443991375491)
              ·
                refine ⟨97316754811734665987063237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64877836541156443991375491 97316754811734665987063237)
                ·
                  refine ⟨18246891527200249872574357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97316754811734665987063237 18246891527200249872574357)
                  ·
                    refine ⟨855323040337511712776923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18246891527200249872574357 855323040337511712776923)
                    ·
                      rfl

theorem cell23_4997207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_4997207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997207 prefixEnd_4997207 := by exact prefixLift 4997207
  have htrace : WordTrace (prefixWord ++ tailWord_4997207) baseStart_4997207 baseEnd_4997207 := by
    simpa [prefixWord, tailWord_4997207, baseEnd_4997207] using wordTrace_append hprefix tailTrace_4997207
  have hstable : (prefixWord ++ tailWord_4997207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997207).length < 2 ^ (prefixWord ++ tailWord_4997207).sum := by decide
  have hdescent : baseEnd_4997207 < baseStart_4997207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997217 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_4997217 : Nat := 118140960795 + 4997217 * 2 ^ 59
def prefixEnd_4997217 : Nat := 4983230072969 + 3 ^ 40 * 4997217 * 2
def baseEnd_4997217 : Nat := 2565974255819080099205723

theorem tailTrace_4997217 : CollatzResearch.WordTrace tailWord_4997217 prefixEnd_4997217 2565974255819080099205723 := by
  unfold tailWord_4997217
  simp only [CollatzResearch.WordTrace]
  refine ⟨182263477536943740561549905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121508985024629160374366603 182263477536943740561549905)
  ·
    refine ⟨136697608152707805421162429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182263477536943740561549905 136697608152707805421162429)
    ·
      refine ⟨51261603057265427032935911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136697608152707805421162429 51261603057265427032935911)
      ·
        refine ⟨76892404585898140549403867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51261603057265427032935911 76892404585898140549403867)
        ·
          refine ⟨115338606878847210824105801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76892404585898140549403867 115338606878847210824105801)
          ·
            refine ⟨86503955159135408118079351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115338606878847210824105801 86503955159135408118079351)
            ·
              refine ⟨129755932738703112177119027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86503955159135408118079351 129755932738703112177119027)
              ·
                refine ⟨194633899108054668265678541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129755932738703112177119027 194633899108054668265678541)
                ·
                  refine ⟨72987712165520500599629453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194633899108054668265678541 72987712165520500599629453)
                  ·
                    refine ⟨27370392062070187724861045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72987712165520500599629453 27370392062070187724861045)
                    ·
                      refine ⟨2565974255819080099205723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27370392062070187724861045 2565974255819080099205723)
                      ·
                        rfl

theorem cell23_4997217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_4997217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997217 prefixEnd_4997217 := by exact prefixLift 4997217
  have htrace : WordTrace (prefixWord ++ tailWord_4997217) baseStart_4997217 baseEnd_4997217 := by
    simpa [prefixWord, tailWord_4997217, baseEnd_4997217] using wordTrace_append hprefix tailTrace_4997217
  have hstable : (prefixWord ++ tailWord_4997217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997217).length < 2 ^ (prefixWord ++ tailWord_4997217).sum := by decide
  have hdescent : baseEnd_4997217 < baseStart_4997217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997234 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_4997234 : Nat := 118140960795 + 4997234 * 2 ^ 59
def prefixEnd_4997234 : Nat := 4983230072969 + 3 ^ 40 * 4997234 * 2
def baseEnd_4997234 : Nat := 2565982984990206532693145

theorem tailTrace_4997234 : CollatzResearch.WordTrace tailWord_4997234 prefixEnd_4997234 2565982984990206532693145 := by
  unfold tailWord_4997234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45566024394470538116229689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121509398385254768309945837 45566024394470538116229689)
  ·
    refine ⟨34174518295852903587172267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45566024394470538116229689 34174518295852903587172267)
    ·
      refine ⟨51261777443779355380758401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34174518295852903587172267 51261777443779355380758401)
      ·
        refine ⟨38446333082834516535568801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51261777443779355380758401 38446333082834516535568801)
        ·
          refine ⟨28834749812125887401676601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38446333082834516535568801 28834749812125887401676601)
          ·
            refine ⟨21626062359094415551257451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28834749812125887401676601 21626062359094415551257451)
            ·
              refine ⟨32439093538641623326886177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21626062359094415551257451 32439093538641623326886177)
              ·
                refine ⟨24329320153981217495164633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32439093538641623326886177 24329320153981217495164633)
                ·
                  refine ⟨18246990115485913121373475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24329320153981217495164633 18246990115485913121373475)
                  ·
                    refine ⟨27370485173228869682060213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18246990115485913121373475 27370485173228869682060213)
                    ·
                      refine ⟨2565982984990206532693145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27370485173228869682060213 2565982984990206532693145)
                      ·
                        rfl

theorem cell23_4997234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_4997234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997234 prefixEnd_4997234 := by exact prefixLift 4997234
  have htrace : WordTrace (prefixWord ++ tailWord_4997234) baseStart_4997234 baseEnd_4997234 := by
    simpa [prefixWord, tailWord_4997234, baseEnd_4997234] using wordTrace_append hprefix tailTrace_4997234
  have hstable : (prefixWord ++ tailWord_4997234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997234).length < 2 ^ (prefixWord ++ tailWord_4997234).sum := by decide
  have hdescent : baseEnd_4997234 < baseStart_4997234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997264 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3]
def baseStart_4997264 : Nat := 118140960795 + 4997264 * 2 ^ 59
def prefixEnd_4997264 : Nat := 4983230072969 + 3 ^ 40 * 4997264 * 2
def baseEnd_4997264 : Nat := 2565998389409841415318007

theorem tailTrace_4997264 : CollatzResearch.WordTrace tailWord_4997264 prefixEnd_4997264 2565998389409841415318007 := by
  unfold tailWord_4997264
  simp only [CollatzResearch.WordTrace]
  refine ⟨91132595883886733794255423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121510127845182311725673897 91132595883886733794255423)
  ·
    refine ⟨136698893825830100691383135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91132595883886733794255423 136698893825830100691383135)
    ·
      refine ⟨205048340738745151037074703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136698893825830100691383135 205048340738745151037074703)
      ·
        refine ⟨307572511108117726555612055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205048340738745151037074703 307572511108117726555612055)
        ·
          refine ⟨461358766662176589833418083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307572511108117726555612055 461358766662176589833418083)
          ·
            refine ⟨692038149993264884750127125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461358766662176589833418083 692038149993264884750127125)
            ·
              refine ⟨32439288280934291472662209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 692038149993264884750127125 32439288280934291472662209)
              ·
                refine ⟨24329466210700718604496657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32439288280934291472662209 24329466210700718604496657)
                ·
                  refine ⟨18247099658025538953372493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24329466210700718604496657 18247099658025538953372493)
                  ·
                    refine ⟨6842662371759577107514685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18247099658025538953372493 6842662371759577107514685)
                    ·
                      refine ⟨2565998389409841415318007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6842662371759577107514685 2565998389409841415318007)
                      ·
                        rfl

theorem cell23_4997264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_4997264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997264 prefixEnd_4997264 := by exact prefixLift 4997264
  have htrace : WordTrace (prefixWord ++ tailWord_4997264) baseStart_4997264 baseEnd_4997264 := by
    simpa [prefixWord, tailWord_4997264, baseEnd_4997264] using wordTrace_append hprefix tailTrace_4997264
  have hstable : (prefixWord ++ tailWord_4997264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997264).length < 2 ^ (prefixWord ++ tailWord_4997264).sum := by decide
  have hdescent : baseEnd_4997264 < baseStart_4997264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997267 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 3, 7]
def baseStart_4997267 : Nat := 118140960795 + 4997267 * 2 ^ 59
def prefixEnd_4997267 : Nat := 4983230072969 + 3 ^ 40 * 4997267 * 2
def baseEnd_4997267 : Nat := 855333309950601634526831

theorem tailTrace_4997267 : CollatzResearch.WordTrace tailWord_4997267 prefixEnd_4997267 855333309950601634526831 := by
  unfold tailWord_4997267
  simp only [CollatzResearch.WordTrace]
  refine ⟨182265301186762599100870055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121510200791175066067246703 182265301186762599100870055)
  ·
    refine ⟨273397951780143898651305083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182265301186762599100870055 273397951780143898651305083)
    ·
      refine ⟨410096927670215847976957625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273397951780143898651305083 410096927670215847976957625)
      ·
        refine ⟨307572695752661885982718219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410096927670215847976957625 307572695752661885982718219)
        ·
          refine ⟨461359043628992828974077329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307572695752661885982718219 461359043628992828974077329)
          ·
            refine ⟨346019282721744621730557997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461359043628992828974077329 346019282721744621730557997)
            ·
              refine ⟨129757231020654233148959249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346019282721744621730557997 129757231020654233148959249)
              ·
                refine ⟨97317923265490674861719437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129757231020654233148959249 97317923265490674861719437)
                ·
                  refine ⟨36494221224559003073144789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97317923265490674861719437 36494221224559003073144789)
                  ·
                    refine ⟨855333309950601634526831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36494221224559003073144789 855333309950601634526831)
                    ·
                      rfl

theorem cell23_4997267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 7].length) (baseStart_4997267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997267 prefixEnd_4997267 := by exact prefixLift 4997267
  have htrace : WordTrace (prefixWord ++ tailWord_4997267) baseStart_4997267 baseEnd_4997267 := by
    simpa [prefixWord, tailWord_4997267, baseEnd_4997267] using wordTrace_append hprefix tailTrace_4997267
  have hstable : (prefixWord ++ tailWord_4997267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997267).length < 2 ^ (prefixWord ++ tailWord_4997267).sum := by decide
  have hdescent : baseEnd_4997267 < baseStart_4997267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997278 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_4997278 : Nat := 118140960795 + 4997278 * 2 ^ 59
def prefixEnd_4997278 : Nat := 4983230072969 + 3 ^ 40 * 4997278 * 2
def baseEnd_4997278 : Nat := 2566005578139004360542943

theorem tailTrace_4997278 : CollatzResearch.WordTrace tailWord_4997278 prefixEnd_4997278 2566005578139004360542943 := by
  unfold tailWord_4997278
  simp only [CollatzResearch.WordTrace]
  refine ⟨22783212798715343497440061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121510468259815165319680325 22783212798715343497440061)
  ·
    refine ⟨8543704799518253811540023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22783212798715343497440061 8543704799518253811540023)
    ·
      refine ⟨12815557199277380717310035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8543704799518253811540023 12815557199277380717310035)
      ·
        refine ⟨19223335798916071075965053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12815557199277380717310035 19223335798916071075965053)
        ·
          refine ⟨7208750924593526653486895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19223335798916071075965053 7208750924593526653486895)
          ·
            refine ⟨10813126386890289980230343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7208750924593526653486895 10813126386890289980230343)
            ·
              refine ⟨16219689580335434970345515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10813126386890289980230343 16219689580335434970345515)
              ·
                refine ⟨24329534370503152455518273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16219689580335434970345515 24329534370503152455518273)
                ·
                  refine ⟨18247150777877364341638705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24329534370503152455518273 18247150777877364341638705)
                  ·
                    refine ⟨13685363083408023256229029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18247150777877364341638705 13685363083408023256229029)
                    ·
                      refine ⟨2566005578139004360542943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13685363083408023256229029 2566005578139004360542943)
                      ·
                        rfl

theorem cell23_4997278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_4997278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997278 prefixEnd_4997278 := by exact prefixLift 4997278
  have htrace : WordTrace (prefixWord ++ tailWord_4997278) baseStart_4997278 baseEnd_4997278 := by
    simpa [prefixWord, tailWord_4997278, baseEnd_4997278] using wordTrace_append hprefix tailTrace_4997278
  have hstable : (prefixWord ++ tailWord_4997278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997278).length < 2 ^ (prefixWord ++ tailWord_4997278).sum := by decide
  have hdescent : baseEnd_4997278 < baseStart_4997278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997281 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4997281 : Nat := 118140960795 + 4997281 * 2 ^ 59
def prefixEnd_4997281 : Nat := 4983230072969 + 3 ^ 40 * 4997281 * 2
def baseEnd_4997281 : Nat := 2566007118580967848805429

theorem tailTrace_4997281 : CollatzResearch.WordTrace tailWord_4997281 prefixEnd_4997281 2566007118580967848805429 := by
  unfold tailWord_4997281
  simp only [CollatzResearch.WordTrace]
  refine ⟨182265811808711879491879697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121510541205807919661253131 182265811808711879491879697)
  ·
    refine ⟨136699358856533909618909773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182265811808711879491879697 136699358856533909618909773)
    ·
      refine ⟨51262259571200216107091165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136699358856533909618909773 51262259571200216107091165)
      ·
        refine ⟨19223347339200081040159187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51262259571200216107091165 19223347339200081040159187)
        ·
          refine ⟨28835021008800121560238781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19223347339200081040159187 28835021008800121560238781)
          ·
            refine ⟨10813132878300045585089543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28835021008800121560238781 10813132878300045585089543)
            ·
              refine ⟨16219699317450068377634315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10813132878300045585089543 16219699317450068377634315)
              ·
                refine ⟨24329548976175102566451473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16219699317450068377634315 24329548976175102566451473)
                ·
                  refine ⟨18247161732131326924838605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24329548976175102566451473 18247161732131326924838605)
                  ·
                    refine ⟨6842685649549247596814477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18247161732131326924838605 6842685649549247596814477)
                    ·
                      refine ⟨2566007118580967848805429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6842685649549247596814477 2566007118580967848805429)
                      ·
                        rfl

theorem cell23_4997281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4997281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997281 prefixEnd_4997281 := by exact prefixLift 4997281
  have htrace : WordTrace (prefixWord ++ tailWord_4997281) baseStart_4997281 baseEnd_4997281 := by
    simpa [prefixWord, tailWord_4997281, baseEnd_4997281] using wordTrace_append hprefix tailTrace_4997281
  have hstable : (prefixWord ++ tailWord_4997281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997281).length < 2 ^ (prefixWord ++ tailWord_4997281).sum := by decide
  have hdescent : baseEnd_4997281 < baseStart_4997281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997304 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_4997304 : Nat := 118140960795 + 4997304 * 2 ^ 59
def prefixEnd_4997304 : Nat := 4983230072969 + 3 ^ 40 * 4997304 * 2
def baseEnd_4997304 : Nat := 2566018928636021258817823

theorem tailTrace_4997304 : CollatzResearch.WordTrace tailWord_4997304 prefixEnd_4997304 2566018928636021258817823 := by
  unfold tailWord_4997304
  simp only [CollatzResearch.WordTrace]
  refine ⟨91133325343814277209983483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121511100458419036279977977 91133325343814277209983483)
  ·
    refine ⟨136699988015721415814975225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91133325343814277209983483 136699988015721415814975225)
    ·
      refine ⟨102524991011791061861231419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136699988015721415814975225 102524991011791061861231419)
      ·
        refine ⟨153787486517686592791847129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102524991011791061861231419 153787486517686592791847129)
        ·
          refine ⟨115340614888264944593885347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153787486517686592791847129 115340614888264944593885347)
          ·
            refine ⟨173010922332397416890828021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115340614888264944593885347 173010922332397416890828021)
            ·
              refine ⟨16219773968662257833515127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173010922332397416890828021 16219773968662257833515127)
              ·
                refine ⟨24329660952993386750272691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16219773968662257833515127 24329660952993386750272691)
                ·
                  refine ⟨36494491429490080125409037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24329660952993386750272691 36494491429490080125409037)
                  ·
                    refine ⟨13685434286058780047028389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36494491429490080125409037 13685434286058780047028389)
                    ·
                      refine ⟨2566018928636021258817823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13685434286058780047028389 2566018928636021258817823)
                      ·
                        rfl

theorem cell23_4997304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_4997304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997304 prefixEnd_4997304 := by exact prefixLift 4997304
  have htrace : WordTrace (prefixWord ++ tailWord_4997304) baseStart_4997304 baseEnd_4997304 := by
    simpa [prefixWord, tailWord_4997304, baseEnd_4997304] using wordTrace_append hprefix tailTrace_4997304
  have hstable : (prefixWord ++ tailWord_4997304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997304).length < 2 ^ (prefixWord ++ tailWord_4997304).sum := by decide
  have hdescent : baseEnd_4997304 < baseStart_4997304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997381 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 3, 5, 2]
def baseStart_4997381 : Nat := 118140960795 + 4997381 * 2 ^ 59
def prefixEnd_4997381 : Nat := 4983230072969 + 3 ^ 40 * 4997381 * 2
def baseEnd_4997381 : Nat := 2566058466646417457554969

theorem tailTrace_4997381 : CollatzResearch.WordTrace tailWord_4997381 prefixEnd_4997381 2566058466646417457554969 := by
  unfold tailWord_4997381
  simp only [CollatzResearch.WordTrace]
  refine ⟨182269459108349596570519997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121512972738899731047013331 182269459108349596570519997)
  ·
    refine ⟨68351047165631098713944999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182269459108349596570519997 68351047165631098713944999)
    ·
      refine ⟨102526570748446648070917499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68351047165631098713944999 102526570748446648070917499)
      ·
        refine ⟨153789856122669972106376249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102526570748446648070917499 153789856122669972106376249)
        ·
          refine ⟨115342392092002479079782187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153789856122669972106376249 115342392092002479079782187)
          ·
            refine ⟨173013588138003718619673281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115342392092002479079782187 173013588138003718619673281)
            ·
              refine ⟨129760191103502788964754961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173013588138003718619673281 129760191103502788964754961)
              ·
                refine ⟨97320143327627091723566221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129760191103502788964754961 97320143327627091723566221)
                ·
                  refine ⟨36495053747860159396337333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97320143327627091723566221 36495053747860159396337333)
                  ·
                    refine ⟨3421411288861889943406625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36495053747860159396337333 3421411288861889943406625)
                    ·
                      refine ⟨2566058466646417457554969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3421411288861889943406625 2566058466646417457554969)
                      ·
                        rfl

theorem cell23_4997381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_4997381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997381 prefixEnd_4997381 := by exact prefixLift 4997381
  have htrace : WordTrace (prefixWord ++ tailWord_4997381) baseStart_4997381 baseEnd_4997381 := by
    simpa [prefixWord, tailWord_4997381, baseEnd_4997381] using wordTrace_append hprefix tailTrace_4997381
  have hstable : (prefixWord ++ tailWord_4997381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997381).length < 2 ^ (prefixWord ++ tailWord_4997381).sum := by decide
  have hdescent : baseEnd_4997381 < baseStart_4997381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997408 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 1, 5]
def baseStart_4997408 : Nat := 118140960795 + 4997408 * 2 ^ 59
def prefixEnd_4997408 : Nat := 4983230072969 + 3 ^ 40 * 4997408 * 2
def baseEnd_4997408 : Nat := 855357443541362950639115

theorem tailTrace_4997408 : CollatzResearch.WordTrace tailWord_4997408 prefixEnd_4997408 855357443541362950639115 := by
  unfold tailWord_4997408
  simp only [CollatzResearch.WordTrace]
  refine ⟨91135221939625890090876439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121513629252834520121168585 91135221939625890090876439)
  ·
    refine ⟨136702832909438835136314659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91135221939625890090876439 136702832909438835136314659)
    ·
      refine ⟨205054249364158252704471989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136702832909438835136314659 205054249364158252704471989)
      ·
        refine ⟨19223835877889836191044249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205054249364158252704471989 19223835877889836191044249)
        ·
          refine ⟨14417876908417377143283187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19223835877889836191044249 14417876908417377143283187)
          ·
            refine ⟨21626815362626065714924781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14417876908417377143283187 21626815362626065714924781)
            ·
              refine ⟨8110055760984774643096793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21626815362626065714924781 8110055760984774643096793)
              ·
                refine ⟨6082541820738580982322595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8110055760984774643096793 6082541820738580982322595)
                ·
                  refine ⟨9123812731107871473483893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6082541820738580982322595 9123812731107871473483893)
                  ·
                    refine ⟨855357443541362950639115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9123812731107871473483893 855357443541362950639115)
                    ·
                      rfl

theorem cell23_4997408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_4997408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997408 prefixEnd_4997408 := by exact prefixLift 4997408
  have htrace : WordTrace (prefixWord ++ tailWord_4997408) baseStart_4997408 baseEnd_4997408 := by
    simpa [prefixWord, tailWord_4997408, baseEnd_4997408] using wordTrace_append hprefix tailTrace_4997408
  have hstable : (prefixWord ++ tailWord_4997408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997408).length < 2 ^ (prefixWord ++ tailWord_4997408).sum := by decide
  have hdescent : baseEnd_4997408 < baseStart_4997408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997411 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 4]
def baseStart_4997411 : Nat := 118140960795 + 4997411 * 2 ^ 59
def prefixEnd_4997411 : Nat := 4983230072969 + 3 ^ 40 * 4997411 * 2
def baseEnd_4997411 : Nat := 2566073871066052340179831

theorem tailTrace_4997411 : CollatzResearch.WordTrace tailWord_4997411 prefixEnd_4997411 2566073871066052340179831 := by
  unfold tailWord_4997411
  simp only [CollatzResearch.WordTrace]
  refine ⟨182270553298240911694112087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121513702198827274462741391 182270553298240911694112087)
  ·
    refine ⟨273405829947361367541168131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182270553298240911694112087 273405829947361367541168131)
    ·
      refine ⟨410108744921042051311752197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273405829947361367541168131 410108744921042051311752197)
      ·
        refine ⟨76895389672695384620953537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 410108744921042051311752197 76895389672695384620953537)
        ·
          refine ⟨57671542254521538465715153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76895389672695384620953537 57671542254521538465715153)
          ·
            refine ⟨43253656690891153849286365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57671542254521538465715153 43253656690891153849286365)
            ·
              refine ⟨16220121259084182693482387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43253656690891153849286365 16220121259084182693482387)
              ·
                refine ⟨24330181888626274040223581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16220121259084182693482387 24330181888626274040223581)
                ·
                  refine ⟨9123818208234852765083843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24330181888626274040223581 9123818208234852765083843)
                  ·
                    refine ⟨13685727312352279147625765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9123818208234852765083843 13685727312352279147625765)
                    ·
                      refine ⟨2566073871066052340179831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13685727312352279147625765 2566073871066052340179831)
                      ·
                        rfl

theorem cell23_4997411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_4997411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997411 prefixEnd_4997411 := by exact prefixLift 4997411
  have htrace : WordTrace (prefixWord ++ tailWord_4997411) baseStart_4997411 baseEnd_4997411 := by
    simpa [prefixWord, tailWord_4997411, baseEnd_4997411] using wordTrace_append hprefix tailTrace_4997411
  have hstable : (prefixWord ++ tailWord_4997411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997411).length < 2 ^ (prefixWord ++ tailWord_4997411).sum := by decide
  have hdescent : baseEnd_4997411 < baseStart_4997411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997424 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_4997424 : Nat := 118140960795 + 4997424 * 2 ^ 59
def prefixEnd_4997424 : Nat := 4983230072969 + 3 ^ 40 * 4997424 * 2
def baseEnd_4997424 : Nat := 2566080546314560789317271

theorem tailTrace_4997424 : CollatzResearch.WordTrace tailWord_4997424 prefixEnd_4997424 2566080546314560789317271 := by
  unfold tailWord_4997424
  simp only [CollatzResearch.WordTrace]
  refine ⟨91135513723596907457167663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121514018298129209942890217 91135513723596907457167663)
  ·
    refine ⟨136703270585395361185751495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91135513723596907457167663 136703270585395361185751495)
    ·
      refine ⟨205054905878093041778627243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136703270585395361185751495 205054905878093041778627243)
      ·
        refine ⟨307582358817139562667940865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205054905878093041778627243 307582358817139562667940865)
        ·
          refine ⟨230686769112854672000955649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307582358817139562667940865 230686769112854672000955649)
          ·
            refine ⟨173015076834641004000716737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230686769112854672000955649 173015076834641004000716737)
            ·
              refine ⟨129761307625980753000537553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173015076834641004000716737 129761307625980753000537553)
              ·
                refine ⟨97320980719485564750403165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129761307625980753000537553 97320980719485564750403165)
                ·
                  refine ⟨36495367769807086781401187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97320980719485564750403165 36495367769807086781401187)
                  ·
                    refine ⟨54743051654710630172101781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36495367769807086781401187 54743051654710630172101781)
                    ·
                      refine ⟨2566080546314560789317271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54743051654710630172101781 2566080546314560789317271)
                      ·
                        rfl

theorem cell23_4997424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_4997424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997424 prefixEnd_4997424 := by exact prefixLift 4997424
  have htrace : WordTrace (prefixWord ++ tailWord_4997424) baseStart_4997424 baseEnd_4997424 := by
    simpa [prefixWord, tailWord_4997424, baseEnd_4997424] using wordTrace_append hprefix tailTrace_4997424
  have hstable : (prefixWord ++ tailWord_4997424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997424).length < 2 ^ (prefixWord ++ tailWord_4997424).sum := by decide
  have hdescent : baseEnd_4997424 < baseStart_4997424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997425 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 1, 5]
def baseStart_4997425 : Nat := 118140960795 + 4997425 * 2 ^ 59
def prefixEnd_4997425 : Nat := 4983230072969 + 3 ^ 40 * 4997425 * 2
def baseEnd_4997425 : Nat := 855360353265071761801589

theorem tailTrace_4997425 : CollatzResearch.WordTrace tailWord_4997425 prefixEnd_4997425 855360353265071761801589 := by
  unfold tailWord_4997425
  simp only [CollatzResearch.WordTrace]
  refine ⟨182271063920190192085121729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121514042613460128056747819 182271063920190192085121729)
  ·
    refine ⟨136703297940142644063841297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182271063920190192085121729 136703297940142644063841297)
    ·
      refine ⟨102527473455106983047880973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136703297940142644063841297 102527473455106983047880973)
      ·
        refine ⟨38447802545665118642955365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102527473455106983047880973 38447802545665118642955365)
        ·
          refine ⟨7208962977312209745554131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38447802545665118642955365 7208962977312209745554131)
          ·
            refine ⟨10813444465968314618331197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7208962977312209745554131 10813444465968314618331197)
            ·
              refine ⟨4055041674738117981874199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10813444465968314618331197 4055041674738117981874199)
              ·
                refine ⟨6082562512107176972811299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055041674738117981874199 6082562512107176972811299)
                ·
                  refine ⟨9123843768160765459216949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6082562512107176972811299 9123843768160765459216949)
                  ·
                    refine ⟨855360353265071761801589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9123843768160765459216949 855360353265071761801589)
                    ·
                      rfl

theorem cell23_4997425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_4997425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997425 prefixEnd_4997425 := by exact prefixLift 4997425
  have htrace : WordTrace (prefixWord ++ tailWord_4997425) baseStart_4997425 baseEnd_4997425 := by
    simpa [prefixWord, tailWord_4997425, baseEnd_4997425] using wordTrace_append hprefix tailTrace_4997425
  have hstable : (prefixWord ++ tailWord_4997425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997425).length < 2 ^ (prefixWord ++ tailWord_4997425).sum := by decide
  have hdescent : baseEnd_4997425 < baseStart_4997425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997434 : List Nat := [3, 1, 1, 1, 4, 13]
def baseStart_4997434 : Nat := 118140960795 + 4997434 * 2 ^ 59
def prefixEnd_4997434 : Nat := 4983230072969 + 3 ^ 40 * 4997434 * 2
def baseEnd_4997434 : Nat := 10560023379099200618075

theorem tailTrace_4997434 : CollatzResearch.WordTrace tailWord_4997434 prefixEnd_4997434 10560023379099200618075 := by
  unfold tailWord_4997434
  simp only [CollatzResearch.WordTrace]
  refine ⟨45567848044289396655549839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121514261451438391081466237 45567848044289396655549839)
  ·
    refine ⟨68351772066434094983324759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45567848044289396655549839 68351772066434094983324759)
    ·
      refine ⟨102527658099651142474987139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68351772066434094983324759 102527658099651142474987139)
      ·
        refine ⟨153791487149476713712480709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102527658099651142474987139 153791487149476713712480709)
        ·
          refine ⟨28835903840526883821090133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153791487149476713712480709 28835903840526883821090133)
          ·
            refine ⟨10560023379099200618075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 28835903840526883821090133 10560023379099200618075)
            ·
              rfl

theorem cell23_4997434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 13].length) (baseStart_4997434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997434 prefixEnd_4997434 := by exact prefixLift 4997434
  have htrace : WordTrace (prefixWord ++ tailWord_4997434) baseStart_4997434 baseEnd_4997434 := by
    simpa [prefixWord, tailWord_4997434, baseEnd_4997434] using wordTrace_append hprefix tailTrace_4997434
  have hstable : (prefixWord ++ tailWord_4997434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997434).length < 2 ^ (prefixWord ++ tailWord_4997434).sum := by decide
  have hdescent : baseEnd_4997434 < baseStart_4997434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997479 : List Nat := [1, 1, 5, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_4997479 : Nat := 118140960795 + 4997479 * 2 ^ 59
def prefixEnd_4997479 : Nat := 4983230072969 + 3 ^ 40 * 4997479 * 2
def baseEnd_4997479 : Nat := 2566108787750558074129519

theorem tailTrace_4997479 : CollatzResearch.WordTrace tailWord_4997479 prefixEnd_4997479 2566108787750558074129519 := by
  unfold tailWord_4997479
  simp only [CollatzResearch.WordTrace]
  refine ⟨182273033461994559307587491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121515355641329706205058327 182273033461994559307587491)
  ·
    refine ⟨273409550192991838961381237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182273033461994559307587491 273409550192991838961381237)
    ·
      refine ⟨25632145330592984902629491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 273409550192991838961381237 25632145330592984902629491)
      ·
        refine ⟨38448217995889477353944237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25632145330592984902629491 38448217995889477353944237)
        ·
          refine ⟨14418081748458554007729089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38448217995889477353944237 14418081748458554007729089)
          ·
            refine ⟨10813561311343915505796817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14418081748458554007729089 10813561311343915505796817)
            ·
              refine ⟨8110170983507936629347613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10813561311343915505796817 8110170983507936629347613)
              ·
                refine ⟨3041314118815476236005355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8110170983507936629347613 3041314118815476236005355)
                ·
                  refine ⟨4561971178223214354008033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041314118815476236005355 4561971178223214354008033)
                  ·
                    refine ⟨3421478383667410765506025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4561971178223214354008033 3421478383667410765506025)
                    ·
                      refine ⟨2566108787750558074129519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3421478383667410765506025 2566108787750558074129519)
                      ·
                        rfl

theorem cell23_4997479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_4997479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997479 prefixEnd_4997479 := by exact prefixLift 4997479
  have htrace : WordTrace (prefixWord ++ tailWord_4997479) baseStart_4997479 baseEnd_4997479 := by
    simpa [prefixWord, tailWord_4997479, baseEnd_4997479] using wordTrace_append hprefix tailTrace_4997479
  have hstable : (prefixWord ++ tailWord_4997479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997479).length < 2 ^ (prefixWord ++ tailWord_4997479).sum := by decide
  have hdescent : baseEnd_4997479 < baseStart_4997479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997482 : List Nat := [3, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4997482 : Nat := 118140960795 + 4997482 * 2 ^ 59
def prefixEnd_4997482 : Nat := 4983230072969 + 3 ^ 40 * 4997482 * 2
def baseEnd_4997482 : Nat := 2566110328192521562392005

theorem tailTrace_4997482 : CollatzResearch.WordTrace tailWord_4997482 prefixEnd_4997482 2566110328192521562392005 := by
  unfold tailWord_4997482
  simp only [CollatzResearch.WordTrace]
  refine ⟨45568285720245922704986675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121515428587322460546631133 45568285720245922704986675)
  ·
    refine ⟨68352428580368884057480013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45568285720245922704986675 68352428580368884057480013)
    ·
      refine ⟨25632160717638331521555005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68352428580368884057480013 25632160717638331521555005)
      ·
        refine ⟨9612060269114374320583127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25632160717638331521555005 9612060269114374320583127)
        ·
          refine ⟨14418090403671561480874691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9612060269114374320583127 14418090403671561480874691)
          ·
            refine ⟨21627135605507342221312037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14418090403671561480874691 21627135605507342221312037)
            ·
              refine ⟨4055087926032626666496007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21627135605507342221312037 4055087926032626666496007)
              ·
                refine ⟨6082631889048939999744011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055087926032626666496007 6082631889048939999744011)
                ·
                  refine ⟨9123947833573409999616017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6082631889048939999744011 9123947833573409999616017)
                  ·
                    refine ⟨6842960875180057499712013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9123947833573409999616017 6842960875180057499712013)
                    ·
                      refine ⟨2566110328192521562392005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6842960875180057499712013 2566110328192521562392005)
                      ·
                        rfl

theorem cell23_4997482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4997482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997482 prefixEnd_4997482 := by exact prefixLift 4997482
  have htrace : WordTrace (prefixWord ++ tailWord_4997482) baseStart_4997482 baseEnd_4997482 := by
    simpa [prefixWord, tailWord_4997482, baseEnd_4997482] using wordTrace_append hprefix tailTrace_4997482
  have hstable : (prefixWord ++ tailWord_4997482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997482).length < 2 ^ (prefixWord ++ tailWord_4997482).sum := by decide
  have hdescent : baseEnd_4997482 < baseStart_4997482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997511 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 2, 6]
def baseStart_4997511 : Nat := 118140960795 + 4997511 * 2 ^ 59
def prefixEnd_4997511 : Nat := 4983230072969 + 3 ^ 40 * 4997511 * 2
def baseEnd_4997511 : Nat := 855375073043833982976457

theorem tailTrace_4997511 : CollatzResearch.WordTrace tailWord_4997511 prefixEnd_4997511 855375073043833982976457 := by
  unfold tailWord_4997511
  simp only [CollatzResearch.WordTrace]
  refine ⟨182274200597878628772752387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121516133731919085848501591 182274200597878628772752387)
  ·
    refine ⟨273411300896817943159128581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182274200597878628772752387 273411300896817943159128581)
    ·
      refine ⟨51264618918153364342336609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273411300896817943159128581 51264618918153364342336609)
      ·
        refine ⟨38448464188615023256752457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51264618918153364342336609 38448464188615023256752457)
        ·
          refine ⟨28836348141461267442564343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38448464188615023256752457 28836348141461267442564343)
          ·
            refine ⟨43254522212191901163846515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28836348141461267442564343 43254522212191901163846515)
            ·
              refine ⟨64881783318287851745769773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43254522212191901163846515 64881783318287851745769773)
              ·
                refine ⟨24330668744357944404663665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64881783318287851745769773 24330668744357944404663665)
                ·
                  refine ⟨18248001558268458303497749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24330668744357944404663665 18248001558268458303497749)
                  ·
                    refine ⟨855375073043833982976457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18248001558268458303497749 855375073043833982976457)
                    ·
                      rfl

theorem cell23_4997511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_4997511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997511 prefixEnd_4997511 := by exact prefixLift 4997511
  have htrace : WordTrace (prefixWord ++ tailWord_4997511) baseStart_4997511 baseEnd_4997511 := by
    simpa [prefixWord, tailWord_4997511, baseEnd_4997511] using wordTrace_append hprefix tailTrace_4997511
  have hstable : (prefixWord ++ tailWord_4997511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997511).length < 2 ^ (prefixWord ++ tailWord_4997511).sum := by decide
  have hdescent : baseEnd_4997511 < baseStart_4997511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997512 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_4997512 : Nat := 118140960795 + 4997512 * 2 ^ 59
def prefixEnd_4997512 : Nat := 4983230072969 + 3 ^ 40 * 4997512 * 2
def baseEnd_4997512 : Nat := 2566125732612156445016867

theorem tailTrace_4997512 : CollatzResearch.WordTrace tailWord_4997512 prefixEnd_4997512 2566125732612156445016867 := by
  unfold tailWord_4997512
  simp only [CollatzResearch.WordTrace]
  refine ⟨91137118535437502971769395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121516158047250003962359193 91137118535437502971769395)
  ·
    refine ⟨136705677803156254457654093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91137118535437502971769395 136705677803156254457654093)
    ·
      refine ⟨51264629176183595421620285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136705677803156254457654093 51264629176183595421620285)
      ·
        refine ⟨19224235941068848283107607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51264629176183595421620285 19224235941068848283107607)
        ·
          refine ⟨28836353911603272424661411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19224235941068848283107607 28836353911603272424661411)
          ·
            refine ⟨43254530867404908636992117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28836353911603272424661411 43254530867404908636992117)
            ·
              refine ⟨4055112268819210184718011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43254530867404908636992117 4055112268819210184718011)
              ·
                refine ⟨6082668403228815277077017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055112268819210184718011 6082668403228815277077017)
                ·
                  refine ⟨4562001302421611457807763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6082668403228815277077017 4562001302421611457807763)
                  ·
                    refine ⟨6843001953632417186711645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4562001302421611457807763 6843001953632417186711645)
                    ·
                      refine ⟨2566125732612156445016867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6843001953632417186711645 2566125732612156445016867)
                      ·
                        rfl

theorem cell23_4997512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_4997512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997512 prefixEnd_4997512 := by exact prefixLift 4997512
  have htrace : WordTrace (prefixWord ++ tailWord_4997512) baseStart_4997512 baseEnd_4997512 := by
    simpa [prefixWord, tailWord_4997512, baseEnd_4997512] using wordTrace_append hprefix tailTrace_4997512
  have hstable : (prefixWord ++ tailWord_4997512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997512).length < 2 ^ (prefixWord ++ tailWord_4997512).sum := by decide
  have hdescent : baseEnd_4997512 < baseStart_4997512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997535 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 6, 2, 2]
def baseStart_4997535 : Nat := 118140960795 + 4997535 * 2 ^ 59
def prefixEnd_4997535 : Nat := 4983230072969 + 3 ^ 40 * 4997535 * 2
def baseEnd_4997535 : Nat := 2566137542667209855029261

theorem tailTrace_4997535 : CollatzResearch.WordTrace tailWord_4997535 prefixEnd_4997535 2566137542667209855029261 := by
  unfold tailWord_4997535
  simp only [CollatzResearch.WordTrace]
  refine ⟨182275075949791680871626059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121516717299861120581084039 182275075949791680871626059)
  ·
    refine ⟨273412613924687521307439089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182275075949791680871626059 273412613924687521307439089)
    ·
      refine ⟨205059460443515640980579317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273412613924687521307439089 205059460443515640980579317)
      ·
        refine ⟨19224324416579591341929311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205059460443515640980579317 19224324416579591341929311)
        ·
          refine ⟨28836486624869387012893967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19224324416579591341929311 28836486624869387012893967)
          ·
            refine ⟨43254729937304080519340951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28836486624869387012893967 43254729937304080519340951)
            ·
              refine ⟨64882094905956120779011427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43254729937304080519340951 64882094905956120779011427)
              ·
                refine ⟨97323142358934181168517141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64882094905956120779011427 97323142358934181168517141)
                ·
                  refine ⟨4562022298075039742274241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97323142358934181168517141 4562022298075039742274241)
                  ·
                    refine ⟨3421516723556279806705681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4562022298075039742274241 3421516723556279806705681)
                    ·
                      refine ⟨2566137542667209855029261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3421516723556279806705681 2566137542667209855029261)
                      ·
                        rfl

theorem cell23_4997535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_4997535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997535 prefixEnd_4997535 := by exact prefixLift 4997535
  have htrace : WordTrace (prefixWord ++ tailWord_4997535) baseStart_4997535 baseEnd_4997535 := by
    simpa [prefixWord, tailWord_4997535, baseEnd_4997535] using wordTrace_append hprefix tailTrace_4997535
  have hstable : (prefixWord ++ tailWord_4997535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997535).length < 2 ^ (prefixWord ++ tailWord_4997535).sum := by decide
  have hdescent : baseEnd_4997535 < baseStart_4997535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997538 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4997538 : Nat := 118140960795 + 4997538 * 2 ^ 59
def prefixEnd_4997538 : Nat := 4983230072969 + 3 ^ 40 * 4997538 * 2
def baseEnd_4997538 : Nat := 2566139083109173343291747

theorem tailTrace_4997538 : CollatzResearch.WordTrace tailWord_4997538 prefixEnd_4997538 2566139083109173343291747 := by
  unfold tailWord_4997538
  simp only [CollatzResearch.WordTrace]
  refine ⟨45568796342195203095996317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121516790245853874922656845 45568796342195203095996317)
  ·
    refine ⟨17088298628323201160998619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45568796342195203095996317 17088298628323201160998619)
    ·
      refine ⟨25632447942484801741497929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17088298628323201160998619 25632447942484801741497929)
      ·
        refine ⟨19224335956863601306123447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25632447942484801741497929 19224335956863601306123447)
        ·
          refine ⟨28836503935295401959185171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19224335956863601306123447 28836503935295401959185171)
          ·
            refine ⟨43254755902943102938777757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28836503935295401959185171 43254755902943102938777757)
            ·
              refine ⟨16220533463603663602041659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43254755902943102938777757 16220533463603663602041659)
              ·
                refine ⟨24330800195405495403062489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16220533463603663602041659 24330800195405495403062489)
                ·
                  refine ⟨18248100146554121552296867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24330800195405495403062489 18248100146554121552296867)
                  ·
                    refine ⟨27372150219831182328445301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18248100146554121552296867 27372150219831182328445301)
                    ·
                      refine ⟨2566139083109173343291747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27372150219831182328445301 2566139083109173343291747)
                      ·
                        rfl

theorem cell23_4997538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4997538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997538 prefixEnd_4997538 := by exact prefixLift 4997538
  have htrace : WordTrace (prefixWord ++ tailWord_4997538) baseStart_4997538 baseEnd_4997538 := by
    simpa [prefixWord, tailWord_4997538, baseEnd_4997538] using wordTrace_append hprefix tailTrace_4997538
  have hstable : (prefixWord ++ tailWord_4997538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997538).length < 2 ^ (prefixWord ++ tailWord_4997538).sum := by decide
  have hdescent : baseEnd_4997538 < baseStart_4997538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997571 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 6, 5]
def baseStart_4997571 : Nat := 118140960795 + 4997571 * 2 ^ 59
def prefixEnd_4997571 : Nat := 4983230072969 + 3 ^ 40 * 4997571 * 2
def baseEnd_4997571 : Nat := 855385342656923904726365

theorem tailTrace_4997571 : CollatzResearch.WordTrace tailWord_4997571 prefixEnd_4997571 855385342656923904726365 := by
  unfold tailWord_4997571
  simp only [CollatzResearch.WordTrace]
  refine ⟨182276388977661259019936567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121517592651774172679957711 182276388977661259019936567)
  ·
    refine ⟨273414583466491888529904851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182276388977661259019936567 273414583466491888529904851)
    ·
      refine ⟨410121875199737832794857277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273414583466491888529904851 410121875199737832794857277)
      ·
        refine ⟨153795703199901687298071479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410121875199737832794857277 153795703199901687298071479)
        ·
          refine ⟨230693554799852530947107219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153795703199901687298071479 230693554799852530947107219)
          ·
            refine ⟨346040332199778796420660829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230693554799852530947107219 346040332199778796420660829)
            ·
              refine ⟨129765124574917048657747811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346040332199778796420660829 129765124574917048657747811)
              ·
                refine ⟨194647686862375572986621717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129765124574917048657747811 194647686862375572986621717)
                ·
                  refine ⟨9124110321673854983747893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 194647686862375572986621717 9124110321673854983747893)
                  ·
                    refine ⟨855385342656923904726365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9124110321673854983747893 855385342656923904726365)
                    ·
                      rfl

theorem cell23_4997571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 5].length) (baseStart_4997571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997571 prefixEnd_4997571 := by exact prefixLift 4997571
  have htrace : WordTrace (prefixWord ++ tailWord_4997571) baseStart_4997571 baseEnd_4997571 := by
    simpa [prefixWord, tailWord_4997571, baseEnd_4997571] using wordTrace_append hprefix tailTrace_4997571
  have hstable : (prefixWord ++ tailWord_4997571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997571).length < 2 ^ (prefixWord ++ tailWord_4997571).sum := by decide
  have hdescent : baseEnd_4997571 < baseStart_4997571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997611 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5]
def baseStart_4997611 : Nat := 118140960795 + 4997611 * 2 ^ 59
def prefixEnd_4997611 : Nat := 4983230072969 + 3 ^ 40 * 4997611 * 2
def baseEnd_4997611 : Nat := 2566176567196951557678911

theorem tailTrace_4997611 : CollatzResearch.WordTrace tailWord_4997611 prefixEnd_4997611 2566176567196951557678911 := by
  unfold tailWord_4997611
  simp only [CollatzResearch.WordTrace]
  refine ⟨182277847897516345851392687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121518565265010897234261791 182277847897516345851392687)
  ·
    refine ⟨273416771846274518777089031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182277847897516345851392687 273416771846274518777089031)
    ·
      refine ⟨410125157769411778165633547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273416771846274518777089031 410125157769411778165633547)
      ·
        refine ⟨615187736654117667248450321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410125157769411778165633547 615187736654117667248450321)
        ·
          refine ⟨461390802490588250436337741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615187736654117667248450321 461390802490588250436337741)
          ·
            refine ⟨173021550933970593913626653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461390802490588250436337741 173021550933970593913626653)
            ·
              refine ⟨64883081600238972717609995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173021550933970593913626653 64883081600238972717609995)
              ·
                refine ⟨97324622400358459076414993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64883081600238972717609995 97324622400358459076414993)
                ·
                  refine ⟨72993466800268844307311245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97324622400358459076414993 72993466800268844307311245)
                  ·
                    refine ⟨27372550050100816615241717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72993466800268844307311245 27372550050100816615241717)
                    ·
                      refine ⟨2566176567196951557678911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27372550050100816615241717 2566176567196951557678911)
                      ·
                        rfl

theorem cell23_4997611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_4997611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997611 prefixEnd_4997611 := by exact prefixLift 4997611
  have htrace : WordTrace (prefixWord ++ tailWord_4997611) baseStart_4997611 baseEnd_4997611 := by
    simpa [prefixWord, tailWord_4997611, baseEnd_4997611] using wordTrace_append hprefix tailTrace_4997611
  have hstable : (prefixWord ++ tailWord_4997611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997611).length < 2 ^ (prefixWord ++ tailWord_4997611).sum := by decide
  have hdescent : baseEnd_4997611 < baseStart_4997611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997628 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_4997628 : Nat := 118140960795 + 4997628 * 2 ^ 59
def prefixEnd_4997628 : Nat := 4983230072969 + 3 ^ 40 * 4997628 * 2
def baseEnd_4997628 : Nat := 2566185296368077991166333

theorem tailTrace_4997628 : CollatzResearch.WordTrace tailWord_4997628 prefixEnd_4997628 2566185296368077991166333 := by
  unfold tailWord_4997628
  simp only [CollatzResearch.WordTrace]
  refine ⟨91139233969227378877380769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121518978625636505169841025 91139233969227378877380769)
  ·
    refine ⟨68354425476920534158035577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91139233969227378877380769 68354425476920534158035577)
    ·
      refine ⟨51265819107690400618526683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68354425476920534158035577 51265819107690400618526683)
      ·
        refine ⟨76898728661535600927790025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51265819107690400618526683 76898728661535600927790025)
        ·
          refine ⟨57674046496151700695842519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76898728661535600927790025 57674046496151700695842519)
          ·
            refine ⟨86511069744227551043763779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57674046496151700695842519 86511069744227551043763779)
            ·
              refine ⟨129766604616341326565645669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86511069744227551043763779 129766604616341326565645669)
              ·
                refine ⟨24331238365563998731058563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129766604616341326565645669 24331238365563998731058563)
                ·
                  refine ⟨36496857548345998096587845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24331238365563998731058563 36496857548345998096587845)
                  ·
                    refine ⟨6843160790314874643110221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36496857548345998096587845 6843160790314874643110221)
                    ·
                      refine ⟨2566185296368077991166333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6843160790314874643110221 2566185296368077991166333)
                      ·
                        rfl

theorem cell23_4997628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_4997628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997628 prefixEnd_4997628 := by exact prefixLift 4997628
  have htrace : WordTrace (prefixWord ++ tailWord_4997628) baseStart_4997628 baseEnd_4997628 := by
    simpa [prefixWord, tailWord_4997628, baseEnd_4997628] using wordTrace_append hprefix tailTrace_4997628
  have hstable : (prefixWord ++ tailWord_4997628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997628).length < 2 ^ (prefixWord ++ tailWord_4997628).sum := by decide
  have hdescent : baseEnd_4997628 < baseStart_4997628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997685 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_4997685 : Nat := 118140960795 + 4997685 * 2 ^ 59
def prefixEnd_4997685 : Nat := 4983230072969 + 3 ^ 40 * 4997685 * 2
def baseEnd_4997685 : Nat := 2566214564765384268153571

theorem tailTrace_4997685 : CollatzResearch.WordTrace tailWord_4997685 prefixEnd_4997685 2566214564765384268153571 := by
  unfold tailWord_4997685
  simp only [CollatzResearch.WordTrace]
  refine ⟨182280546899248256489586509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121520364599498837659724339 182280546899248256489586509)
  ·
    refine ⟨68355205087218096183594941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182280546899248256489586509 68355205087218096183594941)
    ·
      refine ⟨25633201907706786068848103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68355205087218096183594941 25633201907706786068848103)
      ·
        refine ⟨38449802861560179103272155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25633201907706786068848103 38449802861560179103272155)
        ·
          refine ⟨57674704292340268654908233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38449802861560179103272155 57674704292340268654908233)
          ·
            refine ⟨43256028219255201491181175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57674704292340268654908233 43256028219255201491181175)
            ·
              refine ⟨64884042328882802236771763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43256028219255201491181175 64884042328882802236771763)
              ·
                refine ⟨97326063493324203355157645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64884042328882802236771763 97326063493324203355157645)
                ·
                  refine ⟨36497273809996576258184117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97326063493324203355157645 36497273809996576258184117)
                  ·
                    refine ⟨3421619419687179024204761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36497273809996576258184117 3421619419687179024204761)
                    ·
                      refine ⟨2566214564765384268153571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3421619419687179024204761 2566214564765384268153571)
                      ·
                        rfl

theorem cell23_4997685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_4997685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997685 prefixEnd_4997685 := by exact prefixLift 4997685
  have htrace : WordTrace (prefixWord ++ tailWord_4997685) baseStart_4997685 baseEnd_4997685 := by
    simpa [prefixWord, tailWord_4997685, baseEnd_4997685] using wordTrace_append hprefix tailTrace_4997685
  have hstable : (prefixWord ++ tailWord_4997685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997685).length < 2 ^ (prefixWord ++ tailWord_4997685).sum := by decide
  have hdescent : baseEnd_4997685 < baseStart_4997685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997692 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_4997692 : Nat := 118140960795 + 4997692 * 2 ^ 59
def prefixEnd_4997692 : Nat := 4983230072969 + 3 ^ 40 * 4997692 * 2
def baseEnd_4997692 : Nat := 2566218159129965740766039

theorem tailTrace_4997692 : CollatzResearch.WordTrace tailWord_4997692 prefixEnd_4997692 2566218159129965740766039 := by
  unfold tailWord_4997692
  simp only [CollatzResearch.WordTrace]
  refine ⟨91140401105111448342545665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121520534806815264456727553 91140401105111448342545665)
  ·
    refine ⟨68355300828833586256909249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91140401105111448342545665 68355300828833586256909249)
    ·
      refine ⟨51266475621625189692681937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68355300828833586256909249 51266475621625189692681937)
      ·
        refine ⟨38449856716218892269511453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51266475621625189692681937 38449856716218892269511453)
        ·
          refine ⟨14418696268582084601066795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38449856716218892269511453 14418696268582084601066795)
          ·
            refine ⟨21628044402873126901600193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14418696268582084601066795 21628044402873126901600193)
            ·
              refine ⟨16221033302154845176200145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21628044402873126901600193 16221033302154845176200145)
              ·
                refine ⟨12165774976616133882150109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16221033302154845176200145 12165774976616133882150109)
                ·
                  refine ⟨4562165616231050205806291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12165774976616133882150109 4562165616231050205806291)
                  ·
                    refine ⟨6843248424346575308709437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4562165616231050205806291 6843248424346575308709437)
                    ·
                      refine ⟨2566218159129965740766039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6843248424346575308709437 2566218159129965740766039)
                      ·
                        rfl

theorem cell23_4997692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_4997692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997692 prefixEnd_4997692 := by exact prefixLift 4997692
  have htrace : WordTrace (prefixWord ++ tailWord_4997692) baseStart_4997692 baseEnd_4997692 := by
    simpa [prefixWord, tailWord_4997692, baseEnd_4997692] using wordTrace_append hprefix tailTrace_4997692
  have hstable : (prefixWord ++ tailWord_4997692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997692).length < 2 ^ (prefixWord ++ tailWord_4997692).sum := by decide
  have hdescent : baseEnd_4997692 < baseStart_4997692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997695 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 1, 5]
def baseStart_4997695 : Nat := 118140960795 + 4997695 * 2 ^ 59
def prefixEnd_4997695 : Nat := 4983230072969 + 3 ^ 40 * 4997695 * 2
def baseEnd_4997695 : Nat := 855406566523976409676175

theorem tailTrace_4997695 : CollatzResearch.WordTrace tailWord_4997695 prefixEnd_4997695 855406566523976409676175 := by
  unfold tailWord_4997695
  simp only [CollatzResearch.WordTrace]
  refine ⟨182280911629212028197450539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121520607752808018798300359 182280911629212028197450539)
  ·
    refine ⟨273421367443818042296175809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182280911629212028197450539 273421367443818042296175809)
    ·
      refine ⟨205066025582863531722131857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273421367443818042296175809 205066025582863531722131857)
      ·
        refine ⟨153799519187147648791598893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205066025582863531722131857 153799519187147648791598893)
        ·
          refine ⟨57674819695180368296849585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153799519187147648791598893 57674819695180368296849585)
          ·
            refine ⟨43256114771385276222637189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57674819695180368296849585 43256114771385276222637189)
            ·
              refine ⟨8110521519634739291744473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43256114771385276222637189 8110521519634739291744473)
              ·
                refine ⟨6082891139726054468808355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8110521519634739291744473 6082891139726054468808355)
                ·
                  refine ⟨9124336709589081703212533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6082891139726054468808355 9124336709589081703212533)
                  ·
                    refine ⟨855406566523976409676175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9124336709589081703212533 855406566523976409676175)
                    ·
                      rfl

theorem cell23_4997695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_4997695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997695 prefixEnd_4997695 := by exact prefixLift 4997695
  have htrace : WordTrace (prefixWord ++ tailWord_4997695) baseStart_4997695 baseEnd_4997695 := by
    simpa [prefixWord, tailWord_4997695, baseEnd_4997695] using wordTrace_append hprefix tailTrace_4997695
  have hstable : (prefixWord ++ tailWord_4997695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997695).length < 2 ^ (prefixWord ++ tailWord_4997695).sum := by decide
  have hdescent : baseEnd_4997695 < baseStart_4997695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997708 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 3, 6]
def baseStart_4997708 : Nat := 118140960795 + 4997708 * 2 ^ 59
def prefixEnd_4997708 : Nat := 4983230072969 + 3 ^ 40 * 4997708 * 2
def baseEnd_4997708 : Nat := 855408791606812559388655

theorem tailTrace_4997708 : CollatzResearch.WordTrace tailWord_4997708 prefixEnd_4997708 855408791606812559388655 := by
  unfold tailWord_4997708
  simp only [CollatzResearch.WordTrace]
  refine ⟨91140692889082465708836889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121520923852109954278449185 91140692889082465708836889)
  ·
    refine ⟨68355519666811849281627667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91140692889082465708836889 68355519666811849281627667)
    ·
      refine ⟨102533279500217773922441501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68355519666811849281627667 102533279500217773922441501)
      ·
        refine ⟨38449979812581665220915563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102533279500217773922441501 38449979812581665220915563)
        ·
          refine ⟨57674969718872497831373345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38449979812581665220915563 57674969718872497831373345)
          ·
            refine ⟨43256227289154373373530009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57674969718872497831373345 43256227289154373373530009)
            ·
              refine ⟨32442170466865780030147507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43256227289154373373530009 32442170466865780030147507)
              ·
                refine ⟨48663255700298670045221261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32442170466865780030147507 48663255700298670045221261)
                ·
                  refine ⟨18248720887612001266957973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48663255700298670045221261 18248720887612001266957973)
                  ·
                    refine ⟨855408791606812559388655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18248720887612001266957973 855408791606812559388655)
                    ·
                      rfl

theorem cell23_4997708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_4997708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997708 prefixEnd_4997708 := by exact prefixLift 4997708
  have htrace : WordTrace (prefixWord ++ tailWord_4997708) baseStart_4997708 baseEnd_4997708 := by
    simpa [prefixWord, tailWord_4997708, baseEnd_4997708] using wordTrace_append hprefix tailTrace_4997708
  have hstable : (prefixWord ++ tailWord_4997708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997708).length < 2 ^ (prefixWord ++ tailWord_4997708).sum := by decide
  have hdescent : baseEnd_4997708 < baseStart_4997708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997728 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_4997728 : Nat := 118140960795 + 4997728 * 2 ^ 59
def prefixEnd_4997728 : Nat := 4983230072969 + 3 ^ 40 * 4997728 * 2
def baseEnd_4997728 : Nat := 2566236644433527599915873

theorem tailTrace_4997728 : CollatzResearch.WordTrace tailWord_4997728 prefixEnd_4997728 2566236644433527599915873 := by
  unfold tailWord_4997728
  simp only [CollatzResearch.WordTrace]
  refine ⟨91141057619046237416700919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121521410158728316555601225 91141057619046237416700919)
  ·
    refine ⟨136711586428569356125051379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91141057619046237416700919 136711586428569356125051379)
    ·
      refine ⟨205067379642854034187577069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136711586428569356125051379 205067379642854034187577069)
      ·
        refine ⟨76900267366070262820341401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205067379642854034187577069 76900267366070262820341401)
        ·
          refine ⟨57675200524552697115256051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76900267366070262820341401 57675200524552697115256051)
          ·
            refine ⟨86512800786829045672884077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57675200524552697115256051 86512800786829045672884077)
            ·
              refine ⟨32442300295060892127331529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86512800786829045672884077 32442300295060892127331529)
              ·
                refine ⟨24331725221295669095498647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32442300295060892127331529 24331725221295669095498647)
                ·
                  refine ⟨36497587831943503643247971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24331725221295669095498647 36497587831943503643247971)
                  ·
                    refine ⟨54746381747915255464871957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36497587831943503643247971 54746381747915255464871957)
                    ·
                      refine ⟨2566236644433527599915873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54746381747915255464871957 2566236644433527599915873)
                      ·
                        rfl

theorem cell23_4997728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_4997728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997728 prefixEnd_4997728 := by exact prefixLift 4997728
  have htrace : WordTrace (prefixWord ++ tailWord_4997728) baseStart_4997728 baseEnd_4997728 := by
    simpa [prefixWord, tailWord_4997728, baseEnd_4997728] using wordTrace_append hprefix tailTrace_4997728
  have hstable : (prefixWord ++ tailWord_4997728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997728).length < 2 ^ (prefixWord ++ tailWord_4997728).sum := by decide
  have hdescent : baseEnd_4997728 < baseStart_4997728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997735 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_4997735 : Nat := 118140960795 + 4997735 * 2 ^ 59
def prefixEnd_4997735 : Nat := 4983230072969 + 3 ^ 40 * 4997735 * 2
def baseEnd_4997735 : Nat := 2566240238798109072528341

theorem tailTrace_4997735 : CollatzResearch.WordTrace tailWord_4997735 prefixEnd_4997735 2566240238798109072528341 := by
  unfold tailWord_4997735
  simp only [CollatzResearch.WordTrace]
  refine ⟨182282370549067115028906659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121521580366044743352604439 182282370549067115028906659)
  ·
    refine ⟨273423555823600672543359989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182282370549067115028906659 273423555823600672543359989)
    ·
      refine ⟨25633458358462563050939999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 273423555823600672543359989 25633458358462563050939999)
      ·
        refine ⟨38450187537693844576409999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25633458358462563050939999 38450187537693844576409999)
        ·
          refine ⟨57675281306540766864614999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38450187537693844576409999 57675281306540766864614999)
          ·
            refine ⟨86512921959811150296922499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57675281306540766864614999 86512921959811150296922499)
            ·
              refine ⟨129769382939716725445383749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86512921959811150296922499 129769382939716725445383749)
              ·
                refine ⟨24331759301196886021009453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129769382939716725445383749 24331759301196886021009453)
                ·
                  refine ⟨9124409737948832257878545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24331759301196886021009453 9124409737948832257878545)
                  ·
                    refine ⟨6843307303461624193408909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9124409737948832257878545 6843307303461624193408909)
                    ·
                      refine ⟨2566240238798109072528341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6843307303461624193408909 2566240238798109072528341)
                      ·
                        rfl

theorem cell23_4997735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_4997735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997735 prefixEnd_4997735 := by exact prefixLift 4997735
  have htrace : WordTrace (prefixWord ++ tailWord_4997735) baseStart_4997735 baseEnd_4997735 := by
    simpa [prefixWord, tailWord_4997735, baseEnd_4997735] using wordTrace_append hprefix tailTrace_4997735
  have hstable : (prefixWord ++ tailWord_4997735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997735).length < 2 ^ (prefixWord ++ tailWord_4997735).sum := by decide
  have hdescent : baseEnd_4997735 < baseStart_4997735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997765 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_4997765 : Nat := 118140960795 + 4997765 * 2 ^ 59
def prefixEnd_4997765 : Nat := 4983230072969 + 3 ^ 40 * 4997765 * 2
def baseEnd_4997765 : Nat := 2566255643217743955153203

theorem tailTrace_4997765 : CollatzResearch.WordTrace tailWord_4997765 prefixEnd_4997765 2566255643217743955153203 := by
  unfold tailWord_4997765
  simp only [CollatzResearch.WordTrace]
  refine ⟨182283464738958430152498749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121522309825972286768332499 182283464738958430152498749)
  ·
    refine ⟨68356299277109411307187031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182283464738958430152498749 68356299277109411307187031)
    ·
      refine ⟨102534448915664116960780547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68356299277109411307187031 102534448915664116960780547)
      ·
        refine ⟨153801673373496175441170821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102534448915664116960780547 153801673373496175441170821)
        ·
          refine ⟨28837813757530532895219529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153801673373496175441170821 28837813757530532895219529)
          ·
            refine ⟨21628360318147899671414647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28837813757530532895219529 21628360318147899671414647)
            ·
              refine ⟨32442540477221849507121971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21628360318147899671414647 32442540477221849507121971)
              ·
                refine ⟨48663810715832774260682957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32442540477221849507121971 48663810715832774260682957)
                ·
                  refine ⟨18248929018437290347756109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48663810715832774260682957 18248929018437290347756109)
                  ·
                    refine ⟨6843348381913983880408541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18248929018437290347756109 6843348381913983880408541)
                    ·
                      refine ⟨2566255643217743955153203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6843348381913983880408541 2566255643217743955153203)
                      ·
                        rfl

theorem cell23_4997765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_4997765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997765 prefixEnd_4997765 := by exact prefixLift 4997765
  have htrace : WordTrace (prefixWord ++ tailWord_4997765) baseStart_4997765 baseEnd_4997765 := by
    simpa [prefixWord, tailWord_4997765, baseEnd_4997765] using wordTrace_append hprefix tailTrace_4997765
  have hstable : (prefixWord ++ tailWord_4997765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997765).length < 2 ^ (prefixWord ++ tailWord_4997765).sum := by decide
  have hdescent : baseEnd_4997765 < baseStart_4997765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997875 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 2, 5]
def baseStart_4997875 : Nat := 118140960795 + 4997875 * 2 ^ 59
def prefixEnd_4997875 : Nat := 4983230072969 + 3 ^ 40 * 4997875 * 2
def baseEnd_4997875 : Nat := 855437375363246174925899

theorem tailTrace_4997875 : CollatzResearch.WordTrace tailWord_4997875 prefixEnd_4997875 855437375363246174925899 := by
  unfold tailWord_4997875
  simp only [CollatzResearch.WordTrace]
  refine ⟨182287476768559918939003079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121524984512373279292668719 182287476768559918939003079)
  ·
    refine ⟨273431215152839878408504619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182287476768559918939003079 273431215152839878408504619)
    ·
      refine ⟨410146822729259817612756929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273431215152839878408504619 410146822729259817612756929)
      ·
        refine ⟨307610117046944863209567697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410146822729259817612756929 307610117046944863209567697)
        ·
          refine ⟨230707587785208647407175773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307610117046944863209567697 230707587785208647407175773)
          ·
            refine ⟨86515345419453242777690915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230707587785208647407175773 86515345419453242777690915)
            ·
              refine ⟨129773018129179864166536373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86515345419453242777690915 129773018129179864166536373)
              ·
                refine ⟨12166220449610612265612785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129773018129179864166536373 12166220449610612265612785)
                ·
                  refine ⟨9124665337207959199209589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12166220449610612265612785 9124665337207959199209589)
                  ·
                    refine ⟨855437375363246174925899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9124665337207959199209589 855437375363246174925899)
                    ·
                      rfl

theorem cell23_4997875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 5].length) (baseStart_4997875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997875 prefixEnd_4997875 := by exact prefixLift 4997875
  have htrace : WordTrace (prefixWord ++ tailWord_4997875) baseStart_4997875 baseEnd_4997875 := by
    simpa [prefixWord, tailWord_4997875, baseEnd_4997875] using wordTrace_append hprefix tailTrace_4997875
  have hstable : (prefixWord ++ tailWord_4997875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997875).length < 2 ^ (prefixWord ++ tailWord_4997875).sum := by decide
  have hdescent : baseEnd_4997875 < baseStart_4997875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997876 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4997876 : Nat := 118140960795 + 4997876 * 2 ^ 59
def prefixEnd_4997876 : Nat := 4983230072969 + 3 ^ 40 * 4997876 * 2
def baseEnd_4997876 : Nat := 2566312639570393020865193

theorem tailTrace_4997876 : CollatzResearch.WordTrace tailWord_4997876 prefixEnd_4997876 2566312639570393020865193 := by
  unfold tailWord_4997876
  simp only [CollatzResearch.WordTrace]
  refine ⟨91143756620778148054894741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121525008827704197406526321 91143756620778148054894741)
  ·
    refine ⟨4272363591598975690073191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91143756620778148054894741 4272363591598975690073191)
    ·
      refine ⟨6408545387398463535109787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272363591598975690073191 6408545387398463535109787)
      ·
        refine ⟨9612818081097695302664681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408545387398463535109787 9612818081097695302664681)
        ·
          refine ⟨7209613560823271476998511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9612818081097695302664681 7209613560823271476998511)
          ·
            refine ⟨10814420341234907215497767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7209613560823271476998511 10814420341234907215497767)
            ·
              refine ⟨16221630511852360823246651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10814420341234907215497767 16221630511852360823246651)
              ·
                refine ⟨24332445767778541234869977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16221630511852360823246651 24332445767778541234869977)
                ·
                  refine ⟨18249334325833905926152483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24332445767778541234869977 18249334325833905926152483)
                  ·
                    refine ⟨27374001488750858889228725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18249334325833905926152483 27374001488750858889228725)
                    ·
                      refine ⟨2566312639570393020865193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27374001488750858889228725 2566312639570393020865193)
                      ·
                        rfl

theorem cell23_4997876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4997876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997876 prefixEnd_4997876 := by exact prefixLift 4997876
  have htrace : WordTrace (prefixWord ++ tailWord_4997876) baseStart_4997876 baseEnd_4997876 := by
    simpa [prefixWord, tailWord_4997876, baseEnd_4997876] using wordTrace_append hprefix tailTrace_4997876
  have hstable : (prefixWord ++ tailWord_4997876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997876).length < 2 ^ (prefixWord ++ tailWord_4997876).sum := by decide
  have hdescent : baseEnd_4997876 < baseStart_4997876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997885 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_4997885 : Nat := 118140960795 + 4997885 * 2 ^ 59
def prefixEnd_4997885 : Nat := 4983230072969 + 3 ^ 40 * 4997885 * 2
def baseEnd_4997885 : Nat := 2566317260896283485652651

theorem tailTrace_4997885 : CollatzResearch.WordTrace tailWord_4997885 prefixEnd_4997885 2566317260896283485652651 := by
  unfold tailWord_4997885
  simp only [CollatzResearch.WordTrace]
  refine ⟨182287841498523690646867109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121525227665682460431244739 182287841498523690646867109)
  ·
    refine ⟨34178970280973191996287583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182287841498523690646867109 34178970280973191996287583)
    ·
      refine ⟨51268455421459787994431375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34178970280973191996287583 51268455421459787994431375)
      ·
        refine ⟨76902683132189681991647063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51268455421459787994431375 76902683132189681991647063)
        ·
          refine ⟨115354024698284522987470595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76902683132189681991647063 115354024698284522987470595)
          ·
            refine ⟨173031037047426784481205893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115354024698284522987470595 173031037047426784481205893)
            ·
              refine ⟨32443319446392522090226105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173031037047426784481205893 32443319446392522090226105)
              ·
                refine ⟨24332489584794391567669579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32443319446392522090226105 24332489584794391567669579)
                ·
                  refine ⟨36498734377191587351504369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24332489584794391567669579 36498734377191587351504369)
                  ·
                    refine ⟨27374050782893690513628277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36498734377191587351504369 27374050782893690513628277)
                    ·
                      refine ⟨2566317260896283485652651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27374050782893690513628277 2566317260896283485652651)
                      ·
                        rfl

theorem cell23_4997885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_4997885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997885 prefixEnd_4997885 := by exact prefixLift 4997885
  have htrace : WordTrace (prefixWord ++ tailWord_4997885) baseStart_4997885 baseEnd_4997885 := by
    simpa [prefixWord, tailWord_4997885, baseEnd_4997885] using wordTrace_append hprefix tailTrace_4997885
  have hstable : (prefixWord ++ tailWord_4997885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997885).length < 2 ^ (prefixWord ++ tailWord_4997885).sum := by decide
  have hdescent : baseEnd_4997885 < baseStart_4997885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997892 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_4997892 : Nat := 118140960795 + 4997892 * 2 ^ 59
def prefixEnd_4997892 : Nat := 4983230072969 + 3 ^ 40 * 4997892 * 2
def baseEnd_4997892 : Nat := 855440285086954986088373

theorem tailTrace_4997892 : CollatzResearch.WordTrace tailWord_4997892 prefixEnd_4997892 855440285086954986088373 := by
  unfold tailWord_4997892
  simp only [CollatzResearch.WordTrace]
  refine ⟨91144048404749165421185965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121525397872998887228247953 91144048404749165421185965)
  ·
    refine ⟨34179018151780937032944737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91144048404749165421185965 34179018151780937032944737)
    ·
      refine ⟨25634263613835702774708553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34179018151780937032944737 25634263613835702774708553)
      ·
        refine ⟨19225697710376777081031415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25634263613835702774708553 19225697710376777081031415)
        ·
          refine ⟨28838546565565165621547123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19225697710376777081031415 28838546565565165621547123)
          ·
            refine ⟨43257819848347748432320685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28838546565565165621547123 43257819848347748432320685)
            ·
              refine ⟨16221682443130405662120257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43257819848347748432320685 16221682443130405662120257)
              ·
                refine ⟨12166261832347804246590193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16221682443130405662120257 12166261832347804246590193)
                ·
                  refine ⟨9124696374260853184942645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12166261832347804246590193 9124696374260853184942645)
                  ·
                    refine ⟨855440285086954986088373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9124696374260853184942645 855440285086954986088373)
                    ·
                      rfl

theorem cell23_4997892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_4997892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997892 prefixEnd_4997892 := by exact prefixLift 4997892
  have htrace : WordTrace (prefixWord ++ tailWord_4997892) baseStart_4997892 baseEnd_4997892 := by
    simpa [prefixWord, tailWord_4997892, baseEnd_4997892] using wordTrace_append hprefix tailTrace_4997892
  have hstable : (prefixWord ++ tailWord_4997892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997892).length < 2 ^ (prefixWord ++ tailWord_4997892).sum := by decide
  have hdescent : baseEnd_4997892 < baseStart_4997892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997912 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 1, 6, 2]
def baseStart_4997912 : Nat := 118140960795 + 4997912 * 2 ^ 59
def prefixEnd_4997912 : Nat := 4983230072969 + 3 ^ 40 * 4997912 * 2
def baseEnd_4997912 : Nat := 2566331124873954880015027

theorem tailTrace_4997912 : CollatzResearch.WordTrace tailWord_4997912 prefixEnd_4997912 2566331124873954880015027 := by
  unfold tailWord_4997912
  simp only [CollatzResearch.WordTrace]
  refine ⟨91144413134712937129049995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121525884179617249505399993 91144413134712937129049995)
  ·
    refine ⟨136716619702069405693574993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91144413134712937129049995 136716619702069405693574993)
    ·
      refine ⟨102537464776552054270181245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136716619702069405693574993 102537464776552054270181245)
      ·
        refine ⟨38451549291207020351317967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102537464776552054270181245 38451549291207020351317967)
        ·
          refine ⟨57677323936810530526976951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38451549291207020351317967 57677323936810530526976951)
          ·
            refine ⟨86515985905215795790465427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57677323936810530526976951 86515985905215795790465427)
            ·
              refine ⟨129773978857823693685698141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86515985905215795790465427 129773978857823693685698141)
              ·
                refine ⟨48665242071683885132136803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129773978857823693685698141 48665242071683885132136803)
                ·
                  refine ⟨72997863107525827698205205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48665242071683885132136803 72997863107525827698205205)
                  ·
                    refine ⟨3421774833165273173353369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72997863107525827698205205 3421774833165273173353369)
                    ·
                      refine ⟨2566331124873954880015027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3421774833165273173353369 2566331124873954880015027)
                      ·
                        rfl

theorem cell23_4997912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_4997912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997912 prefixEnd_4997912 := by exact prefixLift 4997912
  have htrace : WordTrace (prefixWord ++ tailWord_4997912) baseStart_4997912 baseEnd_4997912 := by
    simpa [prefixWord, tailWord_4997912, baseEnd_4997912] using wordTrace_append hprefix tailTrace_4997912
  have hstable : (prefixWord ++ tailWord_4997912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997912).length < 2 ^ (prefixWord ++ tailWord_4997912).sum := by decide
  have hdescent : baseEnd_4997912 < baseStart_4997912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4997955 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6]
def baseStart_4997955 : Nat := 118140960795 + 4997955 * 2 ^ 59
def prefixEnd_4997955 : Nat := 4983230072969 + 3 ^ 40 * 4997955 * 2
def baseEnd_4997955 : Nat := 2566353204542098211777329

theorem tailTrace_4997955 : CollatzResearch.WordTrace tailWord_4997955 prefixEnd_4997955 2566353204542098211777329 := by
  unfold tailWord_4997955
  simp only [CollatzResearch.WordTrace]
  refine ⟨182290394608270092601915319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121526929738846728401276879 182290394608270092601915319)
  ·
    refine ⟨273435591912405138902872979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182290394608270092601915319 273435591912405138902872979)
    ·
      refine ⟨410153387868607708354309469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273435591912405138902872979 410153387868607708354309469)
      ·
        refine ⟨153807520450727890632866051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410153387868607708354309469 153807520450727890632866051)
        ·
          refine ⟨230711280676091835949299077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153807520450727890632866051 230711280676091835949299077)
          ·
            refine ⟨43258365126767219240493577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230711280676091835949299077 43258365126767219240493577)
            ·
              refine ⟨32443773845075414430370183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43258365126767219240493577 32443773845075414430370183)
              ·
                refine ⟨48665660767613121645555275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32443773845075414430370183 48665660767613121645555275)
                ·
                  refine ⟨72998491151419682468332913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48665660767613121645555275 72998491151419682468332913)
                  ·
                    refine ⟨54748868363564761851249685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72998491151419682468332913 54748868363564761851249685)
                    ·
                      refine ⟨2566353204542098211777329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54748868363564761851249685 2566353204542098211777329)
                      ·
                        rfl

theorem cell23_4997955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_4997955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4997955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4997955 prefixEnd_4997955 := by exact prefixLift 4997955
  have htrace : WordTrace (prefixWord ++ tailWord_4997955) baseStart_4997955 baseEnd_4997955 := by
    simpa [prefixWord, tailWord_4997955, baseEnd_4997955] using wordTrace_append hprefix tailTrace_4997955
  have hstable : (prefixWord ++ tailWord_4997955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4997955).length < 2 ^ (prefixWord ++ tailWord_4997955).sum := by decide
  have hdescent : baseEnd_4997955 < baseStart_4997955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4997955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998036 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_4998036 : Nat := 118140960795 + 4998036 * 2 ^ 59
def prefixEnd_4998036 : Nat := 4983230072969 + 3 ^ 40 * 4998036 * 2
def baseEnd_4998036 : Nat := 2566394796475112394864457

theorem tailTrace_4998036 : CollatzResearch.WordTrace tailWord_4998036 prefixEnd_4998036 2566394796475112394864457 := by
  unfold tailWord_4998036
  simp only [CollatzResearch.WordTrace]
  refine ⟨91146674460488321717806981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121528899280651095623742641 91146674460488321717806981)
  ·
    refine ⟨17090001461341560322088809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91146674460488321717806981 17090001461341560322088809)
    ·
      refine ⟨12817501096006170241566607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17090001461341560322088809 12817501096006170241566607)
      ·
        refine ⟨19226251644009255362349911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12817501096006170241566607 19226251644009255362349911)
        ·
          refine ⟨28839377466013883043524867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19226251644009255362349911 28839377466013883043524867)
          ·
            refine ⟨43259066199020824565287301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28839377466013883043524867 43259066199020824565287301)
            ·
              refine ⟨8111074912316404605991369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43259066199020824565287301 8111074912316404605991369)
              ·
                refine ⟨6083306184237303454493527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8111074912316404605991369 6083306184237303454493527)
                ·
                  refine ⟨9124959276355955181740291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083306184237303454493527 9124959276355955181740291)
                  ·
                    refine ⟨13687438914533932772610437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9124959276355955181740291 13687438914533932772610437)
                    ·
                      refine ⟨2566394796475112394864457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13687438914533932772610437 2566394796475112394864457)
                      ·
                        rfl

theorem cell23_4998036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_4998036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998036 prefixEnd_4998036 := by exact prefixLift 4998036
  have htrace : WordTrace (prefixWord ++ tailWord_4998036) baseStart_4998036 baseEnd_4998036 := by
    simpa [prefixWord, tailWord_4998036, baseEnd_4998036] using wordTrace_append hprefix tailTrace_4998036
  have hstable : (prefixWord ++ tailWord_4998036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998036).length < 2 ^ (prefixWord ++ tailWord_4998036).sum := by decide
  have hdescent : baseEnd_4998036 < baseStart_4998036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998129 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 3]
def baseStart_4998129 : Nat := 118140960795 + 4998129 * 2 ^ 59
def prefixEnd_4998129 : Nat := 4983230072969 + 3 ^ 40 * 4998129 * 2
def baseEnd_4998129 : Nat := 2566442550175980531001529

theorem tailTrace_4998129 : CollatzResearch.WordTrace tailWord_4998129 prefixEnd_4998129 2566442550175980531001529 := by
  unfold tailWord_4998129
  simp only [CollatzResearch.WordTrace]
  refine ⟨182296740909639720318749441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121531160606426480212499627 182296740909639720318749441)
  ·
    refine ⟨136722555682229790239062081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182296740909639720318749441 136722555682229790239062081)
    ·
      refine ⟨102541916761672342679296561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136722555682229790239062081 102541916761672342679296561)
      ·
        refine ⟨76906437571254257009472421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102541916761672342679296561 76906437571254257009472421)
        ·
          refine ⟨14419957044610173189276079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76906437571254257009472421 14419957044610173189276079)
          ·
            refine ⟨21629935566915259783914119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14419957044610173189276079 21629935566915259783914119)
            ·
              refine ⟨32444903350372889675871179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21629935566915259783914119 32444903350372889675871179)
              ·
                refine ⟨48667355025559334513806769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32444903350372889675871179 48667355025559334513806769)
                ·
                  refine ⟨36500516269169500885355077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48667355025559334513806769 36500516269169500885355077)
                  ·
                    refine ⟨6843846800469281416004077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36500516269169500885355077 6843846800469281416004077)
                    ·
                      refine ⟨2566442550175980531001529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6843846800469281416004077 2566442550175980531001529)
                      ·
                        rfl

theorem cell23_4998129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_4998129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998129 prefixEnd_4998129 := by exact prefixLift 4998129
  have htrace : WordTrace (prefixWord ++ tailWord_4998129) baseStart_4998129 baseEnd_4998129 := by
    simpa [prefixWord, tailWord_4998129, baseEnd_4998129] using wordTrace_append hprefix tailTrace_4998129
  have hstable : (prefixWord ++ tailWord_4998129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998129).length < 2 ^ (prefixWord ++ tailWord_4998129).sum := by decide
  have hdescent : baseEnd_4998129 < baseStart_4998129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998183 : List Nat := [1, 1, 7, 1, 1, 1, 2, 4, 5]
def baseStart_4998183 : Nat := 118140960795 + 4998183 * 2 ^ 59
def prefixEnd_4998183 : Nat := 4983230072969 + 3 ^ 40 * 4998183 * 2
def baseEnd_4998183 : Nat := 285163364236813702191809

theorem tailTrace_4998183 : CollatzResearch.WordTrace tailWord_4998183 prefixEnd_4998183 285163364236813702191809 := by
  unfold tailWord_4998183
  simp only [CollatzResearch.WordTrace]
  refine ⟨182298710451444087541215203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121532473634296058360810135 182298710451444087541215203)
  ·
    refine ⟨273448065677166131311822805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182298710451444087541215203 273448065677166131311822805)
    ·
      refine ⟨6408939039308581202620847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 273448065677166131311822805 6408939039308581202620847)
      ·
        refine ⟨9613408558962871803931271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408939039308581202620847 9613408558962871803931271)
        ·
          refine ⟨14420112838444307705896907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9613408558962871803931271 14420112838444307705896907)
          ·
            refine ⟨21630169257666461558845361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14420112838444307705896907 21630169257666461558845361)
            ·
              refine ⟨16222626943249846169134021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21630169257666461558845361 16222626943249846169134021)
              ·
                refine ⟨3041742551859346156712629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16222626943249846169134021 3041742551859346156712629)
                ·
                  refine ⟨285163364236813702191809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3041742551859346156712629 285163364236813702191809)
                  ·
                    rfl

theorem cell23_4998183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 5].length) (baseStart_4998183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998183 prefixEnd_4998183 := by exact prefixLift 4998183
  have htrace : WordTrace (prefixWord ++ tailWord_4998183) baseStart_4998183 baseEnd_4998183 := by
    simpa [prefixWord, tailWord_4998183, baseEnd_4998183] using wordTrace_append hprefix tailTrace_4998183
  have hstable : (prefixWord ++ tailWord_4998183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998183).length < 2 ^ (prefixWord ++ tailWord_4998183).sum := by decide
  have hdescent : baseEnd_4998183 < baseStart_4998183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998196 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_4998196 : Nat := 118140960795 + 4998196 * 2 ^ 59
def prefixEnd_4998196 : Nat := 4983230072969 + 3 ^ 40 * 4998196 * 2
def baseEnd_4998196 : Nat := 855492317793277256287907

theorem tailTrace_4998196 : CollatzResearch.WordTrace tailWord_4998196 prefixEnd_4998196 855492317793277256287907 := by
  unfold tailWord_4998196
  simp only [CollatzResearch.WordTrace]
  refine ⟨91149592300198495380719221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121532789733597993840958961 91149592300198495380719221)
  ·
    refine ⟨8545274278143608941942427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91149592300198495380719221 8545274278143608941942427)
    ·
      refine ⟨12817911417215413412913641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8545274278143608941942427 12817911417215413412913641)
      ·
        refine ⟨9613433562911560059685231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12817911417215413412913641 9613433562911560059685231)
        ·
          refine ⟨14420150344367340089527847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9613433562911560059685231 14420150344367340089527847)
          ·
            refine ⟨21630225516551010134291771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14420150344367340089527847 21630225516551010134291771)
            ·
              refine ⟨32445338274826515201437657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21630225516551010134291771 32445338274826515201437657)
              ·
                refine ⟨24334003706119886401078243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32445338274826515201437657 24334003706119886401078243)
                ·
                  refine ⟨36501005559179829601617365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24334003706119886401078243 36501005559179829601617365)
                  ·
                    refine ⟨855492317793277256287907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36501005559179829601617365 855492317793277256287907)
                    ·
                      rfl

theorem cell23_4998196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_4998196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998196 prefixEnd_4998196 := by exact prefixLift 4998196
  have htrace : WordTrace (prefixWord ++ tailWord_4998196) baseStart_4998196 baseEnd_4998196 := by
    simpa [prefixWord, tailWord_4998196, baseEnd_4998196] using wordTrace_append hprefix tailTrace_4998196
  have hstable : (prefixWord ++ tailWord_4998196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998196).length < 2 ^ (prefixWord ++ tailWord_4998196).sum := by decide
  have hdescent : baseEnd_4998196 < baseStart_4998196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998230 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4998230 : Nat := 118140960795 + 4998230 * 2 ^ 59
def prefixEnd_4998230 : Nat := 4983230072969 + 3 ^ 40 * 4998230 * 2
def baseEnd_4998230 : Nat := 855498137240694878612855

theorem tailTrace_4998230 : CollatzResearch.WordTrace tailWord_4998230 prefixEnd_4998230 855498137240694878612855 := by
  unfold tailWord_4998230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11393776542642113410511009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121533616454849209712117429 11393776542642113410511009)
  ·
    refine ⟨8545332406981585057883257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11393776542642113410511009 8545332406981585057883257)
    ·
      refine ⟨6408999305236188793412443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8545332406981585057883257 6408999305236188793412443)
      ·
        refine ⟨9613498957854283190118665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408999305236188793412443 9613498957854283190118665)
        ·
          refine ⟨7210124218390712392588999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9613498957854283190118665 7210124218390712392588999)
          ·
            refine ⟨10815186327586068588883499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210124218390712392588999 10815186327586068588883499)
            ·
              refine ⟨16222779491379102883325249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10815186327586068588883499 16222779491379102883325249)
              ·
                refine ⟨12167084618534327162493937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16222779491379102883325249 12167084618534327162493937)
                ·
                  refine ⟨9125313463900745371870453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12167084618534327162493937 9125313463900745371870453)
                  ·
                    refine ⟨855498137240694878612855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9125313463900745371870453 855498137240694878612855)
                    ·
                      rfl

theorem cell23_4998230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4998230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998230 prefixEnd_4998230 := by exact prefixLift 4998230
  have htrace : WordTrace (prefixWord ++ tailWord_4998230) baseStart_4998230 baseEnd_4998230 := by
    simpa [prefixWord, tailWord_4998230, baseEnd_4998230] using wordTrace_append hprefix tailTrace_4998230
  have hstable : (prefixWord ++ tailWord_4998230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998230).length < 2 ^ (prefixWord ++ tailWord_4998230).sum := by decide
  have hdescent : baseEnd_4998230 < baseStart_4998230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998239 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 6]
def baseStart_4998239 : Nat := 118140960795 + 4998239 * 2 ^ 59
def prefixEnd_4998239 : Nat := 4983230072969 + 3 ^ 40 * 4998239 * 2
def baseEnd_4998239 : Nat := 285166559227552788958447

theorem tailTrace_4998239 : CollatzResearch.WordTrace tailWord_4998239 prefixEnd_4998239 285166559227552788958447 := by
  unfold tailWord_4998239
  simp only [CollatzResearch.WordTrace]
  refine ⟨182300752939241209105253771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121533835292827472736835847 182300752939241209105253771)
  ·
    refine ⟨273451129408861813657880657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182300752939241209105253771 273451129408861813657880657)
    ·
      refine ⟨205088347056646360243410493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273451129408861813657880657 205088347056646360243410493)
      ·
        refine ⟨76908130146242385091278935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205088347056646360243410493 76908130146242385091278935)
        ·
          refine ⟨115362195219363577636918403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76908130146242385091278935 115362195219363577636918403)
          ·
            refine ⟨173043292829045366455377605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115362195219363577636918403 173043292829045366455377605)
            ·
              refine ⟨32445617405446006210383301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173043292829045366455377605 32445617405446006210383301)
              ·
                refine ⟨6083553263521126164446869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32445617405446006210383301 6083553263521126164446869)
                ·
                  refine ⟨285166559227552788958447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6083553263521126164446869 285166559227552788958447)
                  ·
                    rfl

theorem cell23_4998239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 6].length) (baseStart_4998239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998239 prefixEnd_4998239 := by exact prefixLift 4998239
  have htrace : WordTrace (prefixWord ++ tailWord_4998239) baseStart_4998239 baseEnd_4998239 := by
    simpa [prefixWord, tailWord_4998239, baseEnd_4998239] using wordTrace_append hprefix tailTrace_4998239
  have hstable : (prefixWord ++ tailWord_4998239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998239).length < 2 ^ (prefixWord ++ tailWord_4998239).sum := by decide
  have hdescent : baseEnd_4998239 < baseStart_4998239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998319 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_4998319 : Nat := 118140960795 + 4998319 * 2 ^ 59
def prefixEnd_4998319 : Nat := 4983230072969 + 3 ^ 40 * 4998319 * 2
def baseEnd_4998319 : Nat := 2566540111500334787625655

theorem tailTrace_4998319 : CollatzResearch.WordTrace tailWord_4998319 prefixEnd_4998319 2566540111500334787625655 := by
  unfold tailWord_4998319
  simp only [CollatzResearch.WordTrace]
  refine ⟨182303670778951382768166011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121535780519300921845444007 182303670778951382768166011)
  ·
    refine ⟨273455506168427074152249017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182303670778951382768166011 273455506168427074152249017)
    ·
      refine ⟨205091629626320305614186763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273455506168427074152249017 205091629626320305614186763)
      ·
        refine ⟨307637444439480458421280145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205091629626320305614186763 307637444439480458421280145)
        ·
          refine ⟨230728083329610343815960109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307637444439480458421280145 230728083329610343815960109)
          ·
            refine ⟨86523031248603878930985041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230728083329610343815960109 86523031248603878930985041)
            ·
              refine ⟨64892273436452909198238781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86523031248603878930985041 64892273436452909198238781)
              ·
                refine ⟨24334602538669840949339543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64892273436452909198238781 24334602538669840949339543)
                ·
                  refine ⟨36501903808004761424009315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24334602538669840949339543 36501903808004761424009315)
                  ·
                    refine ⟨54752855712007142136013973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36501903808004761424009315 54752855712007142136013973)
                    ·
                      refine ⟨2566540111500334787625655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54752855712007142136013973 2566540111500334787625655)
                      ·
                        rfl

theorem cell23_4998319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_4998319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998319 prefixEnd_4998319 := by exact prefixLift 4998319
  have htrace : WordTrace (prefixWord ++ tailWord_4998319) baseStart_4998319 baseEnd_4998319 := by
    simpa [prefixWord, tailWord_4998319, baseEnd_4998319] using wordTrace_append hprefix tailTrace_4998319
  have hstable : (prefixWord ++ tailWord_4998319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998319).length < 2 ^ (prefixWord ++ tailWord_4998319).sum := by decide
  have hdescent : baseEnd_4998319 < baseStart_4998319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998323 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 5, 2, 2]
def baseStart_4998323 : Nat := 118140960795 + 4998323 * 2 ^ 59
def prefixEnd_4998323 : Nat := 4983230072969 + 3 ^ 40 * 4998323 * 2
def baseEnd_4998323 : Nat := 2566542165422952771975637

theorem tailTrace_4998323 : CollatzResearch.WordTrace tailWord_4998323 prefixEnd_4998323 2566542165422952771975637 := by
  unfold tailWord_4998323
  simp only [CollatzResearch.WordTrace]
  refine ⟨182303816670936891451311623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121535877780624594300874415 182303816670936891451311623)
  ·
    refine ⟨273455725006405337176967435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182303816670936891451311623 273455725006405337176967435)
    ·
      refine ⟨410183587509608005765451153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273455725006405337176967435 410183587509608005765451153)
      ·
        refine ⟨307637690632206004324088365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410183587509608005765451153 307637690632206004324088365)
        ·
          refine ⟨115364133987077251621533137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307637690632206004324088365 115364133987077251621533137)
          ·
            refine ⟨86523100490307938716149853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115364133987077251621533137 86523100490307938716149853)
            ·
              refine ⟨32446162683865477018556195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86523100490307938716149853 32446162683865477018556195)
              ·
                refine ⟨48669244025798215527834293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32446162683865477018556195 48669244025798215527834293)
                ·
                  refine ⟨4562741627418582705734465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48669244025798215527834293 4562741627418582705734465)
                  ·
                    refine ⟨3422056220563937029300849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4562741627418582705734465 3422056220563937029300849)
                    ·
                      refine ⟨2566542165422952771975637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422056220563937029300849 2566542165422952771975637)
                      ·
                        rfl

theorem cell23_4998323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 2, 2].length) (baseStart_4998323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998323 prefixEnd_4998323 := by exact prefixLift 4998323
  have htrace : WordTrace (prefixWord ++ tailWord_4998323) baseStart_4998323 baseEnd_4998323 := by
    simpa [prefixWord, tailWord_4998323, baseEnd_4998323] using wordTrace_append hprefix tailTrace_4998323
  have hstable : (prefixWord ++ tailWord_4998323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998323).length < 2 ^ (prefixWord ++ tailWord_4998323).sum := by decide
  have hdescent : baseEnd_4998323 < baseStart_4998323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998337 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 1, 5]
def baseStart_4998337 : Nat := 118140960795 + 4998337 * 2 ^ 59
def prefixEnd_4998337 : Nat := 4983230072969 + 3 ^ 40 * 4998337 * 2
def baseEnd_4998337 : Nat := 855516451384038572400191

theorem tailTrace_4998337 : CollatzResearch.WordTrace tailWord_4998337 prefixEnd_4998337 855516451384038572400191 := by
  unfold tailWord_4998337
  simp only [CollatzResearch.WordTrace]
  refine ⟨182304327292886171842321265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121536218195257447894880843 182304327292886171842321265)
  ·
    refine ⟨136728245469664628881740949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182304327292886171842321265 136728245469664628881740949)
    ·
      refine ⟨6409136506390529478831607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 136728245469664628881740949 6409136506390529478831607)
      ·
        refine ⟨9613704759585794218247411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6409136506390529478831607 9613704759585794218247411)
        ·
          refine ⟨14420557139378691327371117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9613704759585794218247411 14420557139378691327371117)
          ·
            refine ⟨5407708927267009247764169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14420557139378691327371117 5407708927267009247764169)
            ·
              refine ⟨4055781695450256935823127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5407708927267009247764169 4055781695450256935823127)
              ·
                refine ⟨6083672543175385403734691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055781695450256935823127 6083672543175385403734691)
                ·
                  refine ⟨9125508814763078105602037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083672543175385403734691 9125508814763078105602037)
                  ·
                    refine ⟨855516451384038572400191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9125508814763078105602037 855516451384038572400191)
                    ·
                      rfl

theorem cell23_4998337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_4998337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998337 prefixEnd_4998337 := by exact prefixLift 4998337
  have htrace : WordTrace (prefixWord ++ tailWord_4998337) baseStart_4998337 baseEnd_4998337 := by
    simpa [prefixWord, tailWord_4998337, baseEnd_4998337] using wordTrace_append hprefix tailTrace_4998337
  have hstable : (prefixWord ++ tailWord_4998337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998337).length < 2 ^ (prefixWord ++ tailWord_4998337).sum := by decide
  have hdescent : baseEnd_4998337 < baseStart_4998337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998340 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_4998340 : Nat := 118140960795 + 4998340 * 2 ^ 59
def prefixEnd_4998340 : Nat := 4983230072969 + 3 ^ 40 * 4998340 * 2
def baseEnd_4998340 : Nat := 2566550894594079205463059

theorem tailTrace_4998340 : CollatzResearch.WordTrace tailWord_4998340 prefixEnd_4998340 2566550894594079205463059 := by
  unfold tailWord_4998340
  simp only [CollatzResearch.WordTrace]
  refine ⟨91152218355937651677340237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121536291141250202236453649 91152218355937651677340237)
  ·
    refine ⟨34182081883476619379002589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91152218355937651677340237 34182081883476619379002589)
    ·
      refine ⟨12818280706303732267125971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34182081883476619379002589 12818280706303732267125971)
      ·
        refine ⟨19227421059455598400688957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12818280706303732267125971 19227421059455598400688957)
        ·
          refine ⟨7210282897295849400258359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19227421059455598400688957 7210282897295849400258359)
          ·
            refine ⟨10815424345943774100387539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210282897295849400258359 10815424345943774100387539)
            ·
              refine ⟨16223136518915661150581309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10815424345943774100387539 16223136518915661150581309)
              ·
                refine ⟨6083676194593372931467991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16223136518915661150581309 6083676194593372931467991)
                ·
                  refine ⟨9125514291890059397201987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083676194593372931467991 9125514291890059397201987)
                  ·
                    refine ⟨13688271437835089095802981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9125514291890059397201987 13688271437835089095802981)
                    ·
                      refine ⟨2566550894594079205463059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13688271437835089095802981 2566550894594079205463059)
                      ·
                        rfl

theorem cell23_4998340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_4998340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998340 prefixEnd_4998340 := by exact prefixLift 4998340
  have htrace : WordTrace (prefixWord ++ tailWord_4998340) baseStart_4998340 baseEnd_4998340 := by
    simpa [prefixWord, tailWord_4998340, baseEnd_4998340] using wordTrace_append hprefix tailTrace_4998340
  have hstable : (prefixWord ++ tailWord_4998340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998340).length < 2 ^ (prefixWord ++ tailWord_4998340).sum := by decide
  have hdescent : baseEnd_4998340 < baseStart_4998340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998357 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4998357 : Nat := 118140960795 + 4998357 * 2 ^ 59
def prefixEnd_4998357 : Nat := 4983230072969 + 3 ^ 40 * 4998357 * 2
def baseEnd_4998357 : Nat := 2566559623765205638950481

theorem tailTrace_4998357 : CollatzResearch.WordTrace tailWord_4998357 prefixEnd_4998357 2566559623765205638950481 := by
  unfold tailWord_4998357
  simp only [CollatzResearch.WordTrace]
  refine ⟨182305056752813715258049325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121536704501875810172032883 182305056752813715258049325)
  ·
    refine ⟨68364396282305143221768497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182305056752813715258049325 68364396282305143221768497)
    ·
      refine ⟨51273297211728857416326373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68364396282305143221768497 51273297211728857416326373)
      ·
        refine ⟨9613743227199160765561195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51273297211728857416326373 9613743227199160765561195)
        ·
          refine ⟨14420614840798741148341793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9613743227199160765561195 14420614840798741148341793)
          ·
            refine ⟨10815461130599055861256345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14420614840798741148341793 10815461130599055861256345)
            ·
              refine ⟨8111595847949291895942259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10815461130599055861256345 8111595847949291895942259)
              ·
                refine ⟨12167393771923937843913389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8111595847949291895942259 12167393771923937843913389)
                ·
                  refine ⟨4562772664471476691467521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12167393771923937843913389 4562772664471476691467521)
                  ·
                    refine ⟨3422079498353607518600641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4562772664471476691467521 3422079498353607518600641)
                    ·
                      refine ⟨2566559623765205638950481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422079498353607518600641 2566559623765205638950481)
                      ·
                        rfl

theorem cell23_4998357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4998357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998357 prefixEnd_4998357 := by exact prefixLift 4998357
  have htrace : WordTrace (prefixWord ++ tailWord_4998357) baseStart_4998357 baseEnd_4998357 := by
    simpa [prefixWord, tailWord_4998357, baseEnd_4998357] using wordTrace_append hprefix tailTrace_4998357
  have hstable : (prefixWord ++ tailWord_4998357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998357).length < 2 ^ (prefixWord ++ tailWord_4998357).sum := by decide
  have hdescent : baseEnd_4998357 < baseStart_4998357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998359 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 9]
def baseStart_4998359 : Nat := 118140960795 + 4998359 * 2 ^ 59
def prefixEnd_4998359 : Nat := 4983230072969 + 3 ^ 40 * 4998359 * 2
def baseEnd_4998359 : Nat := 855520216908838210375157

theorem tailTrace_4998359 : CollatzResearch.WordTrace tailWord_4998359 prefixEnd_4998359 855520216908838210375157 := by
  unfold tailWord_4998359
  simp only [CollatzResearch.WordTrace]
  refine ⟨182305129698806469599622131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121536753132537646399748087 182305129698806469599622131)
  ·
    refine ⟨273457694548209704399433197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182305129698806469599622131 273457694548209704399433197)
    ·
      refine ⟨102546635455578639149787449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273457694548209704399433197 102546635455578639149787449)
      ·
        refine ⟨76909976591683979362340587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102546635455578639149787449 76909976591683979362340587)
        ·
          refine ⟨115364964887525969043510881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76909976591683979362340587 115364964887525969043510881)
          ·
            refine ⟨86523723665644476782633161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115364964887525969043510881 86523723665644476782633161)
            ·
              refine ⟨64892792749233357586974871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86523723665644476782633161 64892792749233357586974871)
              ·
                refine ⟨97339189123850036380462307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64892792749233357586974871 97339189123850036380462307)
                ·
                  refine ⟨146008783685775054570693461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97339189123850036380462307 146008783685775054570693461)
                  ·
                    refine ⟨855520216908838210375157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146008783685775054570693461 855520216908838210375157)
                    ·
                      rfl

theorem cell23_4998359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_4998359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998359 prefixEnd_4998359 := by exact prefixLift 4998359
  have htrace : WordTrace (prefixWord ++ tailWord_4998359) baseStart_4998359 baseEnd_4998359 := by
    simpa [prefixWord, tailWord_4998359, baseEnd_4998359] using wordTrace_append hprefix tailTrace_4998359
  have hstable : (prefixWord ++ tailWord_4998359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998359).length < 2 ^ (prefixWord ++ tailWord_4998359).sum := by decide
  have hdescent : baseEnd_4998359 < baseStart_4998359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998434 : List Nat := [3, 3, 1, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_4998434 : Nat := 118140960795 + 4998434 * 2 ^ 59
def prefixEnd_4998434 : Nat := 4983230072969 + 3 ^ 40 * 4998434 * 2
def baseEnd_4998434 : Nat := 2566599161775601837687627

theorem tailTrace_4998434 : CollatzResearch.WordTrace tailWord_4998434 prefixEnd_4998434 2566599161775601837687627 := by
  unfold tailWord_4998434
  simp only [CollatzResearch.WordTrace]
  refine ⟨45576966293383689352150589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121538576782356504939068237 45576966293383689352150589)
  ·
    refine ⟨17091362360018883507056471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45576966293383689352150589 17091362360018883507056471)
    ·
      refine ⟨25637043540028325260584707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17091362360018883507056471 25637043540028325260584707)
      ·
        refine ⟨38455565310042487890877061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25637043540028325260584707 38455565310042487890877061)
        ·
          refine ⟨7210418495632966479539449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38455565310042487890877061 7210418495632966479539449)
          ·
            refine ⟨5407813871724724859654587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7210418495632966479539449 5407813871724724859654587)
            ·
              refine ⟨8111720807587087289481881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407813871724724859654587 8111720807587087289481881)
              ·
                refine ⟨6083790605690315467111411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8111720807587087289481881 6083790605690315467111411)
                ·
                  refine ⟨9125685908535473200667117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6083790605690315467111411 9125685908535473200667117)
                  ·
                    refine ⟨3422132215700802450250169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9125685908535473200667117 3422132215700802450250169)
                    ·
                      refine ⟨2566599161775601837687627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422132215700802450250169 2566599161775601837687627)
                      ·
                        rfl

theorem cell23_4998434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_4998434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998434 prefixEnd_4998434 := by exact prefixLift 4998434
  have htrace : WordTrace (prefixWord ++ tailWord_4998434) baseStart_4998434 baseEnd_4998434 := by
    simpa [prefixWord, tailWord_4998434, baseEnd_4998434] using wordTrace_append hprefix tailTrace_4998434
  have hstable : (prefixWord ++ tailWord_4998434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998434).length < 2 ^ (prefixWord ++ tailWord_4998434).sum := by decide
  have hdescent : baseEnd_4998434 < baseStart_4998434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998436 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 9]
def baseStart_4998436 : Nat := 118140960795 + 4998436 * 2 ^ 59
def prefixEnd_4998436 : Nat := 4983230072969 + 3 ^ 40 * 4998436 * 2
def baseEnd_4998436 : Nat := 285177798748545647762513

theorem tailTrace_4998436 : CollatzResearch.WordTrace tailWord_4998436 prefixEnd_4998436 285177798748545647762513 := by
  unfold tailWord_4998436
  simp only [CollatzResearch.WordTrace]
  refine ⟨91153969059763755875087581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121538625413018341166783441 91153969059763755875087581)
  ·
    refine ⟨34182738397411408453157843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91153969059763755875087581 34182738397411408453157843)
    ·
      refine ⟨51274107596117112679736765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34182738397411408453157843 51274107596117112679736765)
      ·
        refine ⟨19227790348543917254901287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51274107596117112679736765 19227790348543917254901287)
        ·
          refine ⟨28841685522815875882351931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19227790348543917254901287 28841685522815875882351931)
          ·
            refine ⟨43262528284223813823527897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28841685522815875882351931 43262528284223813823527897)
            ·
              refine ⟨32446896213167860367645923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43262528284223813823527897 32446896213167860367645923)
              ·
                refine ⟨48670344319751790551468885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32446896213167860367645923 48670344319751790551468885)
                ·
                  refine ⟨285177798748545647762513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48670344319751790551468885 285177798748545647762513)
                  ·
                    rfl

theorem cell23_4998436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_4998436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998436 prefixEnd_4998436 := by exact prefixLift 4998436
  have htrace : WordTrace (prefixWord ++ tailWord_4998436) baseStart_4998436 baseEnd_4998436 := by
    simpa [prefixWord, tailWord_4998436, baseEnd_4998436] using wordTrace_append hprefix tailTrace_4998436
  have hstable : (prefixWord ++ tailWord_4998436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998436).length < 2 ^ (prefixWord ++ tailWord_4998436).sum := by decide
  have hdescent : baseEnd_4998436 < baseStart_4998436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998473 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 2, 5, 2]
def baseStart_4998473 : Nat := 118140960795 + 4998473 * 2 ^ 59
def prefixEnd_4998473 : Nat := 4983230072969 + 3 ^ 40 * 4998473 * 2
def baseEnd_4998473 : Nat := 2566619187521127185099947

theorem tailTrace_4998473 : CollatzResearch.WordTrace tailWord_4998473 prefixEnd_4998473 2566619187521127185099947 := by
  unfold tailWord_4998473
  simp only [CollatzResearch.WordTrace]
  refine ⟨182309287620393467069272073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121539525080262311379514715 182309287620393467069272073)
  ·
    refine ⟨136731965715295100301954055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182309287620393467069272073 136731965715295100301954055)
    ·
      refine ⟨205097948572942650452931083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136731965715295100301954055 205097948572942650452931083)
      ·
        refine ⟨307646922859413975679396625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205097948572942650452931083 307646922859413975679396625)
        ·
          refine ⟨230735192144560481759547469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307646922859413975679396625 230735192144560481759547469)
          ·
            refine ⟨86525697054210180659830301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230735192144560481759547469 86525697054210180659830301)
            ·
              refine ⟨32447136395328817747436363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86525697054210180659830301 32447136395328817747436363)
              ·
                refine ⟨48670704592993226621154545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32447136395328817747436363 48670704592993226621154545)
                ·
                  refine ⟨36503028444744919965865909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48670704592993226621154545 36503028444744919965865909)
                  ·
                    refine ⟨3422158916694836246799929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36503028444744919965865909 3422158916694836246799929)
                    ·
                      refine ⟨2566619187521127185099947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422158916694836246799929 2566619187521127185099947)
                      ·
                        rfl

theorem cell23_4998473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 5, 2].length) (baseStart_4998473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998473 prefixEnd_4998473 := by exact prefixLift 4998473
  have htrace : WordTrace (prefixWord ++ tailWord_4998473) baseStart_4998473 baseEnd_4998473 := by
    simpa [prefixWord, tailWord_4998473, baseEnd_4998473] using wordTrace_append hprefix tailTrace_4998473
  have hstable : (prefixWord ++ tailWord_4998473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998473).length < 2 ^ (prefixWord ++ tailWord_4998473).sum := by decide
  have hdescent : baseEnd_4998473 < baseStart_4998473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998477 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4998477 : Nat := 118140960795 + 4998477 * 2 ^ 59
def prefixEnd_4998477 : Nat := 4983230072969 + 3 ^ 40 * 4998477 * 2
def baseEnd_4998477 : Nat := 2566621241443745169449929

theorem tailTrace_4998477 : CollatzResearch.WordTrace tailWord_4998477 prefixEnd_4998477 2566621241443745169449929 := by
  unfold tailWord_4998477
  simp only [CollatzResearch.WordTrace]
  refine ⟨182309433512378975752417685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121539622341585983834945123 182309433512378975752417685)
  ·
    refine ⟨8545754695892764488394579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 182309433512378975752417685 8545754695892764488394579)
    ·
      refine ⟨12818632043839146732591869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8545754695892764488394579 12818632043839146732591869)
      ·
        refine ⟨4806987016439680024721951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12818632043839146732591869 4806987016439680024721951)
        ·
          refine ⟨7210480524659520037082927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806987016439680024721951 7210480524659520037082927)
          ·
            refine ⟨10815720786989280055624391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210480524659520037082927 10815720786989280055624391)
            ·
              refine ⟨16223581180483920083436587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10815720786989280055624391 16223581180483920083436587)
              ·
                refine ⟨24335371770725880125154881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16223581180483920083436587 24335371770725880125154881)
                ·
                  refine ⟨18251528828044410093866161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24335371770725880125154881 18251528828044410093866161)
                  ·
                    refine ⟨13688646621033307570399621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18251528828044410093866161 13688646621033307570399621)
                    ·
                      refine ⟨2566621241443745169449929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13688646621033307570399621 2566621241443745169449929)
                      ·
                        rfl

theorem cell23_4998477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4998477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998477 prefixEnd_4998477 := by exact prefixLift 4998477
  have htrace : WordTrace (prefixWord ++ tailWord_4998477) baseStart_4998477 baseEnd_4998477 := by
    simpa [prefixWord, tailWord_4998477, baseEnd_4998477] using wordTrace_append hprefix tailTrace_4998477
  have hstable : (prefixWord ++ tailWord_4998477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998477).length < 2 ^ (prefixWord ++ tailWord_4998477).sum := by decide
  have hdescent : baseEnd_4998477 < baseStart_4998477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998500 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_4998500 : Nat := 118140960795 + 4998500 * 2 ^ 59
def prefixEnd_4998500 : Nat := 4983230072969 + 3 ^ 40 * 4998500 * 2
def baseEnd_4998500 : Nat := 855544350499599526487441

theorem tailTrace_4998500 : CollatzResearch.WordTrace tailWord_4998500 prefixEnd_4998500 855544350499599526487441 := by
  unfold tailWord_4998500
  simp only [CollatzResearch.WordTrace]
  refine ⟨91155136195647825340252477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121540181594197100453669969 91155136195647825340252477)
  ·
    refine ⟨34183176073367934502594679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91155136195647825340252477 34183176073367934502594679)
    ·
      refine ⟨51274764110051901753892019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34183176073367934502594679 51274764110051901753892019)
      ·
        refine ⟨76912146165077852630838029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51274764110051901753892019 76912146165077852630838029)
        ·
          refine ⟨28842054811904194736564261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76912146165077852630838029 28842054811904194736564261)
          ·
            refine ⟨5407885277232036513105799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28842054811904194736564261 5407885277232036513105799)
            ·
              refine ⟨8111827915848054769658699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407885277232036513105799 8111827915848054769658699)
              ·
                refine ⟨12167741873772082154488049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8111827915848054769658699 12167741873772082154488049)
                ·
                  refine ⟨9125806405329061615866037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12167741873772082154488049 9125806405329061615866037)
                  ·
                    refine ⟨855544350499599526487441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9125806405329061615866037 855544350499599526487441)
                    ·
                      rfl

theorem cell23_4998500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_4998500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998500 prefixEnd_4998500 := by exact prefixLift 4998500
  have htrace : WordTrace (prefixWord ++ tailWord_4998500) baseStart_4998500 baseEnd_4998500 := by
    simpa [prefixWord, tailWord_4998500, baseEnd_4998500] using wordTrace_append hprefix tailTrace_4998500
  have hstable : (prefixWord ++ tailWord_4998500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998500).length < 2 ^ (prefixWord ++ tailWord_4998500).sum := by decide
  have hdescent : baseEnd_4998500 < baseStart_4998500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998523 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 3]
def baseStart_4998523 : Nat := 118140960795 + 4998523 * 2 ^ 59
def prefixEnd_4998523 : Nat := 4983230072969 + 3 ^ 40 * 4998523 * 2
def baseEnd_4998523 : Nat := 2566644861553851989474717

theorem tailTrace_4998523 : CollatzResearch.WordTrace tailWord_4998523 prefixEnd_4998523 2566644861553851989474717 := by
  unfold tailWord_4998523
  simp only [CollatzResearch.WordTrace]
  refine ⟨182311111270212325608592223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121540740846808217072394815 182311111270212325608592223)
  ·
    refine ⟨273466666905318488412888335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182311111270212325608592223 273466666905318488412888335)
    ·
      refine ⟨410200000357977732619332503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273466666905318488412888335 410200000357977732619332503)
      ·
        refine ⟨615300000536966598928998755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410200000357977732619332503 615300000536966598928998755)
        ·
          refine ⟨922950000805449898393498133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615300000536966598928998755 922950000805449898393498133)
          ·
            refine ⟨43263281287755463987195225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 922950000805449898393498133 43263281287755463987195225)
            ·
              refine ⟨32447460965816597990396419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43263281287755463987195225 32447460965816597990396419)
              ·
                refine ⟨48671191448724896985594629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32447460965816597990396419 48671191448724896985594629)
                ·
                  refine ⟨9125848396635918184798993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48671191448724896985594629 9125848396635918184798993)
                  ·
                    refine ⟨6844386297476938638599245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9125848396635918184798993 6844386297476938638599245)
                    ·
                      refine ⟨2566644861553851989474717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6844386297476938638599245 2566644861553851989474717)
                      ·
                        rfl

theorem cell23_4998523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 3].length) (baseStart_4998523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998523 prefixEnd_4998523 := by exact prefixLift 4998523
  have htrace : WordTrace (prefixWord ++ tailWord_4998523) baseStart_4998523 baseEnd_4998523 := by
    simpa [prefixWord, tailWord_4998523, baseEnd_4998523] using wordTrace_append hprefix tailTrace_4998523
  have hstable : (prefixWord ++ tailWord_4998523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998523).length < 2 ^ (prefixWord ++ tailWord_4998523).sum := by decide
  have hdescent : baseEnd_4998523 < baseStart_4998523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998614 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_4998614 : Nat := 118140960795 + 4998614 * 2 ^ 59
def prefixEnd_4998614 : Nat := 4983230072969 + 3 ^ 40 * 4998614 * 2
def baseEnd_4998614 : Nat := 2566691588293411133436799

theorem tailTrace_4998614 : CollatzResearch.WordTrace tailWord_4998614 prefixEnd_4998614 2566691588293411133436799 := by
  unfold tailWord_4998614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11394651894555165509384681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121542953541921765433436597 11394651894555165509384681)
  ·
    refine ⟨8545988920916374132038511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11394651894555165509384681 8545988920916374132038511)
    ·
      refine ⟨12818983381374561198057767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8545988920916374132038511 12818983381374561198057767)
      ·
        refine ⟨19228475072061841797086651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12818983381374561198057767 19228475072061841797086651)
        ·
          refine ⟨28842712608092762695629977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19228475072061841797086651 28842712608092762695629977)
          ·
            refine ⟨21632034456069572021722483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28842712608092762695629977 21632034456069572021722483)
            ·
              refine ⟨32448051684104358032583725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21632034456069572021722483 32448051684104358032583725)
              ·
                refine ⟨12168019381539134262218897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32448051684104358032583725 12168019381539134262218897)
                ·
                  refine ⟨9126014536154350696664173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12168019381539134262218897 9126014536154350696664173)
                  ·
                    refine ⟨3422255451057881511249065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9126014536154350696664173 3422255451057881511249065)
                    ·
                      refine ⟨2566691588293411133436799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422255451057881511249065 2566691588293411133436799)
                      ·
                        rfl

theorem cell23_4998614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_4998614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998614 prefixEnd_4998614 := by exact prefixLift 4998614
  have htrace : WordTrace (prefixWord ++ tailWord_4998614) baseStart_4998614 baseEnd_4998614 := by
    simpa [prefixWord, tailWord_4998614, baseEnd_4998614] using wordTrace_append hprefix tailTrace_4998614
  have hstable : (prefixWord ++ tailWord_4998614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998614).length < 2 ^ (prefixWord ++ tailWord_4998614).sum := by decide
  have hdescent : baseEnd_4998614 < baseStart_4998614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998654 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_4998654 : Nat := 118140960795 + 4998654 * 2 ^ 59
def prefixEnd_4998654 : Nat := 4983230072969 + 3 ^ 40 * 4998654 * 2
def baseEnd_4998654 : Nat := 855570709173196992312205

theorem tailTrace_4998654 : CollatzResearch.WordTrace tailWord_4998654 prefixEnd_4998654 855570709173196992312205 := by
  unfold tailWord_4998654
  simp only [CollatzResearch.WordTrace]
  refine ⟨22789486154092216872701377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121543926155158489987740677 22789486154092216872701377)
  ·
    refine ⟨17092114615569162654526033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22789486154092216872701377 17092114615569162654526033)
    ·
      refine ⟨12819085961676871990894525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17092114615569162654526033 12819085961676871990894525)
      ·
        refine ⟨4807157235628826996585447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12819085961676871990894525 4807157235628826996585447)
        ·
          refine ⟨7210735853443240494878171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4807157235628826996585447 7210735853443240494878171)
          ·
            refine ⟨10816103780164860742317257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210735853443240494878171 10816103780164860742317257)
            ·
              refine ⟨8112077835123645556737943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10816103780164860742317257 8112077835123645556737943)
              ·
                refine ⟨12168116752685468335106915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8112077835123645556737943 12168116752685468335106915)
                ·
                  refine ⟨18252175129028202502660373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12168116752685468335106915 18252175129028202502660373)
                  ·
                    refine ⟨855570709173196992312205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18252175129028202502660373 855570709173196992312205)
                    ·
                      rfl

theorem cell23_4998654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_4998654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998654 prefixEnd_4998654 := by exact prefixLift 4998654
  have htrace : WordTrace (prefixWord ++ tailWord_4998654) baseStart_4998654 baseEnd_4998654 := by
    simpa [prefixWord, tailWord_4998654, baseEnd_4998654] using wordTrace_append hprefix tailTrace_4998654
  have hstable : (prefixWord ++ tailWord_4998654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998654).length < 2 ^ (prefixWord ++ tailWord_4998654).sum := by decide
  have hdescent : baseEnd_4998654 < baseStart_4998654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998657 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_4998657 : Nat := 118140960795 + 4998657 * 2 ^ 59
def prefixEnd_4998657 : Nat := 4983230072969 + 3 ^ 40 * 4998657 * 2
def baseEnd_4998657 : Nat := 2566713667961554465199101

theorem tailTrace_4998657 : CollatzResearch.WordTrace tailWord_4998657 prefixEnd_4998657 2566713667961554465199101 := by
  unfold tailWord_4998657
  simp only [CollatzResearch.WordTrace]
  refine ⟨182315998651726866493970225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121543999101151244329313483 182315998651726866493970225)
  ·
    refine ⟨136736998988795149870477669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182315998651726866493970225 136736998988795149870477669)
    ·
      refine ⟨25638187310399090600714563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136736998988795149870477669 25638187310399090600714563)
      ·
        refine ⟨38457280965598635901071845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25638187310399090600714563 38457280965598635901071845)
        ·
          refine ⟨7210740181049744231450971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38457280965598635901071845 7210740181049744231450971)
          ·
            refine ⟨10816110271574616347176457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210740181049744231450971 10816110271574616347176457)
            ·
              refine ⟨8112082703680962260382343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10816110271574616347176457 8112082703680962260382343)
              ·
                refine ⟨12168124055521443390573515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8112082703680962260382343 12168124055521443390573515)
                ·
                  refine ⟨18252186083282165085860273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12168124055521443390573515 18252186083282165085860273)
                  ·
                    refine ⟨13689139562461623814395205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18252186083282165085860273 13689139562461623814395205)
                    ·
                      refine ⟨2566713667961554465199101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13689139562461623814395205 2566713667961554465199101)
                      ·
                        rfl

theorem cell23_4998657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_4998657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998657 prefixEnd_4998657 := by exact prefixLift 4998657
  have htrace : WordTrace (prefixWord ++ tailWord_4998657) baseStart_4998657 baseEnd_4998657 := by
    simpa [prefixWord, tailWord_4998657, baseEnd_4998657] using wordTrace_append hprefix tailTrace_4998657
  have hstable : (prefixWord ++ tailWord_4998657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998657).length < 2 ^ (prefixWord ++ tailWord_4998657).sum := by decide
  have hdescent : baseEnd_4998657 < baseStart_4998657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998673 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_4998673 : Nat := 118140960795 + 4998673 * 2 ^ 59
def prefixEnd_4998673 : Nat := 4983230072969 + 3 ^ 40 * 4998673 * 2
def baseEnd_4998673 : Nat := 2566721883652026402599027

theorem tailTrace_4998673 : CollatzResearch.WordTrace tailWord_4998673 prefixEnd_4998673 2566721883652026402599027 := by
  unfold tailWord_4998673
  simp only [CollatzResearch.WordTrace]
  refine ⟨182316582219668901226552673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121544388146445934151035115 182316582219668901226552673)
  ·
    refine ⟨136737436664751675919914505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182316582219668901226552673 136737436664751675919914505)
    ·
      refine ⟨102553077498563756939935879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136737436664751675919914505 102553077498563756939935879)
      ·
        refine ⟨153829616247845635409903819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102553077498563756939935879 153829616247845635409903819)
        ·
          refine ⟨230744424371768453114855729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153829616247845635409903819 230744424371768453114855729)
          ·
            refine ⟨173058318278826339836141797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230744424371768453114855729 173058318278826339836141797)
            ·
              refine ⟨32448434677279938719276587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173058318278826339836141797 32448434677279938719276587)
              ·
                refine ⟨48672652015919908078914881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32448434677279938719276587 48672652015919908078914881)
                ·
                  refine ⟨36504489011939931059186161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48672652015919908078914881 36504489011939931059186161)
                  ·
                    refine ⟨27378366758954948294389621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36504489011939931059186161 27378366758954948294389621)
                    ·
                      refine ⟨2566721883652026402599027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27378366758954948294389621 2566721883652026402599027)
                      ·
                        rfl

theorem cell23_4998673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_4998673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998673 prefixEnd_4998673 := by exact prefixLift 4998673
  have htrace : WordTrace (prefixWord ++ tailWord_4998673) baseStart_4998673 baseEnd_4998673 := by
    simpa [prefixWord, tailWord_4998673, baseEnd_4998673] using wordTrace_append hprefix tailTrace_4998673
  have hstable : (prefixWord ++ tailWord_4998673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998673).length < 2 ^ (prefixWord ++ tailWord_4998673).sum := by decide
  have hdescent : baseEnd_4998673 < baseStart_4998673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998700 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 8, 2]
def baseStart_4998700 : Nat := 118140960795 + 4998700 * 2 ^ 59
def prefixEnd_4998700 : Nat := 4983230072969 + 3 ^ 40 * 4998700 * 2
def baseEnd_4998700 : Nat := 2566735747629697796961403

theorem tailTrace_4998700 : CollatzResearch.WordTrace tailWord_4998700 prefixEnd_4998700 2566735747629697796961403 := by
  unfold tailWord_4998700
  simp only [CollatzResearch.WordTrace]
  refine ⟨91158783495285542418892777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121545044660380723225190369 91158783495285542418892777)
  ·
    refine ⟨68369087621464156814169583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91158783495285542418892777 68369087621464156814169583)
    ·
      refine ⟨102553631432196235221254375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68369087621464156814169583 102553631432196235221254375)
      ·
        refine ⟨153830447148294352831881563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102553631432196235221254375 153830447148294352831881563)
        ·
          refine ⟨230745670722441529247822345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153830447148294352831881563 230745670722441529247822345)
          ·
            refine ⟨173059253041831146935866759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230745670722441529247822345 173059253041831146935866759)
            ·
              refine ⟨259588879562746720403800139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173059253041831146935866759 259588879562746720403800139)
              ·
                refine ⟨389383319344120080605700209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259588879562746720403800139 389383319344120080605700209)
                ·
                  refine ⟨292037489508090060454275157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 389383319344120080605700209 292037489508090060454275157)
                  ·
                    refine ⟨3422314330172930395948537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 292037489508090060454275157 3422314330172930395948537)
                    ·
                      refine ⟨2566735747629697796961403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422314330172930395948537 2566735747629697796961403)
                      ·
                        rfl

theorem cell23_4998700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_4998700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998700 prefixEnd_4998700 := by exact prefixLift 4998700
  have htrace : WordTrace (prefixWord ++ tailWord_4998700) baseStart_4998700 baseEnd_4998700 := by
    simpa [prefixWord, tailWord_4998700, baseEnd_4998700] using wordTrace_append hprefix tailTrace_4998700
  have hstable : (prefixWord ++ tailWord_4998700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998700).length < 2 ^ (prefixWord ++ tailWord_4998700).sum := by decide
  have hdescent : baseEnd_4998700 < baseStart_4998700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998757 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 7]
def baseStart_4998757 : Nat := 118140960795 + 4998757 * 2 ^ 59
def prefixEnd_4998757 : Nat := 4983230072969 + 3 ^ 40 * 4998757 * 2
def baseEnd_4998757 : Nat := 285196112891889341549849

theorem tailTrace_4998757 : CollatzResearch.WordTrace tailWord_4998757 prefixEnd_4998757 285196112891889341549849 := by
  unfold tailWord_4998757
  simp only [CollatzResearch.WordTrace]
  refine ⟨182319645951364583572610525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121546430634243055715073683 182319645951364583572610525)
  ·
    refine ⟨68369867231761718839728947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182319645951364583572610525 68369867231761718839728947)
    ·
      refine ⟨102554800847642578259593421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68369867231761718839728947 102554800847642578259593421)
      ·
        refine ⟨38458050317865966847347533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102554800847642578259593421 38458050317865966847347533)
        ·
          refine ⟨14421768869199737567755325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38458050317865966847347533 14421768869199737567755325)
          ·
            refine ⟨5408163325949901587908247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14421768869199737567755325 5408163325949901587908247)
            ·
              refine ⟨8112244988924852381862371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5408163325949901587908247 8112244988924852381862371)
              ·
                refine ⟨12168367483387278572793557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8112244988924852381862371 12168367483387278572793557)
                ·
                  refine ⟨285196112891889341549849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12168367483387278572793557 285196112891889341549849)
                  ·
                    rfl

theorem cell23_4998757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_4998757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998757 prefixEnd_4998757 := by exact prefixLift 4998757
  have htrace : WordTrace (prefixWord ++ tailWord_4998757) baseStart_4998757 baseEnd_4998757 := by
    simpa [prefixWord, tailWord_4998757, baseEnd_4998757] using wordTrace_append hprefix tailTrace_4998757
  have hstable : (prefixWord ++ tailWord_4998757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998757).length < 2 ^ (prefixWord ++ tailWord_4998757).sum := by decide
  have hdescent : baseEnd_4998757 < baseStart_4998757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998768 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 2, 2, 2]
def baseStart_4998768 : Nat := 118140960795 + 4998768 * 2 ^ 59
def prefixEnd_4998768 : Nat := 4983230072969 + 3 ^ 40 * 4998768 * 2
def baseEnd_4998768 : Nat := 2566770664314203530911091

theorem tailTrace_4998768 : CollatzResearch.WordTrace tailWord_4998768 prefixEnd_4998768 2566770664314203530911091 := by
  unfold tailWord_4998768
  simp only [CollatzResearch.WordTrace]
  refine ⟨91160023577162366225630479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121546698102883154967507305 91160023577162366225630479)
  ·
    refine ⟨136740035365743549338445719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91160023577162366225630479 136740035365743549338445719)
    ·
      refine ⟨205110053048615324007668579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136740035365743549338445719 205110053048615324007668579)
      ·
        refine ⟨307665079572922986011502869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205110053048615324007668579 307665079572922986011502869)
        ·
          refine ⟨14421800604980764969289197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 307665079572922986011502869 14421800604980764969289197)
          ·
            refine ⟨5408175226867786863483449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14421800604980764969289197 5408175226867786863483449)
            ·
              refine ⟨4056131420150840147612587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5408175226867786863483449 4056131420150840147612587)
              ·
                refine ⟨6084197130226260221418881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056131420150840147612587 6084197130226260221418881)
                ·
                  refine ⟨4563147847669695166064161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6084197130226260221418881 4563147847669695166064161)
                  ·
                    refine ⟨3422360885752271374548121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4563147847669695166064161 3422360885752271374548121)
                    ·
                      refine ⟨2566770664314203530911091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422360885752271374548121 2566770664314203530911091)
                      ·
                        rfl

theorem cell23_4998768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 2, 2, 2].length) (baseStart_4998768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998768 prefixEnd_4998768 := by exact prefixLift 4998768
  have htrace : WordTrace (prefixWord ++ tailWord_4998768) baseStart_4998768 baseEnd_4998768 := by
    simpa [prefixWord, tailWord_4998768, baseEnd_4998768] using wordTrace_append hprefix tailTrace_4998768
  have hstable : (prefixWord ++ tailWord_4998768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998768).length < 2 ^ (prefixWord ++ tailWord_4998768).sum := by decide
  have hdescent : baseEnd_4998768 < baseStart_4998768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998807 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_4998807 : Nat := 118140960795 + 4998807 * 2 ^ 59
def prefixEnd_4998807 : Nat := 4983230072969 + 3 ^ 40 * 4998807 * 2
def baseEnd_4998807 : Nat := 2566790690059728878323411

theorem tailTrace_4998807 : CollatzResearch.WordTrace tailWord_4998807 prefixEnd_4998807 2566790690059728878323411 := by
  unfold tailWord_4998807
  simp only [CollatzResearch.WordTrace]
  refine ⟨182321469601183442111930675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121547646400788961407953783 182321469601183442111930675)
  ·
    refine ⟨273482204401775163167896013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182321469601183442111930675 273482204401775163167896013)
    ·
      refine ⟨102555826650665686187961005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273482204401775163167896013 102555826650665686187961005)
      ·
        refine ⟨38458434993999632320485377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102555826650665686187961005 38458434993999632320485377)
        ·
          refine ⟨28843826245499724240364033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38458434993999632320485377 28843826245499724240364033)
          ·
            refine ⟨21632869684124793180273025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28843826245499724240364033 21632869684124793180273025)
            ·
              refine ⟨16224652263093594885204769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21632869684124793180273025 16224652263093594885204769)
              ·
                refine ⟨12168489197320196163903577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16224652263093594885204769 12168489197320196163903577)
                ·
                  refine ⟨9126366897990147122927683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12168489197320196163903577 9126366897990147122927683)
                  ·
                    refine ⟨13689550346985220684391525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9126366897990147122927683 13689550346985220684391525)
                    ·
                      refine ⟨2566790690059728878323411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13689550346985220684391525 2566790690059728878323411)
                      ·
                        rfl

theorem cell23_4998807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_4998807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998807 prefixEnd_4998807 := by exact prefixLift 4998807
  have htrace : WordTrace (prefixWord ++ tailWord_4998807) baseStart_4998807 baseEnd_4998807 := by
    simpa [prefixWord, tailWord_4998807, baseEnd_4998807] using wordTrace_append hprefix tailTrace_4998807
  have hstable : (prefixWord ++ tailWord_4998807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998807).length < 2 ^ (prefixWord ++ tailWord_4998807).sum := by decide
  have hdescent : baseEnd_4998807 < baseStart_4998807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998844 : List Nat := [2, 2, 2, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4998844 : Nat := 118140960795 + 4998844 * 2 ^ 59
def prefixEnd_4998844 : Nat := 4983230072969 + 3 ^ 40 * 4998844 * 2
def baseEnd_4998844 : Nat := 2566809688843945233560741

theorem tailTrace_4998844 : CollatzResearch.WordTrace tailWord_4998844 prefixEnd_4998844 2566809688843945233560741 := by
  unfold tailWord_4998844
  simp only [CollatzResearch.WordTrace]
  refine ⟨91161409551024698715513793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121548546068032931620685057 91161409551024698715513793)
  ·
    refine ⟨68371057163268524036635345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91161409551024698715513793 68371057163268524036635345)
    ·
      refine ⟨51278292872451393027476509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68371057163268524036635345 51278292872451393027476509)
      ·
        refine ⟨19229359827169272385303691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51278292872451393027476509 19229359827169272385303691)
        ·
          refine ⟨28844039740753908577955537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19229359827169272385303691 28844039740753908577955537)
          ·
            refine ⟨21633029805565431433466653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28844039740753908577955537 21633029805565431433466653)
            ·
              refine ⟨8112386177087036787549995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21633029805565431433466653 8112386177087036787549995)
              ·
                refine ⟨12168579265630555181324993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8112386177087036787549995 12168579265630555181324993)
                ·
                  refine ⟨9126434449222916385993745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12168579265630555181324993 9126434449222916385993745)
                  ·
                    refine ⟨6844825836917187289495309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9126434449222916385993745 6844825836917187289495309)
                    ·
                      refine ⟨2566809688843945233560741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6844825836917187289495309 2566809688843945233560741)
                      ·
                        rfl

theorem cell23_4998844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4998844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998844 prefixEnd_4998844 := by exact prefixLift 4998844
  have htrace : WordTrace (prefixWord ++ tailWord_4998844) baseStart_4998844 baseEnd_4998844 := by
    simpa [prefixWord, tailWord_4998844, baseEnd_4998844] using wordTrace_append hprefix tailTrace_4998844
  have hstable : (prefixWord ++ tailWord_4998844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998844).length < 2 ^ (prefixWord ++ tailWord_4998844).sum := by decide
  have hdescent : baseEnd_4998844 < baseStart_4998844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998874 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_4998874 : Nat := 118140960795 + 4998874 * 2 ^ 59
def prefixEnd_4998874 : Nat := 4983230072969 + 3 ^ 40 * 4998874 * 2
def baseEnd_4998874 : Nat := 2566825093263580116185603

theorem tailTrace_4998874 : CollatzResearch.WordTrace tailWord_4998874 prefixEnd_4998874 2566825093263580116185603 := by
  unfold tailWord_4998874
  simp only [CollatzResearch.WordTrace]
  refine ⟨45580978322985178138654919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121549275527960475036413117 45580978322985178138654919)
  ·
    refine ⟨68371467484477767207982379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45580978322985178138654919 68371467484477767207982379)
    ·
      refine ⟨102557201226716650811973569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68371467484477767207982379 102557201226716650811973569)
      ·
        refine ⟨76917900920037488108980177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102557201226716650811973569 76917900920037488108980177)
        ·
          refine ⟨57688425690028116081735133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76917900920037488108980177 57688425690028116081735133)
          ·
            refine ⟨21633159633760543530650675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57688425690028116081735133 21633159633760543530650675)
            ·
              refine ⟨32449739450640815295976013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21633159633760543530650675 32449739450640815295976013)
              ·
                refine ⟨12168652293990305735991005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32449739450640815295976013 12168652293990305735991005)
                ·
                  refine ⟨4563244610246364650996627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12168652293990305735991005 4563244610246364650996627)
                  ·
                    refine ⟨6844866915369546976494941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4563244610246364650996627 6844866915369546976494941)
                    ·
                      refine ⟨2566825093263580116185603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6844866915369546976494941 2566825093263580116185603)
                      ·
                        rfl

theorem cell23_4998874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_4998874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998874 prefixEnd_4998874 := by exact prefixLift 4998874
  have htrace : WordTrace (prefixWord ++ tailWord_4998874) baseStart_4998874 baseEnd_4998874 := by
    simpa [prefixWord, tailWord_4998874, baseEnd_4998874] using wordTrace_append hprefix tailTrace_4998874
  have hstable : (prefixWord ++ tailWord_4998874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998874).length < 2 ^ (prefixWord ++ tailWord_4998874).sum := by decide
  have hdescent : baseEnd_4998874 < baseStart_4998874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998894 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_4998894 : Nat := 118140960795 + 4998894 * 2 ^ 59
def prefixEnd_4998894 : Nat := 4983230072969 + 3 ^ 40 * 4998894 * 2
def baseEnd_4998894 : Nat := 855611787625556679311837

theorem tailTrace_4998894 : CollatzResearch.WordTrace tailWord_4998894 prefixEnd_4998894 855611787625556679311837 := by
  unfold tailWord_4998894
  simp only [CollatzResearch.WordTrace]
  refine ⟨22790580343983531996293467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121549761834578837313565157 22790580343983531996293467)
  ·
    refine ⟨34185870515975297994440201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22790580343983531996293467 34185870515975297994440201)
    ·
      refine ⟨25639402886981473495830151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34185870515975297994440201 25639402886981473495830151)
      ·
        refine ⟨38459104330472210243745227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25639402886981473495830151 38459104330472210243745227)
        ·
          refine ⟨57688656495708315365617841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38459104330472210243745227 57688656495708315365617841)
          ·
            refine ⟨43266492371781236524213381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57688656495708315365617841 43266492371781236524213381)
            ·
              refine ⟨8112467319708981848290009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43266492371781236524213381 8112467319708981848290009)
              ·
                refine ⟨6084350489781736386217507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8112467319708981848290009 6084350489781736386217507)
                ·
                  refine ⟨9126525734672604579326261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6084350489781736386217507 9126525734672604579326261)
                  ·
                    refine ⟨855611787625556679311837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9126525734672604579326261 855611787625556679311837)
                    ·
                      rfl

theorem cell23_4998894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_4998894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998894 prefixEnd_4998894 := by exact prefixLift 4998894
  have htrace : WordTrace (prefixWord ++ tailWord_4998894) baseStart_4998894 baseEnd_4998894 := by
    simpa [prefixWord, tailWord_4998894, baseEnd_4998894] using wordTrace_append hprefix tailTrace_4998894
  have hstable : (prefixWord ++ tailWord_4998894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998894).length < 2 ^ (prefixWord ++ tailWord_4998894).sum := by decide
  have hdescent : baseEnd_4998894 < baseStart_4998894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998917 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_4998917 : Nat := 118140960795 + 4998917 * 2 ^ 59
def prefixEnd_4998917 : Nat := 4983230072969 + 3 ^ 40 * 4998917 * 2
def baseEnd_4998917 : Nat := 2566847172931723447947905

theorem tailTrace_4998917 : CollatzResearch.WordTrace tailWord_4998917 prefixEnd_4998917 2566847172931723447947905 := by
  unfold tailWord_4998917
  simp only [CollatzResearch.WordTrace]
  refine ⟨182325481630784930898435005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121550321087189953932290003 182325481630784930898435005)
  ·
    refine ⟨68372055611544349086913127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182325481630784930898435005 68372055611544349086913127)
    ·
      refine ⟨102558083417316523630369691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68372055611544349086913127 102558083417316523630369691)
      ·
        refine ⟨153837125125974785445554537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102558083417316523630369691 153837125125974785445554537)
        ·
          refine ⟨115377843844481089084165903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153837125125974785445554537 115377843844481089084165903)
          ·
            refine ⟨173066765766721633626248855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115377843844481089084165903 173066765766721633626248855)
            ·
              refine ⟨259600148650082450439373283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173066765766721633626248855 259600148650082450439373283)
              ·
                refine ⟨389400222975123675659059925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259600148650082450439373283 389400222975123675659059925)
                ·
                  refine ⟨9126567725979461148259217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 389400222975123675659059925 9126567725979461148259217)
                  ·
                    refine ⟨6844925794484595861194413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9126567725979461148259217 6844925794484595861194413)
                    ·
                      refine ⟨2566847172931723447947905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6844925794484595861194413 2566847172931723447947905)
                      ·
                        rfl

theorem cell23_4998917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_4998917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998917 prefixEnd_4998917 := by exact prefixLift 4998917
  have htrace : WordTrace (prefixWord ++ tailWord_4998917) baseStart_4998917 baseEnd_4998917 := by
    simpa [prefixWord, tailWord_4998917, baseEnd_4998917] using wordTrace_append hprefix tailTrace_4998917
  have hstable : (prefixWord ++ tailWord_4998917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998917).length < 2 ^ (prefixWord ++ tailWord_4998917).sum := by decide
  have hdescent : baseEnd_4998917 < baseStart_4998917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998932 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 6]
def baseStart_4998932 : Nat := 118140960795 + 4998932 * 2 ^ 59
def prefixEnd_4998932 : Nat := 4983230072969 + 3 ^ 40 * 4998932 * 2
def baseEnd_4998932 : Nat := 285206097237948987695593

theorem tailTrace_4998932 : CollatzResearch.WordTrace tailWord_4998932 prefixEnd_4998932 285206097237948987695593 := by
  unfold tailWord_4998932
  simp only [CollatzResearch.WordTrace]
  refine ⟨91163014362865294230115525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121550685817153725640154033 91163014362865294230115525)
  ·
    refine ⟨17093065193037242668146661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91163014362865294230115525 17093065193037242668146661)
    ·
      refine ⟨3204949723694483000277499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17093065193037242668146661 3204949723694483000277499)
      ·
        refine ⟨4807424585541724500416249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204949723694483000277499 4807424585541724500416249)
        ·
          refine ⟨3605568439156293375312187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4807424585541724500416249 3605568439156293375312187)
          ·
            refine ⟨5408352658734440062968281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3605568439156293375312187 5408352658734440062968281)
            ·
              refine ⟨4056264494050830047226211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5408352658734440062968281 4056264494050830047226211)
              ·
                refine ⟨6084396741076245070839317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056264494050830047226211 6084396741076245070839317)
                ·
                  refine ⟨285206097237948987695593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6084396741076245070839317 285206097237948987695593)
                  ·
                    rfl

theorem cell23_4998932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_4998932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998932 prefixEnd_4998932 := by exact prefixLift 4998932
  have htrace : WordTrace (prefixWord ++ tailWord_4998932) baseStart_4998932 baseEnd_4998932 := by
    simpa [prefixWord, tailWord_4998932, baseEnd_4998932] using wordTrace_append hprefix tailTrace_4998932
  have hstable : (prefixWord ++ tailWord_4998932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998932).length < 2 ^ (prefixWord ++ tailWord_4998932).sum := by decide
  have hdescent : baseEnd_4998932 < baseStart_4998932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998981 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_4998981 : Nat := 118140960795 + 4998981 * 2 ^ 59
def prefixEnd_4998981 : Nat := 4983230072969 + 3 ^ 40 * 4998981 * 2
def baseEnd_4998981 : Nat := 2566880035693611197547611

theorem tailTrace_4998981 : CollatzResearch.WordTrace tailWord_4998981 prefixEnd_4998981 2566880035693611197547611 := by
  unfold tailWord_4998981
  simp only [CollatzResearch.WordTrace]
  refine ⟨182327815902553069828764797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121551877268368713219176531 182327815902553069828764797)
  ·
    refine ⟨68372930963457401185786799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182327815902553069828764797 68372930963457401185786799)
    ·
      refine ⟨102559396445186101778680199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68372930963457401185786799 102559396445186101778680199)
      ·
        refine ⟨153839094667779152668020299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102559396445186101778680199 153839094667779152668020299)
        ·
          refine ⟨230758642001668729002030449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153839094667779152668020299 230758642001668729002030449)
          ·
            refine ⟨173068981501251546751522837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230758642001668729002030449 173068981501251546751522837)
            ·
              refine ⟨8112608507871166253977633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173068981501251546751522837 8112608507871166253977633)
              ·
                refine ⟨6084456380903374690483225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8112608507871166253977633 6084456380903374690483225)
                ·
                  refine ⟨4563342285677531017862419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6084456380903374690483225 4563342285677531017862419)
                  ·
                    refine ⟨6845013428516296526793629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4563342285677531017862419 6845013428516296526793629)
                    ·
                      refine ⟨2566880035693611197547611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6845013428516296526793629 2566880035693611197547611)
                      ·
                        rfl

theorem cell23_4998981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_4998981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998981 prefixEnd_4998981 := by exact prefixLift 4998981
  have htrace : WordTrace (prefixWord ++ tailWord_4998981) baseStart_4998981 baseEnd_4998981 := by
    simpa [prefixWord, tailWord_4998981, baseEnd_4998981] using wordTrace_append hprefix tailTrace_4998981
  have hstable : (prefixWord ++ tailWord_4998981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998981).length < 2 ^ (prefixWord ++ tailWord_4998981).sum := by decide
  have hdescent : baseEnd_4998981 < baseStart_4998981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4998997 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_4998997 : Nat := 118140960795 + 4998997 * 2 ^ 59
def prefixEnd_4998997 : Nat := 4983230072969 + 3 ^ 40 * 4998997 * 2
def baseEnd_4998997 : Nat := 855629417128027711649179

theorem tailTrace_4998997 : CollatzResearch.WordTrace tailWord_4998997 prefixEnd_4998997 855629417128027711649179 := by
  unfold tailWord_4998997
  simp only [CollatzResearch.WordTrace]
  refine ⟨182328399470495104561347245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121552266313663403040898163 182328399470495104561347245)
  ·
    refine ⟨68373149801435664210505217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182328399470495104561347245 68373149801435664210505217)
    ·
      refine ⟨51279862351076748157878913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68373149801435664210505217 51279862351076748157878913)
      ·
        refine ⟨38459896763307561118409185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51279862351076748157878913 38459896763307561118409185)
        ·
          refine ⟨28844922572480670838806889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38459896763307561118409185 28844922572480670838806889)
          ·
            refine ⟨21633691929360503129105167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28844922572480670838806889 21633691929360503129105167)
            ·
              refine ⟨32450537894040754693657751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21633691929360503129105167 32450537894040754693657751)
              ·
                refine ⟨48675806841061132040486627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32450537894040754693657751 48675806841061132040486627)
                ·
                  refine ⟨73013710261591698060729941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48675806841061132040486627 73013710261591698060729941)
                  ·
                    refine ⟨855629417128027711649179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73013710261591698060729941 855629417128027711649179)
                    ·
                      rfl

theorem cell23_4998997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_4998997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4998997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4998997 prefixEnd_4998997 := by exact prefixLift 4998997
  have htrace : WordTrace (prefixWord ++ tailWord_4998997) baseStart_4998997 baseEnd_4998997 := by
    simpa [prefixWord, tailWord_4998997, baseEnd_4998997] using wordTrace_append hprefix tailTrace_4998997
  have hstable : (prefixWord ++ tailWord_4998997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4998997).length < 2 ^ (prefixWord ++ tailWord_4998997).sum := by decide
  have hdescent : baseEnd_4998997 < baseStart_4998997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4998997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999021 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_4999021 : Nat := 118140960795 + 4999021 * 2 ^ 59
def prefixEnd_4999021 : Nat := 4983230072969 + 3 ^ 40 * 4999021 * 2
def baseEnd_4999021 : Nat := 2566900574919791041047427

theorem tailTrace_4999021 : CollatzResearch.WordTrace tailWord_4999021 prefixEnd_4999021 2566900574919791041047427 := by
  unfold tailWord_4999021
  simp only [CollatzResearch.WordTrace]
  refine ⟨182329274822408156660220917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121552849881605437773480611 182329274822408156660220917)
  ·
    refine ⟨17093369514600764686895711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182329274822408156660220917 17093369514600764686895711)
    ·
      refine ⟨25640054271901147030343567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17093369514600764686895711 25640054271901147030343567)
      ·
        refine ⟨38460081407851720545515351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25640054271901147030343567 38460081407851720545515351)
        ·
          refine ⟨57690122111777580818273027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38460081407851720545515351 57690122111777580818273027)
          ·
            refine ⟨86535183167666371227409541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57690122111777580818273027 86535183167666371227409541)
            ·
              refine ⟨16225346843937444605139289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86535183167666371227409541 16225346843937444605139289)
              ·
                refine ⟨12169010132953083453854467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16225346843937444605139289 12169010132953083453854467)
                ·
                  refine ⟨18253515199429625180781701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12169010132953083453854467 18253515199429625180781701)
                  ·
                    refine ⟨3422534099893054721396569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18253515199429625180781701 3422534099893054721396569)
                    ·
                      refine ⟨2566900574919791041047427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422534099893054721396569 2566900574919791041047427)
                      ·
                        rfl

theorem cell23_4999021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_4999021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999021 prefixEnd_4999021 := by exact prefixLift 4999021
  have htrace : WordTrace (prefixWord ++ tailWord_4999021) baseStart_4999021 baseEnd_4999021 := by
    simpa [prefixWord, tailWord_4999021, baseEnd_4999021] using wordTrace_append hprefix tailTrace_4999021
  have hstable : (prefixWord ++ tailWord_4999021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999021).length < 2 ^ (prefixWord ++ tailWord_4999021).sum := by decide
  have hdescent : baseEnd_4999021 < baseStart_4999021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999057 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 1, 7]
def baseStart_4999057 : Nat := 118140960795 + 4999057 * 2 ^ 59
def prefixEnd_4999057 : Nat := 4983230072969 + 3 ^ 40 * 4999057 * 2
def baseEnd_4999057 : Nat := 855639686741117633399087

theorem tailTrace_4999057 : CollatzResearch.WordTrace tailWord_4999057 prefixEnd_4999057 855639686741117633399087 := by
  unfold tailWord_4999057
  simp only [CollatzResearch.WordTrace]
  refine ⟨182330587850277734808531425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121553725233518489872354283 182330587850277734808531425)
  ·
    refine ⟨136747940887708301106398569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182330587850277734808531425 136747940887708301106398569)
    ·
      refine ⟨102560955665781225829798927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136747940887708301106398569 102560955665781225829798927)
      ·
        refine ⟨153841433498671838744698391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102560955665781225829798927 153841433498671838744698391)
        ·
          refine ⟨230762150248007758117047587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153841433498671838744698391 230762150248007758117047587)
          ·
            refine ⟨346143225372011637175571381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230762150248007758117047587 346143225372011637175571381)
            ·
              refine ⟨32450927378626090985209817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 346143225372011637175571381 32450927378626090985209817)
              ·
                refine ⟨24338195533969568238907363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32450927378626090985209817 24338195533969568238907363)
                ·
                  refine ⟨36507293300954352358361045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24338195533969568238907363 36507293300954352358361045)
                  ·
                    refine ⟨855639686741117633399087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36507293300954352358361045 855639686741117633399087)
                    ·
                      rfl

theorem cell23_4999057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_4999057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999057 prefixEnd_4999057 := by exact prefixLift 4999057
  have htrace : WordTrace (prefixWord ++ tailWord_4999057) baseStart_4999057 baseEnd_4999057 := by
    simpa [prefixWord, tailWord_4999057, baseEnd_4999057] using wordTrace_append hprefix tailTrace_4999057
  have hstable : (prefixWord ++ tailWord_4999057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999057).length < 2 ^ (prefixWord ++ tailWord_4999057).sum := by decide
  have hdescent : baseEnd_4999057 < baseStart_4999057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999114 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_4999114 : Nat := 118140960795 + 4999114 * 2 ^ 59
def prefixEnd_4999114 : Nat := 4983230072969 + 3 ^ 40 * 4999114 * 2
def baseEnd_4999114 : Nat := 2566948328620659177184499

theorem tailTrace_4999114 : CollatzResearch.WordTrace tailWord_4999114 prefixEnd_4999114 2566948328620659177184499 := by
  unfold tailWord_4999114
  simp only [CollatzResearch.WordTrace]
  refine ⟨45583166702767808385839099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121555111207380822362237597 45583166702767808385839099)
  ·
    refine ⟨68374750054151712578758649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45583166702767808385839099 68374750054151712578758649)
    ·
      refine ⟨51281062540613784434068987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68374750054151712578758649 51281062540613784434068987)
      ·
        refine ⟨76921593810920676651103481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51281062540613784434068987 76921593810920676651103481)
        ·
          refine ⟨57691195358190507488327611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76921593810920676651103481 57691195358190507488327611)
          ·
            refine ⟨86536793037285761232491417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57691195358190507488327611 86536793037285761232491417)
            ·
              refine ⟨64902594777964320924368563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86536793037285761232491417 64902594777964320924368563)
              ·
                refine ⟨97353892166946481386552845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64902594777964320924368563 97353892166946481386552845)
                ·
                  refine ⟨36507709562604930519957317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97353892166946481386552845 36507709562604930519957317)
                  ·
                    refine ⟨6845195542988424472491997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36507709562604930519957317 6845195542988424472491997)
                    ·
                      refine ⟨2566948328620659177184499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6845195542988424472491997 2566948328620659177184499)
                      ·
                        rfl

theorem cell23_4999114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_4999114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999114 prefixEnd_4999114 := by exact prefixLift 4999114
  have htrace : WordTrace (prefixWord ++ tailWord_4999114) baseStart_4999114 baseEnd_4999114 := by
    simpa [prefixWord, tailWord_4999114, baseEnd_4999114] using wordTrace_append hprefix tailTrace_4999114
  have hstable : (prefixWord ++ tailWord_4999114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999114).length < 2 ^ (prefixWord ++ tailWord_4999114).sum := by decide
  have hdescent : baseEnd_4999114 < baseStart_4999114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999164 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_4999164 : Nat := 118140960795 + 4999164 * 2 ^ 59
def prefixEnd_4999164 : Nat := 4983230072969 + 3 ^ 40 * 4999164 * 2
def baseEnd_4999164 : Nat := 855658000884461327186423

theorem tailTrace_4999164 : CollatzResearch.WordTrace tailWord_4999164 prefixEnd_4999164 855658000884461327186423 := by
  unfold tailWord_4999164
  simp only [CollatzResearch.WordTrace]
  refine ⟨91167245230445046041338273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121556326973926728055117697 91167245230445046041338273)
  ·
    refine ⟨68375433922833784531003705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91167245230445046041338273 68375433922833784531003705)
    ·
      refine ⟨51281575442125338398252779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68375433922833784531003705 51281575442125338398252779)
      ·
        refine ⟨76922363163188007597379169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51281575442125338398252779 76922363163188007597379169)
        ·
          refine ⟨57691772372391005698034377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76922363163188007597379169 57691772372391005698034377)
          ·
            refine ⟨43268829279293254273525783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57691772372391005698034377 43268829279293254273525783)
            ·
              refine ⟨64903243918939881410288675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43268829279293254273525783 64903243918939881410288675)
              ·
                refine ⟨97354865878409822115433013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64903243918939881410288675 97354865878409822115433013)
                ·
                  refine ⟨9127018676100920823321845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97354865878409822115433013 9127018676100920823321845)
                  ·
                    refine ⟨855658000884461327186423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9127018676100920823321845 855658000884461327186423)
                    ·
                      rfl

theorem cell23_4999164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_4999164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999164 prefixEnd_4999164 := by exact prefixLift 4999164
  have htrace : WordTrace (prefixWord ++ tailWord_4999164) baseStart_4999164 baseEnd_4999164 := by
    simpa [prefixWord, tailWord_4999164, baseEnd_4999164] using wordTrace_append hprefix tailTrace_4999164
  have hstable : (prefixWord ++ tailWord_4999164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999164).length < 2 ^ (prefixWord ++ tailWord_4999164).sum := by decide
  have hdescent : baseEnd_4999164 < baseStart_4999164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999171 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 4, 3, 2]
def baseStart_4999171 : Nat := 118140960795 + 4999171 * 2 ^ 59
def prefixEnd_4999171 : Nat := 4983230072969 + 3 ^ 40 * 4999171 * 2
def baseEnd_4999171 : Nat := 2566977597017965454171737

theorem tailTrace_4999171 : CollatzResearch.WordTrace tailWord_4999171 prefixEnd_4999171 2566977597017965454171737 := by
  unfold tailWord_4999171
  simp only [CollatzResearch.WordTrace]
  refine ⟨182334745771864732278181367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121556497181243154852120911 182334745771864732278181367)
  ·
    refine ⟨273502118657797098417272051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182334745771864732278181367 273502118657797098417272051)
    ·
      refine ⟨410253177986695647625908077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273502118657797098417272051 410253177986695647625908077)
      ·
        refine ⟨153844941745010867859715529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410253177986695647625908077 153844941745010867859715529)
        ·
          refine ⟨115383706308758150894786647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153844941745010867859715529 115383706308758150894786647)
          ·
            refine ⟨173075559463137226342179971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115383706308758150894786647 173075559463137226342179971)
            ·
              refine ⟨259613339194705839513269957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173075559463137226342179971 259613339194705839513269957)
              ·
                refine ⟨48677501099007344908738117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 259613339194705839513269957 48677501099007344908738117)
                ·
                  refine ⟨9127031456063877170388397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48677501099007344908738117 9127031456063877170388397)
                  ·
                    refine ⟨3422636796023953938895649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9127031456063877170388397 3422636796023953938895649)
                    ·
                      refine ⟨2566977597017965454171737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422636796023953938895649 2566977597017965454171737)
                      ·
                        rfl

theorem cell23_4999171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_4999171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999171 prefixEnd_4999171 := by exact prefixLift 4999171
  have htrace : WordTrace (prefixWord ++ tailWord_4999171) baseStart_4999171 baseEnd_4999171 := by
    simpa [prefixWord, tailWord_4999171, baseEnd_4999171] using wordTrace_append hprefix tailTrace_4999171
  have hstable : (prefixWord ++ tailWord_4999171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999171).length < 2 ^ (prefixWord ++ tailWord_4999171).sum := by decide
  have hdescent : baseEnd_4999171 < baseStart_4999171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999211 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 2, 4]
def baseStart_4999211 : Nat := 118140960795 + 4999211 * 2 ^ 59
def prefixEnd_4999211 : Nat := 4983230072969 + 3 ^ 40 * 4999211 * 2
def baseEnd_4999211 : Nat := 855666045414715099223851

theorem tailTrace_4999211 : CollatzResearch.WordTrace tailWord_4999211 prefixEnd_4999211 855666045414715099223851 := by
  unfold tailWord_4999211
  simp only [CollatzResearch.WordTrace]
  refine ⟨182336204691719819109637487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121557469794479879406424991 182336204691719819109637487)
  ·
    refine ⟨273504307037579728664456231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182336204691719819109637487 273504307037579728664456231)
    ·
      refine ⟨410256460556369592996684347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273504307037579728664456231 410256460556369592996684347)
      ·
        refine ⟨615384690834554389495026521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410256460556369592996684347 615384690834554389495026521)
        ·
          refine ⟨461538518125915792121269891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615384690834554389495026521 461538518125915792121269891)
          ·
            refine ⟨692307777188873688181904837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461538518125915792121269891 692307777188873688181904837)
            ·
              refine ⟨129807708222913816534107157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 692307777188873688181904837 129807708222913816534107157)
              ·
                refine ⟨6084736322949085150036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129807708222913816534107157 6084736322949085150036273)
                ·
                  refine ⟨4563552242211813862527205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6084736322949085150036273 4563552242211813862527205)
                  ·
                    refine ⟨855666045414715099223851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4563552242211813862527205 855666045414715099223851)
                    ·
                      rfl

theorem cell23_4999211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 2, 4].length) (baseStart_4999211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999211 prefixEnd_4999211 := by exact prefixLift 4999211
  have htrace : WordTrace (prefixWord ++ tailWord_4999211) baseStart_4999211 baseEnd_4999211 := by
    simpa [prefixWord, tailWord_4999211, baseEnd_4999211] using wordTrace_append hprefix tailTrace_4999211
  have hstable : (prefixWord ++ tailWord_4999211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999211).length < 2 ^ (prefixWord ++ tailWord_4999211).sum := by decide
  have hdescent : baseEnd_4999211 < baseStart_4999211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999221 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_4999221 : Nat := 118140960795 + 4999221 * 2 ^ 59
def prefixEnd_4999221 : Nat := 4983230072969 + 3 ^ 40 * 4999221 * 2
def baseEnd_4999221 : Nat := 2567003271050690258546507

theorem tailTrace_4999221 : CollatzResearch.WordTrace tailWord_4999221 prefixEnd_4999221 2567003271050690258546507 := by
  unfold tailWord_4999221
  simp only [CollatzResearch.WordTrace]
  refine ⟨182336569421683590817501517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121557712947789060545001011 182336569421683590817501517)
  ·
    refine ⟨68376213533131346556563069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182336569421683590817501517 68376213533131346556563069)
    ·
      refine ⟨25641080074924254958711151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68376213533131346556563069 25641080074924254958711151)
      ·
        refine ⟨38461620112386382438066727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25641080074924254958711151 38461620112386382438066727)
        ·
          refine ⟨57692430168579573657100091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38461620112386382438066727 57692430168579573657100091)
          ·
            refine ⟨86538645252869360485650137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57692430168579573657100091 86538645252869360485650137)
            ·
              refine ⟨64903983939652020364237603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86538645252869360485650137 64903983939652020364237603)
              ·
                refine ⟨97355975909478030546356405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64903983939652020364237603 97355975909478030546356405)
                ·
                  refine ⟨9127122741513565363720913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97355975909478030546356405 9127122741513565363720913)
                  ·
                    refine ⟨6845342056135174022790685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9127122741513565363720913 6845342056135174022790685)
                    ·
                      refine ⟨2567003271050690258546507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6845342056135174022790685 2567003271050690258546507)
                      ·
                        rfl

theorem cell23_4999221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_4999221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999221 prefixEnd_4999221 := by exact prefixLift 4999221
  have htrace : WordTrace (prefixWord ++ tailWord_4999221) baseStart_4999221 baseEnd_4999221 := by
    simpa [prefixWord, tailWord_4999221, baseEnd_4999221] using wordTrace_append hprefix tailTrace_4999221
  have hstable : (prefixWord ++ tailWord_4999221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999221).length < 2 ^ (prefixWord ++ tailWord_4999221).sum := by decide
  have hdescent : baseEnd_4999221 < baseStart_4999221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999231 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 4]
def baseStart_4999231 : Nat := 118140960795 + 4999231 * 2 ^ 59
def prefixEnd_4999231 : Nat := 4983230072969 + 3 ^ 40 * 4999231 * 2
def baseEnd_4999231 : Nat := 2567008405857235219421461

theorem tailTrace_4999231 : CollatzResearch.WordTrace tailWord_4999231 prefixEnd_4999231 2567008405857235219421461 := by
  unfold tailWord_4999231
  simp only [CollatzResearch.WordTrace]
  refine ⟨182336934151647362525365547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121557956101098241683577031 182336934151647362525365547)
  ·
    refine ⟨273505401227471043788048321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182336934151647362525365547 273505401227471043788048321)
    ·
      refine ⟨205129050920603282841036241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273505401227471043788048321 205129050920603282841036241)
      ·
        refine ⟨153846788190452462130777181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205129050920603282841036241 153846788190452462130777181)
        ·
          refine ⟨57692545571419673299041443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153846788190452462130777181 57692545571419673299041443)
          ·
            refine ⟨86538818357129509948562165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57692545571419673299041443 86538818357129509948562165)
            ·
              refine ⟨8113014220980891557677703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86538818357129509948562165 8113014220980891557677703)
              ·
                refine ⟨12169521331471337336516555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8113014220980891557677703 12169521331471337336516555)
                ·
                  refine ⟨18254281997207006004774833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12169521331471337336516555 18254281997207006004774833)
                  ·
                    refine ⟨13690711497905254503581125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18254281997207006004774833 13690711497905254503581125)
                    ·
                      refine ⟨2567008405857235219421461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13690711497905254503581125 2567008405857235219421461)
                      ·
                        rfl

theorem cell23_4999231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_4999231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999231 prefixEnd_4999231 := by exact prefixLift 4999231
  have htrace : WordTrace (prefixWord ++ tailWord_4999231) baseStart_4999231 baseEnd_4999231 := by
    simpa [prefixWord, tailWord_4999231, baseEnd_4999231] using wordTrace_append hprefix tailTrace_4999231
  have hstable : (prefixWord ++ tailWord_4999231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999231).length < 2 ^ (prefixWord ++ tailWord_4999231).sum := by decide
  have hdescent : baseEnd_4999231 < baseStart_4999231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999238 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4999238 : Nat := 118140960795 + 4999238 * 2 ^ 59
def prefixEnd_4999238 : Nat := 4983230072969 + 3 ^ 40 * 4999238 * 2
def baseEnd_4999238 : Nat := 2567012000221816692033929

theorem tailTrace_4999238 : CollatzResearch.WordTrace tailWord_4999238 prefixEnd_4999238 2567012000221816692033929 := by
  unfold tailWord_4999238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698037170706937585027199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121558126308414668480580245 5698037170706937585027199)
  ·
    refine ⟨8547055756060406377540799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5698037170706937585027199 8547055756060406377540799)
    ·
      refine ⟨12820583634090609566311199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8547055756060406377540799 12820583634090609566311199)
      ·
        refine ⟨19230875451135914349466799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12820583634090609566311199 19230875451135914349466799)
        ·
          refine ⟨28846313176703871524200199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19230875451135914349466799 28846313176703871524200199)
          ·
            refine ⟨43269469765055807286300299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28846313176703871524200199 43269469765055807286300299)
            ·
              refine ⟨64904204647583710929450449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43269469765055807286300299 64904204647583710929450449)
              ·
                refine ⟨48678153485687783197087837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64904204647583710929450449 48678153485687783197087837)
                ·
                  refine ⟨18254307557132918698907939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48678153485687783197087837 18254307557132918698907939)
                  ·
                    refine ⟨27381461335699378048361909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18254307557132918698907939 27381461335699378048361909)
                    ·
                      refine ⟨2567012000221816692033929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27381461335699378048361909 2567012000221816692033929)
                      ·
                        rfl

theorem cell23_4999238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4999238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999238 prefixEnd_4999238 := by exact prefixLift 4999238
  have htrace : WordTrace (prefixWord ++ tailWord_4999238) baseStart_4999238 baseEnd_4999238 := by
    simpa [prefixWord, tailWord_4999238, baseEnd_4999238] using wordTrace_append hprefix tailTrace_4999238
  have hstable : (prefixWord ++ tailWord_4999238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999238).length < 2 ^ (prefixWord ++ tailWord_4999238).sum := by decide
  have hdescent : baseEnd_4999238 < baseStart_4999238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999268 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_4999268 : Nat := 118140960795 + 4999268 * 2 ^ 59
def prefixEnd_4999268 : Nat := 4983230072969 + 3 ^ 40 * 4999268 * 2
def baseEnd_4999268 : Nat := 2567027404641451574658791

theorem tailTrace_4999268 : CollatzResearch.WordTrace tailWord_4999268 prefixEnd_4999268 2567027404641451574658791 := by
  unfold tailWord_4999268
  simp only [CollatzResearch.WordTrace]
  refine ⟨91169141826256658922231229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121558855768342211896308305 91169141826256658922231229)
  ·
    refine ⟨34188428184846247095836711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91169141826256658922231229 34188428184846247095836711)
    ·
      refine ⟨51282642277269370643755067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34188428184846247095836711 51282642277269370643755067)
      ·
        refine ⟨76923963415904055965632601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51282642277269370643755067 76923963415904055965632601)
        ·
          refine ⟨57692972561928041974224451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76923963415904055965632601 57692972561928041974224451)
          ·
            refine ⟨86539458842892062961336677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57692972561928041974224451 86539458842892062961336677)
            ·
              refine ⟨16226148533042261805250627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86539458842892062961336677 16226148533042261805250627)
              ·
                refine ⟨24339222799563392707875941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16226148533042261805250627 24339222799563392707875941)
                ·
                  refine ⟨4563604274918136132726739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24339222799563392707875941 4563604274918136132726739)
                  ·
                    refine ⟨6845406412377204199090109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4563604274918136132726739 6845406412377204199090109)
                    ·
                      refine ⟨2567027404641451574658791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6845406412377204199090109 2567027404641451574658791)
                      ·
                        rfl

theorem cell23_4999268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_4999268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999268 prefixEnd_4999268 := by exact prefixLift 4999268
  have htrace : WordTrace (prefixWord ++ tailWord_4999268) baseStart_4999268 baseEnd_4999268 := by
    simpa [prefixWord, tailWord_4999268, baseEnd_4999268] using wordTrace_append hprefix tailTrace_4999268
  have hstable : (prefixWord ++ tailWord_4999268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999268).length < 2 ^ (prefixWord ++ tailWord_4999268).sum := by decide
  have hdescent : baseEnd_4999268 < baseStart_4999268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999269 : List Nat := [1, 3, 1, 3, 2, 3, 3, 2, 1, 2, 2]
def baseStart_4999269 : Nat := 118140960795 + 4999269 * 2 ^ 59
def prefixEnd_4999269 : Nat := 4983230072969 + 3 ^ 40 * 4999269 * 2
def baseEnd_4999269 : Nat := 2567027918122106070746287

theorem tailTrace_4999269 : CollatzResearch.WordTrace tailWord_4999269 prefixEnd_4999269 2567027918122106070746287 := by
  unfold tailWord_4999269
  simp only [CollatzResearch.WordTrace]
  refine ⟨182338320125509695015248861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121558880083673130010165907 182338320125509695015248861)
  ·
    refine ⟨68376870047066135630718323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182338320125509695015248861 68376870047066135630718323)
    ·
      refine ⟨102565305070599203446077485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68376870047066135630718323 102565305070599203446077485)
      ·
        refine ⟨38461989401474701292279057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102565305070599203446077485 38461989401474701292279057)
        ·
          refine ⟨28846492051106025969209293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38461989401474701292279057 28846492051106025969209293)
          ·
            refine ⟨10817434519164759738453485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28846492051106025969209293 10817434519164759738453485)
            ·
              refine ⟨4056537944686784901920057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10817434519164759738453485 4056537944686784901920057)
              ·
                refine ⟨3042403458515088676440043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4056537944686784901920057 3042403458515088676440043)
                ·
                  refine ⟨4563605187772633014660065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3042403458515088676440043 4563605187772633014660065)
                  ·
                    refine ⟨3422703890829474760995049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4563605187772633014660065 3422703890829474760995049)
                    ·
                      refine ⟨2567027918122106070746287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422703890829474760995049 2567027918122106070746287)
                      ·
                        rfl

theorem cell23_4999269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_4999269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999269 prefixEnd_4999269 := by exact prefixLift 4999269
  have htrace : WordTrace (prefixWord ++ tailWord_4999269) baseStart_4999269 baseEnd_4999269 := by
    simpa [prefixWord, tailWord_4999269, baseEnd_4999269] using wordTrace_append hprefix tailTrace_4999269
  have hstable : (prefixWord ++ tailWord_4999269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999269).length < 2 ^ (prefixWord ++ tailWord_4999269).sum := by decide
  have hdescent : baseEnd_4999269 < baseStart_4999269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999382 : List Nat := [5, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_4999382 : Nat := 118140960795 + 4999382 * 2 ^ 59
def prefixEnd_4999382 : Nat := 4983230072969 + 3 ^ 40 * 4999382 * 2
def baseEnd_4999382 : Nat := 285231771270673792070363

theorem tailTrace_4999382 : CollatzResearch.WordTrace tailWord_4999382 prefixEnd_4999382 285231771270673792070363 := by
  unfold tailWord_4999382
  simp only [CollatzResearch.WordTrace]
  refine ⟨11396402598381269707132025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121561627716066876876074933 11396402598381269707132025)
  ·
    refine ⟨8547301948785952280349019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11396402598381269707132025 8547301948785952280349019)
    ·
      refine ⟨12820952923178928420523529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8547301948785952280349019 12820952923178928420523529)
      ·
        refine ⟨9615714692384196315392647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12820952923178928420523529 9615714692384196315392647)
        ·
          refine ⟨14423572038576294473088971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9615714692384196315392647 14423572038576294473088971)
          ·
            refine ⟨21635358057864441709633457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14423572038576294473088971 21635358057864441709633457)
            ·
              refine ⟨16226518543398331282225093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21635358057864441709633457 16226518543398331282225093)
              ·
                refine ⟨3042472226887187115417205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16226518543398331282225093 3042472226887187115417205)
                ·
                  refine ⟨285231771270673792070363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3042472226887187115417205 285231771270673792070363)
                  ·
                    rfl

theorem cell23_4999382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_4999382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999382 prefixEnd_4999382 := by exact prefixLift 4999382
  have htrace : WordTrace (prefixWord ++ tailWord_4999382) baseStart_4999382 baseEnd_4999382 := by
    simpa [prefixWord, tailWord_4999382, baseEnd_4999382] using wordTrace_append hprefix tailTrace_4999382
  have hstable : (prefixWord ++ tailWord_4999382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999382).length < 2 ^ (prefixWord ++ tailWord_4999382).sum := by decide
  have hdescent : baseEnd_4999382 < baseStart_4999382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999411 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4]
def baseStart_4999411 : Nat := 118140960795 + 4999411 * 2 ^ 59
def prefixEnd_4999411 : Nat := 4983230072969 + 3 ^ 40 * 4999411 * 2
def baseEnd_4999411 : Nat := 2567100832375044515170633

theorem tailTrace_4999411 : CollatzResearch.WordTrace tailWord_4999411 prefixEnd_4999411 2567100832375044515170633 := by
  unfold tailWord_4999411
  simp only [CollatzResearch.WordTrace]
  refine ⟨182343499290995253266918087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121562332860663502177945391 182343499290995253266918087)
  ·
    refine ⟨273515248936492879900377131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182343499290995253266918087 273515248936492879900377131)
    ·
      refine ⟨410272873404739319850565697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273515248936492879900377131 410272873404739319850565697)
      ·
        refine ⟨307704655053554489887924273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410272873404739319850565697 307704655053554489887924273)
        ·
          refine ⟨230778491290165867415943205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307704655053554489887924273 230778491290165867415943205)
          ·
            refine ⟨43270967116906100140489351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 230778491290165867415943205 43270967116906100140489351)
            ·
              refine ⟨64906450675359150210734027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43270967116906100140489351 64906450675359150210734027)
              ·
                refine ⟨97359676013038725316101041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64906450675359150210734027 97359676013038725316101041)
                ·
                  refine ⟨73019757009779043987075781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97359676013038725316101041 73019757009779043987075781)
                  ·
                    refine ⟨13691204439333570747576709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73019757009779043987075781 13691204439333570747576709)
                    ·
                      refine ⟨2567100832375044515170633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13691204439333570747576709 2567100832375044515170633)
                      ·
                        rfl

theorem cell23_4999411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_4999411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999411 prefixEnd_4999411 := by exact prefixLift 4999411
  have htrace : WordTrace (prefixWord ++ tailWord_4999411) baseStart_4999411 baseEnd_4999411 := by
    simpa [prefixWord, tailWord_4999411, baseEnd_4999411] using wordTrace_append hprefix tailTrace_4999411
  have hstable : (prefixWord ++ tailWord_4999411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999411).length < 2 ^ (prefixWord ++ tailWord_4999411).sum := by decide
  have hdescent : baseEnd_4999411 < baseStart_4999411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999418 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_4999418 : Nat := 118140960795 + 4999418 * 2 ^ 59
def prefixEnd_4999418 : Nat := 4983230072969 + 3 ^ 40 * 4999418 * 2
def baseEnd_4999418 : Nat := 2567104426739625987783101

theorem tailTrace_4999418 : CollatzResearch.WordTrace tailWord_4999418 prefixEnd_4999418 2567104426739625987783101 := by
  unfold tailWord_4999418
  simp only [CollatzResearch.WordTrace]
  refine ⟨45585938650492473365605727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121562503067979928974948605 45585938650492473365605727)
  ·
    refine ⟨68378907975738710048408591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45585938650492473365605727 68378907975738710048408591)
    ·
      refine ⟨102568361963608065072612887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68378907975738710048408591 102568361963608065072612887)
      ·
        refine ⟨153852542945412097608919331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102568361963608065072612887 153852542945412097608919331)
        ·
          refine ⟨230778814418118146413378997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153852542945412097608919331 230778814418118146413378997)
          ·
            refine ⟨21635513851698576226254281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230778814418118146413378997 21635513851698576226254281)
            ·
              refine ⟨16226635388773932169690711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21635513851698576226254281 16226635388773932169690711)
              ·
                refine ⟨24339953083160898254536067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16226635388773932169690711 24339953083160898254536067)
                ·
                  refine ⟨36509929624741347381804101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24339953083160898254536067 36509929624741347381804101)
                  ·
                    refine ⟨6845611804639002634088269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36509929624741347381804101 6845611804639002634088269)
                    ·
                      refine ⟨2567104426739625987783101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6845611804639002634088269 2567104426739625987783101)
                      ·
                        rfl

theorem cell23_4999418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_4999418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999418 prefixEnd_4999418 := by exact prefixLift 4999418
  have htrace : WordTrace (prefixWord ++ tailWord_4999418) baseStart_4999418 baseEnd_4999418 := by
    simpa [prefixWord, tailWord_4999418, baseEnd_4999418] using wordTrace_append hprefix tailTrace_4999418
  have hstable : (prefixWord ++ tailWord_4999418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999418).length < 2 ^ (prefixWord ++ tailWord_4999418).sum := by decide
  have hdescent : baseEnd_4999418 < baseStart_4999418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999438 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_4999438 : Nat := 118140960795 + 4999438 * 2 ^ 59
def prefixEnd_4999438 : Nat := 4983230072969 + 3 ^ 40 * 4999438 * 2
def baseEnd_4999438 : Nat := 285234966261412878837001

theorem tailTrace_4999438 : CollatzResearch.WordTrace tailWord_4999438 prefixEnd_4999438 285234966261412878837001 := by
  unfold tailWord_4999438
  simp only [CollatzResearch.WordTrace]
  refine ⟨22793060507737179609768871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121562989374598291252100645 22793060507737179609768871)
  ·
    refine ⟨34189590761605769414653307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22793060507737179609768871 34189590761605769414653307)
    ·
      refine ⟨51284386142408654121979961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34189590761605769414653307 51284386142408654121979961)
      ·
        refine ⟨38463289606806490591484971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51284386142408654121979961 38463289606806490591484971)
        ·
          refine ⟨57694934410209735887227457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38463289606806490591484971 57694934410209735887227457)
          ·
            refine ⟨43271200807657301915420593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57694934410209735887227457 43271200807657301915420593)
            ·
              refine ⟨32453400605742976436565445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43271200807657301915420593 32453400605742976436565445)
              ·
                refine ⟨6085012613576808081856021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32453400605742976436565445 6085012613576808081856021)
                ·
                  refine ⟨285234966261412878837001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6085012613576808081856021 285234966261412878837001)
                  ·
                    rfl

theorem cell23_4999438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_4999438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999438 prefixEnd_4999438 := by exact prefixLift 4999438
  have htrace : WordTrace (prefixWord ++ tailWord_4999438) baseStart_4999438 baseEnd_4999438 := by
    simpa [prefixWord, tailWord_4999438, baseEnd_4999438] using wordTrace_append hprefix tailTrace_4999438
  have hstable : (prefixWord ++ tailWord_4999438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999438).length < 2 ^ (prefixWord ++ tailWord_4999438).sum := by decide
  have hdescent : baseEnd_4999438 < baseStart_4999438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999455 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 6]
def baseStart_4999455 : Nat := 118140960795 + 4999455 * 2 ^ 59
def prefixEnd_4999455 : Nat := 4983230072969 + 3 ^ 40 * 4999455 * 2
def baseEnd_4999455 : Nat := 285235936169315815891159

theorem tailTrace_4999455 : CollatzResearch.WordTrace tailWord_4999455 prefixEnd_4999455 285235936169315815891159 := by
  unfold tailWord_4999455
  simp only [CollatzResearch.WordTrace]
  refine ⟨182345104102835848781519819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121563402735223899187679879 182345104102835848781519819)
  ·
    refine ⟨273517656154253773172279729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182345104102835848781519819 273517656154253773172279729)
    ·
      refine ⟨205138242115690329879209797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273517656154253773172279729 205138242115690329879209797)
      ·
        refine ⟨38463420396691936852351837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205138242115690329879209797 38463420396691936852351837)
        ·
          refine ⟨14423782648759476319631939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38463420396691936852351837 14423782648759476319631939)
          ·
            refine ⟨21635673973139214479447909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14423782648759476319631939 21635673973139214479447909)
            ·
              refine ⟨4056688869963602714896483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21635673973139214479447909 4056688869963602714896483)
              ·
                refine ⟨6085033304945404072344725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056688869963602714896483 6085033304945404072344725)
                ·
                  refine ⟨285235936169315815891159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6085033304945404072344725 285235936169315815891159)
                  ·
                    rfl

theorem cell23_4999455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 6].length) (baseStart_4999455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999455 prefixEnd_4999455 := by exact prefixLift 4999455
  have htrace : WordTrace (prefixWord ++ tailWord_4999455) baseStart_4999455 baseEnd_4999455 := by
    simpa [prefixWord, tailWord_4999455, baseEnd_4999455] using wordTrace_append hprefix tailTrace_4999455
  have hstable : (prefixWord ++ tailWord_4999455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999455).length < 2 ^ (prefixWord ++ tailWord_4999455).sum := by decide
  have hdescent : baseEnd_4999455 < baseStart_4999455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999469 : List Nat := [1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4999469 : Nat := 118140960795 + 4999469 * 2 ^ 59
def prefixEnd_4999469 : Nat := 4983230072969 + 3 ^ 40 * 4999469 * 2
def baseEnd_4999469 : Nat := 2567130614253005288245367

theorem tailTrace_4999469 : CollatzResearch.WordTrace tailWord_4999469 prefixEnd_4999469 2567130614253005288245367 := by
  unfold tailWord_4999469
  simp only [CollatzResearch.WordTrace]
  refine ⟨182345614724785129172529461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121563743149856752781686307 182345614724785129172529461)
  ·
    refine ⟨17094901380448605859924637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182345614724785129172529461 17094901380448605859924637)
    ·
      refine ⟨6410588017668227197471739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17094901380448605859924637 6410588017668227197471739)
      ·
        refine ⟨9615882026502340796207609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410588017668227197471739 9615882026502340796207609)
        ·
          refine ⟨7211911519876755597155707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9615882026502340796207609 7211911519876755597155707)
          ·
            refine ⟨10817867279815133395733561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7211911519876755597155707 10817867279815133395733561)
            ·
              refine ⟨8113400459861350046800171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10817867279815133395733561 8113400459861350046800171)
              ·
                refine ⟨12170100689792025070200257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8113400459861350046800171 12170100689792025070200257)
                ·
                  refine ⟨9127575517344018802650193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12170100689792025070200257 9127575517344018802650193)
                  ·
                    refine ⟨6845681638008014101987645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9127575517344018802650193 6845681638008014101987645)
                    ·
                      refine ⟨2567130614253005288245367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6845681638008014101987645 2567130614253005288245367)
                      ·
                        rfl

theorem cell23_4999469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4999469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999469 prefixEnd_4999469 := by exact prefixLift 4999469
  have htrace : WordTrace (prefixWord ++ tailWord_4999469) baseStart_4999469 baseEnd_4999469 := by
    simpa [prefixWord, tailWord_4999469, baseEnd_4999469] using wordTrace_append hprefix tailTrace_4999469
  have hstable : (prefixWord ++ tailWord_4999469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999469).length < 2 ^ (prefixWord ++ tailWord_4999469).sum := by decide
  have hdescent : baseEnd_4999469 < baseStart_4999469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999525 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_4999525 : Nat := 118140960795 + 4999525 * 2 ^ 59
def prefixEnd_4999525 : Nat := 4983230072969 + 3 ^ 40 * 4999525 * 2
def baseEnd_4999525 : Nat := 2567159369169657069145109

theorem tailTrace_4999525 : CollatzResearch.WordTrace tailWord_4999525 prefixEnd_4999525 2567159369169657069145109 := by
  unfold tailWord_4999525
  simp only [CollatzResearch.WordTrace]
  refine ⟨182347657212582250736568029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121565104808388167157712019 182347657212582250736568029)
  ·
    refine ⟨68380371454718344026213011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182347657212582250736568029 68380371454718344026213011)
    ·
      refine ⟨102570557182077516039319517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68380371454718344026213011 102570557182077516039319517)
      ·
        refine ⟨38463958943279068514744819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102570557182077516039319517 38463958943279068514744819)
        ·
          refine ⟨57695938414918602772117229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38463958943279068514744819 57695938414918602772117229)
          ·
            refine ⟨21635976905594476039543961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57695938414918602772117229 21635976905594476039543961)
            ·
              refine ⟨16226982679195857029657971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21635976905594476039543961 16226982679195857029657971)
              ·
                refine ⟨24340474018793785544486957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16226982679195857029657971 24340474018793785544486957)
                ·
                  refine ⟨9127677757047669579182609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24340474018793785544486957 9127677757047669579182609)
                  ·
                    refine ⟨6845758317785752184386957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9127677757047669579182609 6845758317785752184386957)
                    ·
                      refine ⟨2567159369169657069145109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6845758317785752184386957 2567159369169657069145109)
                      ·
                        rfl

theorem cell23_4999525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_4999525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999525 prefixEnd_4999525 := by exact prefixLift 4999525
  have htrace : WordTrace (prefixWord ++ tailWord_4999525) baseStart_4999525 baseEnd_4999525 := by
    simpa [prefixWord, tailWord_4999525, baseEnd_4999525] using wordTrace_append hprefix tailTrace_4999525
  have hstable : (prefixWord ++ tailWord_4999525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999525).length < 2 ^ (prefixWord ++ tailWord_4999525).sum := by decide
  have hdescent : baseEnd_4999525 < baseStart_4999525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999588 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_4999588 : Nat := 118140960795 + 4999588 * 2 ^ 59
def prefixEnd_4999588 : Nat := 4983230072969 + 3 ^ 40 * 4999588 * 2
def baseEnd_4999588 : Nat := 855730572816963440885773

theorem tailTrace_4999588 : CollatzResearch.WordTrace tailWord_4999588 prefixEnd_4999588 855730572816963440885773 := by
  unfold tailWord_4999588
  simp only [CollatzResearch.WordTrace]
  refine ⟨91174977505677006248055709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121566636674236008330740945 91174977505677006248055709)
  ·
    refine ⟨34190616564628877343020891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91174977505677006248055709 34190616564628877343020891)
    ·
      refine ⟨51285924846943316014531337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34190616564628877343020891 51285924846943316014531337)
      ·
        refine ⟨38464443635207487010898503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51285924846943316014531337 38464443635207487010898503)
        ·
          refine ⟨57696665452811230516347755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38464443635207487010898503 57696665452811230516347755)
          ·
            refine ⟨86544998179216845774521633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57696665452811230516347755 86544998179216845774521633)
            ·
              refine ⟨64908748634412634330891225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86544998179216845774521633 64908748634412634330891225)
              ·
                refine ⟨48681561475809475748168419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64908748634412634330891225 48681561475809475748168419)
                ·
                  refine ⟨73022342213714213622252629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48681561475809475748168419 73022342213714213622252629)
                  ·
                    refine ⟨855730572816963440885773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73022342213714213622252629 855730572816963440885773)
                    ·
                      rfl

theorem cell23_4999588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_4999588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999588 prefixEnd_4999588 := by exact prefixLift 4999588
  have htrace : WordTrace (prefixWord ++ tailWord_4999588) baseStart_4999588 baseEnd_4999588 := by
    simpa [prefixWord, tailWord_4999588, baseEnd_4999588] using wordTrace_append hprefix tailTrace_4999588
  have hstable : (prefixWord ++ tailWord_4999588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999588).length < 2 ^ (prefixWord ++ tailWord_4999588).sum := by decide
  have hdescent : baseEnd_4999588 < baseStart_4999588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999650 : List Nat := [3, 3, 3, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4999650 : Nat := 118140960795 + 4999650 * 2 ^ 59
def prefixEnd_4999650 : Nat := 4983230072969 + 3 ^ 40 * 4999650 * 2
def baseEnd_4999650 : Nat := 2567223554251469080082035

theorem tailTrace_4999650 : CollatzResearch.WordTrace tailWord_4999650 prefixEnd_4999650 2567223554251469080082035 := by
  unfold tailWord_4999650
  simp only [CollatzResearch.WordTrace]
  refine ⟨45588054084282349271217101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121568144224752931389912269 45588054084282349271217101)
  ·
    refine ⟨17095520281605880976706413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45588054084282349271217101 17095520281605880976706413)
    ·
      refine ⟨6410820105602205366264905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17095520281605880976706413 6410820105602205366264905)
      ·
        refine ⟨4808115079201654024698679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6410820105602205366264905 4808115079201654024698679)
        ·
          refine ⟨7212172618802481037048019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808115079201654024698679 7212172618802481037048019)
          ·
            refine ⟨10818258928203721555572029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212172618802481037048019 10818258928203721555572029)
            ·
              refine ⟨4056847098076395583339511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10818258928203721555572029 4056847098076395583339511)
              ·
                refine ⟨6085270647114593375009267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056847098076395583339511 6085270647114593375009267)
                ·
                  refine ⟨9127905970671890062513901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6085270647114593375009267 9127905970671890062513901)
                  ·
                    refine ⟨3422964739001958773442713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9127905970671890062513901 3422964739001958773442713)
                    ·
                      refine ⟨2567223554251469080082035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3422964739001958773442713 2567223554251469080082035)
                      ·
                        rfl

theorem cell23_4999650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4999650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999650 prefixEnd_4999650 := by exact prefixLift 4999650
  have htrace : WordTrace (prefixWord ++ tailWord_4999650) baseStart_4999650 baseEnd_4999650 := by
    simpa [prefixWord, tailWord_4999650, baseEnd_4999650] using wordTrace_append hprefix tailTrace_4999650
  have hstable : (prefixWord ++ tailWord_4999650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999650).length < 2 ^ (prefixWord ++ tailWord_4999650).sum := by decide
  have hdescent : baseEnd_4999650 < baseStart_4999650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999665 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 2, 5]
def baseStart_4999665 : Nat := 118140960795 + 4999665 * 2 ^ 59
def prefixEnd_4999665 : Nat := 4983230072969 + 3 ^ 40 * 4999665 * 2
def baseEnd_4999665 : Nat := 855743752153762173798155

theorem tailTrace_4999665 : CollatzResearch.WordTrace tailWord_4999665 prefixEnd_4999665 855743752153762173798155 := by
  unfold tailWord_4999665
  simp only [CollatzResearch.WordTrace]
  refine ⟨182352763432075054646664449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121568508954716703097776299 182352763432075054646664449)
  ·
    refine ⟨136764572574056290984998337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182352763432075054646664449 136764572574056290984998337)
    ·
      refine ⟨102573429430542218238748753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136764572574056290984998337 102573429430542218238748753)
      ·
        refine ⟨76930072072906663679061565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102573429430542218238748753 76930072072906663679061565)
        ·
          refine ⟨28848777027339998879648087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76930072072906663679061565 28848777027339998879648087)
          ·
            refine ⟨43273165541009998319472131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28848777027339998879648087 43273165541009998319472131)
            ·
              refine ⟨64909748311514997479208197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43273165541009998319472131 64909748311514997479208197)
              ·
                refine ⟨12170577808409062027351537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64909748311514997479208197 12170577808409062027351537)
                ·
                  refine ⟨9127933356306796520513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12170577808409062027351537 9127933356306796520513653)
                  ·
                    refine ⟨855743752153762173798155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9127933356306796520513653 855743752153762173798155)
                    ·
                      rfl

theorem cell23_4999665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_4999665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999665 prefixEnd_4999665 := by exact prefixLift 4999665
  have htrace : WordTrace (prefixWord ++ tailWord_4999665) baseStart_4999665 baseEnd_4999665 := by
    simpa [prefixWord, tailWord_4999665, baseEnd_4999665] using wordTrace_append hprefix tailTrace_4999665
  have hstable : (prefixWord ++ tailWord_4999665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999665).length < 2 ^ (prefixWord ++ tailWord_4999665).sum := by decide
  have hdescent : baseEnd_4999665 < baseStart_4999665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999685 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_4999685 : Nat := 118140960795 + 4999685 * 2 ^ 59
def prefixEnd_4999685 : Nat := 4983230072969 + 3 ^ 40 * 4999685 * 2
def baseEnd_4999685 : Nat := 2567241526074376443144373

theorem tailTrace_4999685 : CollatzResearch.WordTrace tailWord_4999685 prefixEnd_4999685 2567241526074376443144373 := by
  unfold tailWord_4999685
  simp only [CollatzResearch.WordTrace]
  refine ⟨182353492892002598062392509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121568995261335065374928339 182353492892002598062392509)
  ·
    refine ⟨68382559834500974273397191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182353492892002598062392509 68382559834500974273397191)
    ·
      refine ⟨102573839751751461410095787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68382559834500974273397191 102573839751751461410095787)
      ·
        refine ⟨153860759627627192115143681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102573839751751461410095787 153860759627627192115143681)
        ·
          refine ⟨115395569720720394086357761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153860759627627192115143681 115395569720720394086357761)
          ·
            refine ⟨86546677290540295564768321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115395569720720394086357761 86546677290540295564768321)
            ·
              refine ⟨64910007967905221673576241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86546677290540295564768321 64910007967905221673576241)
              ·
                refine ⟨48682505975928916255182181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64910007967905221673576241 48682505975928916255182181)
                ·
                  refine ⟨9127969870486671797846659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48682505975928916255182181 9127969870486671797846659)
                  ·
                    refine ⟨13691954805730007696769989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9127969870486671797846659 13691954805730007696769989)
                    ·
                      refine ⟨2567241526074376443144373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13691954805730007696769989 2567241526074376443144373)
                      ·
                        rfl

theorem cell23_4999685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_4999685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999685 prefixEnd_4999685 := by exact prefixLift 4999685
  have htrace : WordTrace (prefixWord ++ tailWord_4999685) baseStart_4999685 baseEnd_4999685 := by
    simpa [prefixWord, tailWord_4999685, baseEnd_4999685] using wordTrace_append hprefix tailTrace_4999685
  have hstable : (prefixWord ++ tailWord_4999685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999685).length < 2 ^ (prefixWord ++ tailWord_4999685).sum := by decide
  have hdescent : baseEnd_4999685 < baseStart_4999685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999686 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_4999686 : Nat := 118140960795 + 4999686 * 2 ^ 59
def prefixEnd_4999686 : Nat := 4983230072969 + 3 ^ 40 * 4999686 * 2
def baseEnd_4999686 : Nat := 285249115506114548803541

theorem tailTrace_4999686 : CollatzResearch.WordTrace tailWord_4999686 prefixEnd_4999686 285249115506114548803541 := by
  unfold tailWord_4999686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5698547792656217976036841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 121569019576665983488785941 5698547792656217976036841)
  ·
    refine ⟨4273910844492163482027631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5698547792656217976036841 4273910844492163482027631)
    ·
      refine ⟨6410866266738245223041447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4273910844492163482027631 6410866266738245223041447)
      ·
        refine ⟨9616299400107367834562171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410866266738245223041447 9616299400107367834562171)
        ·
          refine ⟨14424449100161051751843257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9616299400107367834562171 14424449100161051751843257)
          ·
            refine ⟨10818336825120788813882443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14424449100161051751843257 10818336825120788813882443)
            ·
              refine ⟨16227505237681183220823665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10818336825120788813882443 16227505237681183220823665)
              ·
                refine ⟨12170628928260887415617749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16227505237681183220823665 12170628928260887415617749)
                ·
                  refine ⟨285249115506114548803541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12170628928260887415617749 285249115506114548803541)
                  ·
                    rfl

theorem cell23_4999686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_4999686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999686 prefixEnd_4999686 := by exact prefixLift 4999686
  have htrace : WordTrace (prefixWord ++ tailWord_4999686) baseStart_4999686 baseEnd_4999686 := by
    simpa [prefixWord, tailWord_4999686, baseEnd_4999686] using wordTrace_append hprefix tailTrace_4999686
  have hstable : (prefixWord ++ tailWord_4999686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999686).length < 2 ^ (prefixWord ++ tailWord_4999686).sum := by decide
  have hdescent : baseEnd_4999686 < baseStart_4999686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999695 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 5, 4]
def baseStart_4999695 : Nat := 118140960795 + 4999695 * 2 ^ 59
def prefixEnd_4999695 : Nat := 4983230072969 + 3 ^ 40 * 4999695 * 2
def baseEnd_4999695 : Nat := 855748886960307134673109

theorem tailTrace_4999695 : CollatzResearch.WordTrace tailWord_4999695 prefixEnd_4999695 855748886960307134673109 := by
  unfold tailWord_4999695
  simp only [CollatzResearch.WordTrace]
  refine ⟨182353857621966369770256539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121569238414644246513504359 182353857621966369770256539)
  ·
    refine ⟨273530786432949554655384809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182353857621966369770256539 273530786432949554655384809)
    ·
      refine ⟨205148089824712165991538607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273530786432949554655384809 205148089824712165991538607)
      ·
        refine ⟨307722134737068248987307911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205148089824712165991538607 307722134737068248987307911)
        ·
          refine ⟨461583202105602373480961867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307722134737068248987307911 461583202105602373480961867)
          ·
            refine ⟨692374803158403560221442801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461583202105602373480961867 692374803158403560221442801)
            ·
              refine ⟨519281102368802670166082101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692374803158403560221442801 519281102368802670166082101)
              ·
                refine ⟨48682603347075250328070197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519281102368802670166082101 48682603347075250328070197)
                ·
                  refine ⟨4563994063788304718256581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48682603347075250328070197 4563994063788304718256581)
                  ·
                    refine ⟨855748886960307134673109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4563994063788304718256581 855748886960307134673109)
                    ·
                      rfl

theorem cell23_4999695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_4999695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999695 prefixEnd_4999695 := by exact prefixLift 4999695
  have htrace : WordTrace (prefixWord ++ tailWord_4999695) baseStart_4999695 baseEnd_4999695 := by
    simpa [prefixWord, tailWord_4999695, baseEnd_4999695] using wordTrace_append hprefix tailTrace_4999695
  have hstable : (prefixWord ++ tailWord_4999695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999695).length < 2 ^ (prefixWord ++ tailWord_4999695).sum := by decide
  have hdescent : baseEnd_4999695 < baseStart_4999695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999705 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 3]
def baseStart_4999705 : Nat := 118140960795 + 4999705 * 2 ^ 59
def prefixEnd_4999705 : Nat := 4983230072969 + 3 ^ 40 * 4999705 * 2
def baseEnd_4999705 : Nat := 2567251795687466364894281

theorem tailTrace_4999705 : CollatzResearch.WordTrace tailWord_4999705 prefixEnd_4999705 2567251795687466364894281 := by
  unfold tailWord_4999705
  simp only [CollatzResearch.WordTrace]
  refine ⟨182354222351930141478120569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121569481567953427652080379 182354222351930141478120569)
  ·
    refine ⟨136765666763947606108590427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182354222351930141478120569 136765666763947606108590427)
    ·
      refine ⟨205148500145921409162885641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136765666763947606108590427 205148500145921409162885641)
      ·
        refine ⟨153861375109441056872164231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205148500145921409162885641 153861375109441056872164231)
        ·
          refine ⟨230792062664161585308246347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153861375109441056872164231 230792062664161585308246347)
          ·
            refine ⟨346188093996242377962369521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230792062664161585308246347 346188093996242377962369521)
            ·
              refine ⟨259641070497181783471777141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346188093996242377962369521 259641070497181783471777141)
              ·
                refine ⟨24341350359110792200479107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259641070497181783471777141 24341350359110792200479107)
                ·
                  refine ⟨36512025538666188300718661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24341350359110792200479107 36512025538666188300718661)
                  ·
                    refine ⟨6846004788499910306384749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36512025538666188300718661 6846004788499910306384749)
                    ·
                      refine ⟨2567251795687466364894281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846004788499910306384749 2567251795687466364894281)
                      ·
                        rfl

theorem cell23_4999705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_4999705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999705 prefixEnd_4999705 := by exact prefixLift 4999705
  have htrace : WordTrace (prefixWord ++ tailWord_4999705) baseStart_4999705 baseEnd_4999705 := by
    simpa [prefixWord, tailWord_4999705, baseEnd_4999705] using wordTrace_append hprefix tailTrace_4999705
  have hstable : (prefixWord ++ tailWord_4999705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999705).length < 2 ^ (prefixWord ++ tailWord_4999705).sum := by decide
  have hdescent : baseEnd_4999705 < baseStart_4999705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999715 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6]
def baseStart_4999715 : Nat := 118140960795 + 4999715 * 2 ^ 59
def prefixEnd_4999715 : Nat := 4983230072969 + 3 ^ 40 * 4999715 * 2
def baseEnd_4999715 : Nat := 2567256930494011325769235

theorem tailTrace_4999715 : CollatzResearch.WordTrace tailWord_4999715 prefixEnd_4999715 2567256930494011325769235 := by
  unfold tailWord_4999715
  simp only [CollatzResearch.WordTrace]
  refine ⟨182354587081893913185984599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121569724721262608790656399 182354587081893913185984599)
  ·
    refine ⟨273531880622840869778976899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182354587081893913185984599 273531880622840869778976899)
    ·
      refine ⟨410297820934261304668465349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273531880622840869778976899 410297820934261304668465349)
      ·
        refine ⟨76930841425173994625337253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 410297820934261304668465349 76930841425173994625337253)
        ·
          refine ⟨14424532767220123992250735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76930841425173994625337253 14424532767220123992250735)
          ·
            refine ⟨21636799150830185988376103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14424532767220123992250735 21636799150830185988376103)
            ·
              refine ⟨32455198726245278982564155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21636799150830185988376103 32455198726245278982564155)
              ·
                refine ⟨48682798089367918473846233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32455198726245278982564155 48682798089367918473846233)
                ·
                  refine ⟨36512098567025938855384675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48682798089367918473846233 36512098567025938855384675)
                  ·
                    refine ⟨54768147850538908283077013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36512098567025938855384675 54768147850538908283077013)
                    ·
                      refine ⟨2567256930494011325769235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54768147850538908283077013 2567256930494011325769235)
                      ·
                        rfl

theorem cell23_4999715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_4999715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999715 prefixEnd_4999715 := by exact prefixLift 4999715
  have htrace : WordTrace (prefixWord ++ tailWord_4999715) baseStart_4999715 baseEnd_4999715 := by
    simpa [prefixWord, tailWord_4999715, baseEnd_4999715] using wordTrace_append hprefix tailTrace_4999715
  have hstable : (prefixWord ++ tailWord_4999715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999715).length < 2 ^ (prefixWord ++ tailWord_4999715).sum := by decide
  have hdescent : baseEnd_4999715 < baseStart_4999715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999729 : List Nat := [1, 2, 2, 3, 1, 1, 4, 4, 1, 4]
def baseStart_4999729 : Nat := 118140960795 + 4999729 * 2 ^ 59
def prefixEnd_4999729 : Nat := 4983230072969 + 3 ^ 40 * 4999729 * 2
def baseEnd_4999729 : Nat := 855754706407724756998057

theorem tailTrace_4999729 : CollatzResearch.WordTrace tailWord_4999729 prefixEnd_4999729 855754706407724756998057 := by
  unfold tailWord_4999729
  simp only [CollatzResearch.WordTrace]
  refine ⟨182355097703843193576994241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121570065135895462384662827 182355097703843193576994241)
  ·
    refine ⟨136766323277882395182745681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182355097703843193576994241 136766323277882395182745681)
    ·
      refine ⟨102574742458411796387059261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136766323277882395182745681 102574742458411796387059261)
      ·
        refine ⟨38465528421904423645147223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102574742458411796387059261 38465528421904423645147223)
        ·
          refine ⟨57698292632856635467720835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38465528421904423645147223 57698292632856635467720835)
          ·
            refine ⟨86547438949284953201581253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57698292632856635467720835 86547438949284953201581253)
            ·
              refine ⟨16227644802990928725296485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86547438949284953201581253 16227644802990928725296485)
              ·
                refine ⟨3042683400560799135993091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16227644802990928725296485 3042683400560799135993091)
                ·
                  refine ⟨4564025100841198703989637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3042683400560799135993091 4564025100841198703989637)
                  ·
                    refine ⟨855754706407724756998057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564025100841198703989637 855754706407724756998057)
                    ·
                      rfl

theorem cell23_4999729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_4999729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999729 prefixEnd_4999729 := by exact prefixLift 4999729
  have htrace : WordTrace (prefixWord ++ tailWord_4999729) baseStart_4999729 baseEnd_4999729 := by
    simpa [prefixWord, tailWord_4999729, baseEnd_4999729] using wordTrace_append hprefix tailTrace_4999729
  have hstable : (prefixWord ++ tailWord_4999729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999729).length < 2 ^ (prefixWord ++ tailWord_4999729).sum := by decide
  have hdescent : baseEnd_4999729 < baseStart_4999729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999755 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 3, 5]
def baseStart_4999755 : Nat := 118140960795 + 4999755 * 2 ^ 59
def prefixEnd_4999755 : Nat := 4983230072969 + 3 ^ 40 * 4999755 * 2
def baseEnd_4999755 : Nat := 855759156573397056423017

theorem tailTrace_4999755 : CollatzResearch.WordTrace tailWord_4999755 prefixEnd_4999755 855759156573397056423017 := by
  unfold tailWord_4999755
  simp only [CollatzResearch.WordTrace]
  refine ⟨182356046001749000017440719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121570697334499333344960479 182356046001749000017440719)
  ·
    refine ⟨273534069002623500026161079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182356046001749000017440719 273534069002623500026161079)
    ·
      refine ⟨410301103503935250039241619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273534069002623500026161079 410301103503935250039241619)
      ·
        refine ⟨615451655255902875058862429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410301103503935250039241619 615451655255902875058862429)
        ·
          refine ⟨230794370720963578147073411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 615451655255902875058862429 230794370720963578147073411)
          ·
            refine ⟨346191556081445367220610117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230794370720963578147073411 346191556081445367220610117)
            ·
              refine ⟨64910916765271006353864397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346191556081445367220610117 64910916765271006353864397)
              ·
                refine ⟨24341593786976627382699149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64910916765271006353864397 24341593786976627382699149)
                ·
                  refine ⟨9128097670116235268512181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24341593786976627382699149 9128097670116235268512181)
                  ·
                    refine ⟨855759156573397056423017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9128097670116235268512181 855759156573397056423017)
                    ·
                      rfl

theorem cell23_4999755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 5].length) (baseStart_4999755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999755 prefixEnd_4999755 := by exact prefixLift 4999755
  have htrace : WordTrace (prefixWord ++ tailWord_4999755) baseStart_4999755 baseEnd_4999755 := by
    simpa [prefixWord, tailWord_4999755, baseEnd_4999755] using wordTrace_append hprefix tailTrace_4999755
  have hstable : (prefixWord ++ tailWord_4999755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999755).length < 2 ^ (prefixWord ++ tailWord_4999755).sum := by decide
  have hdescent : baseEnd_4999755 < baseStart_4999755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999779 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 2, 3, 2]
def baseStart_4999779 : Nat := 118140960795 + 4999779 * 2 ^ 59
def prefixEnd_4999779 : Nat := 4983230072969 + 3 ^ 40 * 4999779 * 2
def baseEnd_4999779 : Nat := 2567289793255899075368941

theorem tailTrace_4999779 : CollatzResearch.WordTrace tailWord_4999779 prefixEnd_4999779 2567289793255899075368941 := by
  unfold tailWord_4999779
  simp only [CollatzResearch.WordTrace]
  refine ⟨182356921353662052116314391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121571280902441368077542927 182356921353662052116314391)
  ·
    refine ⟨273535382030493078174471587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182356921353662052116314391 273535382030493078174471587)
    ·
      refine ⟨410303073045739617261707381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273535382030493078174471587 410303073045739617261707381)
      ·
        refine ⟨38465913098038089118285067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 410303073045739617261707381 38465913098038089118285067)
        ·
          refine ⟨57698869647057133677427601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38465913098038089118285067 57698869647057133677427601)
          ·
            refine ⟨43274152235292850258070701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57698869647057133677427601 43274152235292850258070701)
            ·
              refine ⟨16227807088234818846776513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43274152235292850258070701 16227807088234818846776513)
              ·
                refine ⟨12170855316176114135082385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16227807088234818846776513 12170855316176114135082385)
                ·
                  refine ⟨9128141487132085601311789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12170855316176114135082385 9128141487132085601311789)
                  ·
                    refine ⟨3423053057674532100491921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9128141487132085601311789 3423053057674532100491921)
                    ·
                      refine ⟨2567289793255899075368941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423053057674532100491921 2567289793255899075368941)
                      ·
                        rfl

theorem cell23_4999779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_4999779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999779 prefixEnd_4999779 := by exact prefixLift 4999779
  have htrace : WordTrace (prefixWord ++ tailWord_4999779) baseStart_4999779 baseEnd_4999779 := by
    simpa [prefixWord, tailWord_4999779, baseEnd_4999779] using wordTrace_append hprefix tailTrace_4999779
  have hstable : (prefixWord ++ tailWord_4999779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999779).length < 2 ^ (prefixWord ++ tailWord_4999779).sum := by decide
  have hdescent : baseEnd_4999779 < baseStart_4999779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999795 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5]
def baseStart_4999795 : Nat := 118140960795 + 4999795 * 2 ^ 59
def prefixEnd_4999795 : Nat := 4983230072969 + 3 ^ 40 * 4999795 * 2
def baseEnd_4999795 : Nat := 2567298008946371012768867

theorem tailTrace_4999795 : CollatzResearch.WordTrace tailWord_4999795 prefixEnd_4999795 2567298008946371012768867 := by
  unfold tailWord_4999795
  simp only [CollatzResearch.WordTrace]
  refine ⟨182357504921604086848896839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121571669947736057899264559 182357504921604086848896839)
  ·
    refine ⟨273536257382406130273345259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182357504921604086848896839 273536257382406130273345259)
    ·
      refine ⟨410304386073609195410017889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273536257382406130273345259 410304386073609195410017889)
      ·
        refine ⟨307728289555206896557513417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410304386073609195410017889 307728289555206896557513417)
        ·
          refine ⟨230796217166405172418135063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307728289555206896557513417 230796217166405172418135063)
          ·
            refine ⟨346194325749607758627202595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230796217166405172418135063 346194325749607758627202595)
            ·
              refine ⟨519291488624411637940803893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346194325749607758627202595 519291488624411637940803893)
              ·
                refine ⟨48683577058538591056950365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 519291488624411637940803893 48683577058538591056950365)
                ·
                  refine ⟨18256341396951971646356387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48683577058538591056950365 18256341396951971646356387)
                  ·
                    refine ⟨27384512095427957469534581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18256341396951971646356387 27384512095427957469534581)
                    ·
                      refine ⟨2567298008946371012768867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27384512095427957469534581 2567298008946371012768867)
                      ·
                        rfl

theorem cell23_4999795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_4999795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999795 prefixEnd_4999795 := by exact prefixLift 4999795
  have htrace : WordTrace (prefixWord ++ tailWord_4999795) baseStart_4999795 baseEnd_4999795 := by
    simpa [prefixWord, tailWord_4999795, baseEnd_4999795] using wordTrace_append hprefix tailTrace_4999795
  have hstable : (prefixWord ++ tailWord_4999795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999795).length < 2 ^ (prefixWord ++ tailWord_4999795).sum := by decide
  have hdescent : baseEnd_4999795 < baseStart_4999795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999815 : List Nat := [1, 1, 4, 2, 1, 2, 1, 11]
def baseStart_4999815 : Nat := 118140960795 + 4999815 * 2 ^ 59
def prefixEnd_4999815 : Nat := 4983230072969 + 3 ^ 40 * 4999815 * 2
def baseEnd_4999815 : Nat := 95085491798498553130325

theorem tailTrace_4999815 : CollatzResearch.WordTrace tailWord_4999815 prefixEnd_4999815 95085491798498553130325 := by
  unfold tailWord_4999815
  simp only [CollatzResearch.WordTrace]
  refine ⟨182358234381531630264624899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121572156254354420176416599 182358234381531630264624899)
  ·
    refine ⟨273537351572297445396937349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182358234381531630264624899 273537351572297445396937349)
    ·
      refine ⟨51288253419805771011925753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 273537351572297445396937349 51288253419805771011925753)
      ·
        refine ⟨38466190064854328258944315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51288253419805771011925753 38466190064854328258944315)
        ·
          refine ⟨57699285097281492388416473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38466190064854328258944315 57699285097281492388416473)
          ·
            refine ⟨43274463822961119291312355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57699285097281492388416473 43274463822961119291312355)
            ·
              refine ⟨64911695734441678936968533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43274463822961119291312355 64911695734441678936968533)
              ·
                refine ⟨95085491798498553130325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 64911695734441678936968533 95085491798498553130325)
                ·
                  rfl

theorem cell23_4999815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 11].length) (baseStart_4999815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999815 prefixEnd_4999815 := by exact prefixLift 4999815
  have htrace : WordTrace (prefixWord ++ tailWord_4999815) baseStart_4999815 baseEnd_4999815 := by
    simpa [prefixWord, tailWord_4999815, baseEnd_4999815] using wordTrace_append hprefix tailTrace_4999815
  have hstable : (prefixWord ++ tailWord_4999815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999815).length < 2 ^ (prefixWord ++ tailWord_4999815).sum := by decide
  have hdescent : baseEnd_4999815 < baseStart_4999815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999836 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_4999836 : Nat := 118140960795 + 4999836 * 2 ^ 59
def prefixEnd_4999836 : Nat := 4983230072969 + 3 ^ 40 * 4999836 * 2
def baseEnd_4999836 : Nat := 855773020551068450785393

theorem tailTrace_4999836 : CollatzResearch.WordTrace tailWord_4999836 prefixEnd_4999836 855773020551068450785393 := by
  unfold tailWord_4999836
  simp only [CollatzResearch.WordTrace]
  refine ⟨91179500157227775425569681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121572666876303700567426241 91179500157227775425569681)
  ·
    refine ⟨68384625117920831569177261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91179500157227775425569681 68384625117920831569177261)
    ·
      refine ⟨25644234419220311838441473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68384625117920831569177261 25644234419220311838441473)
      ·
        refine ⟨19233175814415233878831105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25644234419220311838441473 19233175814415233878831105)
        ·
          refine ⟨14424881860811425409123329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19233175814415233878831105 14424881860811425409123329)
          ·
            refine ⟨10818661395608569056842497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14424881860811425409123329 10818661395608569056842497)
            ·
              refine ⟨8113996046706426792631873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10818661395608569056842497 8113996046706426792631873)
              ·
                refine ⟨6085497035029820094473905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8113996046706426792631873 6085497035029820094473905)
                ·
                  refine ⟨4564122776272365070855429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6085497035029820094473905 4564122776272365070855429)
                  ·
                    refine ⟨855773020551068450785393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564122776272365070855429 855773020551068450785393)
                    ·
                      rfl

theorem cell23_4999836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_4999836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999836 prefixEnd_4999836 := by exact prefixLift 4999836
  have htrace : WordTrace (prefixWord ++ tailWord_4999836) baseStart_4999836 baseEnd_4999836 := by
    simpa [prefixWord, tailWord_4999836, baseEnd_4999836] using wordTrace_append hprefix tailTrace_4999836
  have hstable : (prefixWord ++ tailWord_4999836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999836).length < 2 ^ (prefixWord ++ tailWord_4999836).sum := by decide
  have hdescent : baseEnd_4999836 < baseStart_4999836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999859 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 3]
def baseStart_4999859 : Nat := 118140960795 + 4999859 * 2 ^ 59
def prefixEnd_4999859 : Nat := 4983230072969 + 3 ^ 40 * 4999859 * 2
def baseEnd_4999859 : Nat := 2567330871708258762368573

theorem tailTrace_4999859 : CollatzResearch.WordTrace tailWord_4999859 prefixEnd_4999859 2567330871708258762368573 := by
  unfold tailWord_4999859
  simp only [CollatzResearch.WordTrace]
  refine ⟨182359839193372225779226631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121573226128914817186151087 182359839193372225779226631)
  ·
    refine ⟨273539758790058338668839947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182359839193372225779226631 273539758790058338668839947)
    ·
      refine ⟨410309638185087508003259921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273539758790058338668839947 410309638185087508003259921)
      ·
        refine ⟨307732228638815631002444941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410309638185087508003259921 307732228638815631002444941)
        ·
          refine ⟨115399585739555861625916853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307732228638815631002444941 115399585739555861625916853)
          ·
            refine ⟨10818711163083362027429705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115399585739555861625916853 10818711163083362027429705)
            ·
              refine ⟨8114033372312521520572279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10818711163083362027429705 8114033372312521520572279)
              ·
                refine ⟨12171050058468782280858419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8114033372312521520572279 12171050058468782280858419)
                ·
                  refine ⟨18256575087703173421287629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12171050058468782280858419 18256575087703173421287629)
                  ·
                    refine ⟨6846215657888690032982861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18256575087703173421287629 6846215657888690032982861)
                    ·
                      refine ⟨2567330871708258762368573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846215657888690032982861 2567330871708258762368573)
                      ·
                        rfl

theorem cell23_4999859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_4999859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999859 prefixEnd_4999859 := by exact prefixLift 4999859
  have htrace : WordTrace (prefixWord ++ tailWord_4999859) baseStart_4999859 baseEnd_4999859 := by
    simpa [prefixWord, tailWord_4999859, baseEnd_4999859] using wordTrace_append hprefix tailTrace_4999859
  have hstable : (prefixWord ++ tailWord_4999859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999859).length < 2 ^ (prefixWord ++ tailWord_4999859).sum := by decide
  have hdescent : baseEnd_4999859 < baseStart_4999859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4999893 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_4999893 : Nat := 118140960795 + 4999893 * 2 ^ 59
def prefixEnd_4999893 : Nat := 4983230072969 + 3 ^ 40 * 4999893 * 2
def baseEnd_4999893 : Nat := 2567348330050511629343417

theorem tailTrace_4999893 : CollatzResearch.WordTrace tailWord_4999893 prefixEnd_4999893 2567348330050511629343417 := by
  unfold tailWord_4999893
  simp only [CollatzResearch.WordTrace]
  refine ⟨182361079275249049585964333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121574052850166033057309555 182361079275249049585964333)
  ·
    refine ⟨68385404728218393594736625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182361079275249049585964333 68385404728218393594736625)
    ·
      refine ⟨51289053546163795196052469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68385404728218393594736625 51289053546163795196052469)
      ·
        refine ⟨4808348769952855799629919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51289053546163795196052469 4808348769952855799629919)
        ·
          refine ⟨7212523154929283699444879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808348769952855799629919 7212523154929283699444879)
          ·
            refine ⟨10818784732393925549167319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212523154929283699444879 10818784732393925549167319)
            ·
              refine ⟨16228177098590888323750979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10818784732393925549167319 16228177098590888323750979)
              ·
                refine ⟨24342265647886332485626469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16228177098590888323750979 24342265647886332485626469)
                ·
                  refine ⟨4564174808978687341054963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24342265647886332485626469 4564174808978687341054963)
                  ·
                    refine ⟨6846262213468031011582445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4564174808978687341054963 6846262213468031011582445)
                    ·
                      refine ⟨2567348330050511629343417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846262213468031011582445 2567348330050511629343417)
                      ·
                        rfl

theorem cell23_4999893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_4999893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4999893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4999893 prefixEnd_4999893 := by exact prefixLift 4999893
  have htrace : WordTrace (prefixWord ++ tailWord_4999893) baseStart_4999893 baseEnd_4999893 := by
    simpa [prefixWord, tailWord_4999893, baseEnd_4999893] using wordTrace_append hprefix tailTrace_4999893
  have hstable : (prefixWord ++ tailWord_4999893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4999893).length < 2 ^ (prefixWord ++ tailWord_4999893).sum := by decide
  have hdescent : baseEnd_4999893 < baseStart_4999893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4999893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000073 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 3]
def baseStart_5000073 : Nat := 118140960795 + 5000073 * 2 ^ 59
def prefixEnd_5000073 : Nat := 4983230072969 + 3 ^ 40 * 5000073 * 2
def baseEnd_5000073 : Nat := 2567440756568320925092589

theorem tailTrace_5000073 : CollatzResearch.WordTrace tailWord_5000073 prefixEnd_5000073 2567440756568320925092589 := by
  unfold tailWord_5000073
  simp only [CollatzResearch.WordTrace]
  refine ⟨182367644414596940327516873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121578429609731293551677915 182367644414596940327516873)
  ·
    refine ⟨136775733310947705245637655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182367644414596940327516873 136775733310947705245637655)
    ·
      refine ⟨205163599966421557868456483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136775733310947705245637655 205163599966421557868456483)
      ·
        refine ⟨307745399949632336802684725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205163599966421557868456483 307745399949632336802684725)
        ·
          refine ⟨28851131245278031575251693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 307745399949632336802684725 28851131245278031575251693)
          ·
            refine ⟨10819174216979261840719385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28851131245278031575251693 10819174216979261840719385)
            ·
              refine ⟨8114380662734446380539539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10819174216979261840719385 8114380662734446380539539)
              ·
                refine ⟨12171570994101669570809309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8114380662734446380539539 12171570994101669570809309)
                ·
                  refine ⟨4564339122788126089053491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12171570994101669570809309 4564339122788126089053491)
                  ·
                    refine ⟨6846508684182189133580237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4564339122788126089053491 6846508684182189133580237)
                    ·
                      refine ⟨2567440756568320925092589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846508684182189133580237 2567440756568320925092589)
                      ·
                        rfl

theorem cell23_5000073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3, 1, 3].length) (baseStart_5000073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000073 prefixEnd_5000073 := by exact prefixLift 5000073
  have htrace : WordTrace (prefixWord ++ tailWord_5000073) baseStart_5000073 baseEnd_5000073 := by
    simpa [prefixWord, tailWord_5000073, baseEnd_5000073] using wordTrace_append hprefix tailTrace_5000073
  have hstable : (prefixWord ++ tailWord_5000073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000073).length < 2 ^ (prefixWord ++ tailWord_5000073).sum := by decide
  have hdescent : baseEnd_5000073 < baseStart_5000073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000096 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4]
def baseStart_5000096 : Nat := 118140960795 + 5000096 * 2 ^ 59
def prefixEnd_5000096 : Nat := 4983230072969 + 3 ^ 40 * 5000096 * 2
def baseEnd_5000096 : Nat := 2567452566623374335104983

theorem tailTrace_5000096 : CollatzResearch.WordTrace tailWord_5000096 prefixEnd_5000096 2567452566623374335104983 := by
  unfold tailWord_5000096
  simp only [CollatzResearch.WordTrace]
  refine ⟨91184241646756807627802071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121578988862342410170402761 91184241646756807627802071)
  ·
    refine ⟨136776362470135211441703107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91184241646756807627802071 136776362470135211441703107)
    ·
      refine ⟨205164543705202817162554661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136776362470135211441703107 205164543705202817162554661)
      ·
        refine ⟨38468351944725528217978999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205164543705202817162554661 38468351944725528217978999)
        ·
          refine ⟨57702527917088292326968499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38468351944725528217978999 57702527917088292326968499)
          ·
            refine ⟨86553791875632438490452749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57702527917088292326968499 86553791875632438490452749)
            ·
              refine ⟨32457671953362164433919781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86553791875632438490452749 32457671953362164433919781)
              ·
                refine ⟨6085813491255405831359959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32457671953362164433919781 6085813491255405831359959)
                ·
                  refine ⟨9128720236883108747039939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6085813491255405831359959 9128720236883108747039939)
                  ·
                    refine ⟨13693080355324663120559909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9128720236883108747039939 13693080355324663120559909)
                    ·
                      refine ⟨2567452566623374335104983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13693080355324663120559909 2567452566623374335104983)
                      ·
                        rfl

theorem cell23_5000096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_5000096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000096 prefixEnd_5000096 := by exact prefixLift 5000096
  have htrace : WordTrace (prefixWord ++ tailWord_5000096) baseStart_5000096 baseEnd_5000096 := by
    simpa [prefixWord, tailWord_5000096, baseEnd_5000096] using wordTrace_append hprefix tailTrace_5000096
  have hstable : (prefixWord ++ tailWord_5000096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000096).length < 2 ^ (prefixWord ++ tailWord_5000096).sum := by decide
  have hdescent : baseEnd_5000096 < baseStart_5000096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000136 : List Nat := [2, 1, 3, 1, 5, 1, 2, 8]
def baseStart_5000136 : Nat := 118140960795 + 5000136 * 2 ^ 59
def prefixEnd_5000136 : Nat := 4983230072969 + 3 ^ 40 * 5000136 * 2
def baseEnd_5000136 : Nat := 95091596512946451059437

theorem tailTrace_5000136 : CollatzResearch.WordTrace tailWord_5000136 prefixEnd_5000136 95091596512946451059437 := by
  unfold tailWord_5000136
  simp only [CollatzResearch.WordTrace]
  refine ⟨91184971106684351043530131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121579961475579134724706841 91184971106684351043530131)
  ·
    refine ⟨136777456660026526565295197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91184971106684351043530131 136777456660026526565295197)
    ·
      refine ⟨51291546247509947461985699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136777456660026526565295197 51291546247509947461985699)
      ·
        refine ⟨76937319371264921192978549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51291546247509947461985699 76937319371264921192978549)
        ·
          refine ⟨7212873691056086361841739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76937319371264921192978549 7212873691056086361841739)
          ·
            refine ⟨10819310536584129542762609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212873691056086361841739 10819310536584129542762609)
            ·
              refine ⟨8114482902438097157071957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10819310536584129542762609 8114482902438097157071957)
              ·
                refine ⟨95091596512946451059437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8114482902438097157071957 95091596512946451059437)
                ·
                  rfl

theorem cell23_5000136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 8].length) (baseStart_5000136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000136 prefixEnd_5000136 := by exact prefixLift 5000136
  have htrace : WordTrace (prefixWord ++ tailWord_5000136) baseStart_5000136 baseEnd_5000136 := by
    simpa [prefixWord, tailWord_5000136, baseEnd_5000136] using wordTrace_append hprefix tailTrace_5000136
  have hstable : (prefixWord ++ tailWord_5000136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000136).length < 2 ^ (prefixWord ++ tailWord_5000136).sum := by decide
  have hdescent : baseEnd_5000136 < baseStart_5000136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000150 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_5000150 : Nat := 118140960795 + 5000150 * 2 ^ 59
def prefixEnd_5000150 : Nat := 4983230072969 + 3 ^ 40 * 5000150 * 2
def baseEnd_5000150 : Nat := 2567480294578717123829735

theorem tailTrace_5000150 : CollatzResearch.WordTrace tailWord_5000150 prefixEnd_5000150 2567480294578717123829735 := by
  unfold tailWord_5000150
  simp only [CollatzResearch.WordTrace]
  refine ⟨11398153302207373904879369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121580301890211988318713269 11398153302207373904879369)
  ·
    refine ⟨8548614976655530428659527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11398153302207373904879369 8548614976655530428659527)
    ·
      refine ⟨12822922464983295642989291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8548614976655530428659527 12822922464983295642989291)
      ·
        refine ⟨19234383697474943464483937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12822922464983295642989291 19234383697474943464483937)
        ·
          refine ⟨14425787773106207598362953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19234383697474943464483937 14425787773106207598362953)
          ·
            refine ⟨10819340829829655698772215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14425787773106207598362953 10819340829829655698772215)
            ·
              refine ⟨16229011244744483548158323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10819340829829655698772215 16229011244744483548158323)
              ·
                refine ⟨24343516867116725322237485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16229011244744483548158323 24343516867116725322237485)
                ·
                  refine ⟨9128818825168771995839057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24343516867116725322237485 9128818825168771995839057)
                  ·
                    refine ⟨6846614118876578996879293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9128818825168771995839057 6846614118876578996879293)
                    ·
                      refine ⟨2567480294578717123829735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846614118876578996879293 2567480294578717123829735)
                      ·
                        rfl

theorem cell23_5000150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_5000150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000150 prefixEnd_5000150 := by exact prefixLift 5000150
  have htrace : WordTrace (prefixWord ++ tailWord_5000150) baseStart_5000150 baseEnd_5000150 := by
    simpa [prefixWord, tailWord_5000150, baseEnd_5000150] using wordTrace_append hprefix tailTrace_5000150
  have hstable : (prefixWord ++ tailWord_5000150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000150).length < 2 ^ (prefixWord ++ tailWord_5000150).sum := by decide
  have hdescent : baseEnd_5000150 < baseStart_5000150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000169 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_5000169 : Nat := 118140960795 + 5000169 * 2 ^ 59
def prefixEnd_5000169 : Nat := 4983230072969 + 3 ^ 40 * 5000169 * 2
def baseEnd_5000169 : Nat := 2567490050711152549492147

theorem tailTrace_5000169 : CollatzResearch.WordTrace tailWord_5000169 prefixEnd_5000169 2567490050711152549492147 := by
  unfold tailWord_5000169
  simp only [CollatzResearch.WordTrace]
  refine ⟨182371145822249148723011561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121580763881499432482007707 182371145822249148723011561)
  ·
    refine ⟨136778359366686861542258671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182371145822249148723011561 136778359366686861542258671)
    ·
      refine ⟨205167539050030292313388007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136778359366686861542258671 205167539050030292313388007)
      ·
        refine ⟨307751308575045438470082011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205167539050030292313388007 307751308575045438470082011)
        ·
          refine ⟨461626962862568157705123017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307751308575045438470082011 461626962862568157705123017)
          ·
            refine ⟨346220222146926118278842263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461626962862568157705123017 346220222146926118278842263)
            ·
              refine ⟨519330333220389177418263395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346220222146926118278842263 519330333220389177418263395)
              ·
                refine ⟨778995499830583766127395093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519330333220389177418263395 778995499830583766127395093)
                ·
                  refine ⟨36515414054558614037221645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 778995499830583766127395093 36515414054558614037221645)
                  ·
                    refine ⟨13693280270459480263958117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36515414054558614037221645 13693280270459480263958117)
                    ·
                      refine ⟨2567490050711152549492147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13693280270459480263958117 2567490050711152549492147)
                      ·
                        rfl

theorem cell23_5000169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_5000169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000169 prefixEnd_5000169 := by exact prefixLift 5000169
  have htrace : WordTrace (prefixWord ++ tailWord_5000169) baseStart_5000169 baseEnd_5000169 := by
    simpa [prefixWord, tailWord_5000169, baseEnd_5000169] using wordTrace_append hprefix tailTrace_5000169
  have hstable : (prefixWord ++ tailWord_5000169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000169).length < 2 ^ (prefixWord ++ tailWord_5000169).sum := by decide
  have hdescent : baseEnd_5000169 < baseStart_5000169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000181 : List Nat := [1, 3, 5, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5000181 : Nat := 118140960795 + 5000181 * 2 ^ 59
def prefixEnd_5000181 : Nat := 4983230072969 + 3 ^ 40 * 5000181 * 2
def baseEnd_5000181 : Nat := 2567496212479006502542093

theorem tailTrace_5000181 : CollatzResearch.WordTrace tailWord_5000181 prefixEnd_5000181 2567496212479006502542093 := by
  unfold tailWord_5000181
  simp only [CollatzResearch.WordTrace]
  refine ⟨182371583498205674772448397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121581055665470449848298931 182371583498205674772448397)
  ·
    refine ⟨68389343811827128039668149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182371583498205674772448397 68389343811827128039668149)
    ·
      refine ⟨6411500982358793253718889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68389343811827128039668149 6411500982358793253718889)
      ·
        refine ⟨4808625736769094940289167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6411500982358793253718889 4808625736769094940289167)
        ·
          refine ⟨7212938605153642410433751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808625736769094940289167 7212938605153642410433751)
          ·
            refine ⟨10819407907730463615650627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212938605153642410433751 10819407907730463615650627)
            ·
              refine ⟨16229111861595695423475941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10819407907730463615650627 16229111861595695423475941)
              ·
                refine ⟨3042958474049192891901739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16229111861595695423475941 3042958474049192891901739)
                ·
                  refine ⟨4564437711073789337852609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3042958474049192891901739 4564437711073789337852609)
                  ·
                    refine ⟨3423328283305342003389457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564437711073789337852609 3423328283305342003389457)
                    ·
                      refine ⟨2567496212479006502542093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423328283305342003389457 2567496212479006502542093)
                      ·
                        rfl

theorem cell23_5000181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5000181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000181 prefixEnd_5000181 := by exact prefixLift 5000181
  have htrace : WordTrace (prefixWord ++ tailWord_5000181) baseStart_5000181 baseEnd_5000181 := by
    simpa [prefixWord, tailWord_5000181, baseEnd_5000181] using wordTrace_append hprefix tailTrace_5000181
  have hstable : (prefixWord ++ tailWord_5000181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000181).length < 2 ^ (prefixWord ++ tailWord_5000181).sum := by decide
  have hdescent : baseEnd_5000181 < baseStart_5000181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000203 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 1, 4, 2]
def baseStart_5000203 : Nat := 118140960795 + 5000203 * 2 ^ 59
def prefixEnd_5000203 : Nat := 4983230072969 + 3 ^ 40 * 5000203 * 2
def baseEnd_5000203 : Nat := 2567507509053405416466991

theorem tailTrace_5000203 : CollatzResearch.WordTrace tailWord_5000203 prefixEnd_5000203 2567507509053405416466991 := by
  unfold tailWord_5000203
  simp only [CollatzResearch.WordTrace]
  refine ⟨182372385904125972529749263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121581590602750648353166175 182372385904125972529749263)
  ·
    refine ⟨273558578856188958794623895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182372385904125972529749263 273558578856188958794623895)
    ·
      refine ⟨410337868284283438191935843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273558578856188958794623895 410337868284283438191935843)
      ·
        refine ⟨615506802426425157287903765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410337868284283438191935843 615506802426425157287903765)
        ·
          refine ⟨28851881363738679247870489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 615506802426425157287903765 28851881363738679247870489)
          ·
            refine ⟨21638911022804009435902867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28851881363738679247870489 21638911022804009435902867)
            ·
              refine ⟨32458366534206014153854301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21638911022804009435902867 32458366534206014153854301)
              ·
                refine ⟨12171887450327255307695363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32458366534206014153854301 12171887450327255307695363)
                ·
                  refine ⟨18257831175490882961543045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12171887450327255307695363 18257831175490882961543045)
                  ·
                    refine ⟨3423343345404540555289321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18257831175490882961543045 3423343345404540555289321)
                    ·
                      refine ⟨2567507509053405416466991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423343345404540555289321 2567507509053405416466991)
                      ·
                        rfl

theorem cell23_5000203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 4, 2].length) (baseStart_5000203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000203 prefixEnd_5000203 := by exact prefixLift 5000203
  have htrace : WordTrace (prefixWord ++ tailWord_5000203) baseStart_5000203 baseEnd_5000203 := by
    simpa [prefixWord, tailWord_5000203, baseEnd_5000203] using wordTrace_append hprefix tailTrace_5000203
  have hstable : (prefixWord ++ tailWord_5000203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000203).length < 2 ^ (prefixWord ++ tailWord_5000203).sum := by decide
  have hdescent : baseEnd_5000203 < baseStart_5000203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000236 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_5000236 : Nat := 118140960795 + 5000236 * 2 ^ 59
def prefixEnd_5000236 : Nat := 4983230072969 + 3 ^ 40 * 5000236 * 2
def baseEnd_5000236 : Nat := 2567524453915003787354339

theorem tailTrace_5000236 : CollatzResearch.WordTrace tailWord_5000236 prefixEnd_5000236 2567524453915003787354339 := by
  unfold tailWord_5000236
  simp only [CollatzResearch.WordTrace]
  refine ⟨91186794756503209582850281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121582393008670946110467041 91186794756503209582850281)
  ·
    refine ⟨68390096067377407187137711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91186794756503209582850281 68390096067377407187137711)
    ·
      refine ⟨102585144101066110780706567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68390096067377407187137711 102585144101066110780706567)
      ·
        refine ⟨153877716151599166171059851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102585144101066110780706567 153877716151599166171059851)
        ·
          refine ⟨230816574227398749256589777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153877716151599166171059851 230816574227398749256589777)
          ·
            refine ⟨173112430670549061942442333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230816574227398749256589777 173112430670549061942442333)
            ·
              refine ⟨64917161501455898228415875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173112430670549061942442333 64917161501455898228415875)
              ·
                refine ⟨97375742252183847342623813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64917161501455898228415875 97375742252183847342623813)
                ·
                  refine ⟨18257951672284471376741965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97375742252183847342623813 18257951672284471376741965)
                  ·
                    refine ⟨6846731877106676766278237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18257951672284471376741965 6846731877106676766278237)
                    ·
                      refine ⟨2567524453915003787354339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846731877106676766278237 2567524453915003787354339)
                      ·
                        rfl

theorem cell23_5000236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_5000236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000236 prefixEnd_5000236 := by exact prefixLift 5000236
  have htrace : WordTrace (prefixWord ++ tailWord_5000236) baseStart_5000236 baseEnd_5000236 := by
    simpa [prefixWord, tailWord_5000236, baseEnd_5000236] using wordTrace_append hprefix tailTrace_5000236
  have hstable : (prefixWord ++ tailWord_5000236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000236).length < 2 ^ (prefixWord ++ tailWord_5000236).sum := by decide
  have hdescent : baseEnd_5000236 < baseStart_5000236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000253 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_5000253 : Nat := 118140960795 + 5000253 * 2 ^ 59
def prefixEnd_5000253 : Nat := 4983230072969 + 3 ^ 40 * 5000253 * 2
def baseEnd_5000253 : Nat := 2567533183086130220841761

theorem tailTrace_5000253 : CollatzResearch.WordTrace tailWord_5000253 prefixEnd_5000253 2567533183086130220841761 := by
  unfold tailWord_5000253
  simp only [CollatzResearch.WordTrace]
  refine ⟨182374209553944831069069413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121582806369296554046046275 182374209553944831069069413)
  ·
    refine ⟨34195164291364655825450515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182374209553944831069069413 34195164291364655825450515)
    ·
      refine ⟨51292746437046983738175773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34195164291364655825450515 51292746437046983738175773)
      ·
        refine ⟨19234779913892618901815915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51292746437046983738175773 19234779913892618901815915)
        ·
          refine ⟨28852169870838928352723873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19234779913892618901815915 28852169870838928352723873)
          ·
            refine ⟨21639127403129196264542905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28852169870838928352723873 21639127403129196264542905)
            ·
              refine ⟨16229345552346897198407179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21639127403129196264542905 16229345552346897198407179)
              ·
                refine ⟨24344018328520345797610769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16229345552346897198407179 24344018328520345797610769)
                ·
                  refine ⟨18258013746390259348208077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24344018328520345797610769 18258013746390259348208077)
                  ·
                    refine ⟨6846755154896347255578029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18258013746390259348208077 6846755154896347255578029)
                    ·
                      refine ⟨2567533183086130220841761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846755154896347255578029 2567533183086130220841761)
                      ·
                        rfl

theorem cell23_5000253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_5000253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000253 prefixEnd_5000253 := by exact prefixLift 5000253
  have htrace : WordTrace (prefixWord ++ tailWord_5000253) baseStart_5000253 baseEnd_5000253 := by
    simpa [prefixWord, tailWord_5000253, baseEnd_5000253] using wordTrace_append hprefix tailTrace_5000253
  have hstable : (prefixWord ++ tailWord_5000253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000253).length < 2 ^ (prefixWord ++ tailWord_5000253).sum := by decide
  have hdescent : baseEnd_5000253 < baseStart_5000253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000290 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_5000290 : Nat := 118140960795 + 5000290 * 2 ^ 59
def prefixEnd_5000290 : Nat := 4983230072969 + 3 ^ 40 * 5000290 * 2
def baseEnd_5000290 : Nat := 855850727290115525359697

theorem tailTrace_5000290 : CollatzResearch.WordTrace tailWord_5000290 prefixEnd_5000290 855850727290115525359697 := by
  unfold tailWord_5000290
  simp only [CollatzResearch.WordTrace]
  refine ⟨45593889763702696597041581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121583706036540524258777549 45593889763702696597041581)
  ·
    refine ⟨17097708661388511223890593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45593889763702696597041581 17097708661388511223890593)
    ·
      refine ⟨12823281496041383417917945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17097708661388511223890593 12823281496041383417917945)
      ·
        refine ⟨9617461122031037563438459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12823281496041383417917945 9617461122031037563438459)
        ·
          refine ⟨14426191683046556345157689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9617461122031037563438459 14426191683046556345157689)
          ·
            refine ⟨10819643762284917258868267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14426191683046556345157689 10819643762284917258868267)
            ·
              refine ⟨16229465643427375888302401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10819643762284917258868267 16229465643427375888302401)
              ·
                refine ⟨12172099232570531916226801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16229465643427375888302401 12172099232570531916226801)
                ·
                  refine ⟨9129074424427898937170101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12172099232570531916226801 9129074424427898937170101)
                  ·
                    refine ⟨855850727290115525359697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9129074424427898937170101 855850727290115525359697)
                    ·
                      rfl

theorem cell23_5000290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_5000290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000290 prefixEnd_5000290 := by exact prefixLift 5000290
  have htrace : WordTrace (prefixWord ++ tailWord_5000290) baseStart_5000290 baseEnd_5000290 := by
    simpa [prefixWord, tailWord_5000290, baseEnd_5000290] using wordTrace_append hprefix tailTrace_5000290
  have hstable : (prefixWord ++ tailWord_5000290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000290).length < 2 ^ (prefixWord ++ tailWord_5000290).sum := by decide
  have hdescent : baseEnd_5000290 < baseStart_5000290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000293 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_5000293 : Nat := 118140960795 + 5000293 * 2 ^ 59
def prefixEnd_5000293 : Nat := 4983230072969 + 3 ^ 40 * 5000293 * 2
def baseEnd_5000293 : Nat := 2567553722312310064341577

theorem tailTrace_5000293 : CollatzResearch.WordTrace tailWord_5000293 prefixEnd_5000293 2567553722312310064341577 := by
  unfold tailWord_5000293
  simp only [CollatzResearch.WordTrace]
  refine ⟨182375668473799917900525533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121583778982533278600350355 182375668473799917900525533)
  ·
    refine ⟨68390875677674969212697075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182375668473799917900525533 68390875677674969212697075)
    ·
      refine ⟨102586313516512453819045613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68390875677674969212697075 102586313516512453819045613)
      ·
        refine ⟨38469867568692170182142105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102586313516512453819045613 38469867568692170182142105)
        ·
          refine ⟨28852400676519127636606579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38469867568692170182142105 28852400676519127636606579)
          ·
            refine ⟨43278601014778691454909869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28852400676519127636606579 43278601014778691454909869)
            ·
              refine ⟨16229475380542009295591201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43278601014778691454909869 16229475380542009295591201)
              ·
                refine ⟨12172106535406506971693401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16229475380542009295591201 12172106535406506971693401)
                ·
                  refine ⟨9129079901554880228770051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12172106535406506971693401 9129079901554880228770051)
                  ·
                    refine ⟨13693619852332320343155077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9129079901554880228770051 13693619852332320343155077)
                    ·
                      refine ⟨2567553722312310064341577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13693619852332320343155077 2567553722312310064341577)
                      ·
                        rfl

theorem cell23_5000293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_5000293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000293 prefixEnd_5000293 := by exact prefixLift 5000293
  have htrace : WordTrace (prefixWord ++ tailWord_5000293) baseStart_5000293 baseEnd_5000293 := by
    simpa [prefixWord, tailWord_5000293, baseEnd_5000293] using wordTrace_append hprefix tailTrace_5000293
  have hstable : (prefixWord ++ tailWord_5000293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000293).length < 2 ^ (prefixWord ++ tailWord_5000293).sum := by decide
  have hdescent : baseEnd_5000293 < baseStart_5000293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000310 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_5000310 : Nat := 118140960795 + 5000310 * 2 ^ 59
def prefixEnd_5000310 : Nat := 4983230072969 + 3 ^ 40 * 5000310 * 2
def baseEnd_5000310 : Nat := 2567562451483436497828999

theorem tailTrace_5000310 : CollatzResearch.WordTrace tailWord_5000310 prefixEnd_5000310 2567562451483436497828999 := by
  unfold tailWord_5000310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11398518032171145612743399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121584192343158886535929589 11398518032171145612743399)
  ·
    refine ⟨17097777048256718419115099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11398518032171145612743399 17097777048256718419115099)
    ·
      refine ⟨25646665572385077628672649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17097777048256718419115099 25646665572385077628672649)
      ·
        refine ⟨19234999179288808221504487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25646665572385077628672649 19234999179288808221504487)
        ·
          refine ⟨28852498768933212332256731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19234999179288808221504487 28852498768933212332256731)
          ·
            refine ⟨43278748153399818498385097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28852498768933212332256731 43278748153399818498385097)
            ·
              refine ⟨32459061115049863873788823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43278748153399818498385097 32459061115049863873788823)
              ·
                refine ⟨48688591672574795810683235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32459061115049863873788823 48688591672574795810683235)
                ·
                  refine ⟨73032887508862193716024853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48688591672574795810683235 73032887508862193716024853)
                  ·
                    refine ⟨3423416601977915330438665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73032887508862193716024853 3423416601977915330438665)
                    ·
                      refine ⟨2567562451483436497828999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423416601977915330438665 2567562451483436497828999)
                      ·
                        rfl

theorem cell23_5000310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_5000310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000310 prefixEnd_5000310 := by exact prefixLift 5000310
  have htrace : WordTrace (prefixWord ++ tailWord_5000310) baseStart_5000310 baseEnd_5000310 := by
    simpa [prefixWord, tailWord_5000310, baseEnd_5000310] using wordTrace_append hprefix tailTrace_5000310
  have hstable : (prefixWord ++ tailWord_5000310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000310).length < 2 ^ (prefixWord ++ tailWord_5000310).sum := by decide
  have hdescent : baseEnd_5000310 < baseStart_5000310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000330 : List Nat := [3, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_5000330 : Nat := 118140960795 + 5000330 * 2 ^ 59
def prefixEnd_5000330 : Nat := 4983230072969 + 3 ^ 40 * 5000330 * 2
def baseEnd_5000330 : Nat := 2567572721096526419578907

theorem tailTrace_5000330 : CollatzResearch.WordTrace tailWord_5000330 prefixEnd_5000330 2567572721096526419578907 := by
  unfold tailWord_5000330
  simp only [CollatzResearch.WordTrace]
  refine ⟨45594254493666468304905611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121584678649777248813081629 45594254493666468304905611)
  ·
    refine ⟨68391381740499702457358417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45594254493666468304905611 68391381740499702457358417)
    ·
      refine ⟨51293536305374776843018813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68391381740499702457358417 51293536305374776843018813)
      ·
        refine ⟨19235076114515541316132055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51293536305374776843018813 19235076114515541316132055)
        ·
          refine ⟨28852614171773311974198083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19235076114515541316132055 28852614171773311974198083)
          ·
            refine ⟨43278921257659967961297125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28852614171773311974198083 43278921257659967961297125)
            ·
              refine ⟨8114797735811243992743211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43278921257659967961297125 8114797735811243992743211)
              ·
                refine ⟨12172196603716865989114817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8114797735811243992743211 12172196603716865989114817)
                ·
                  refine ⟨9129147452787649491836113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12172196603716865989114817 9129147452787649491836113)
                  ·
                    refine ⟨6846860589590737118877085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9129147452787649491836113 6846860589590737118877085)
                    ·
                      refine ⟨2567572721096526419578907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846860589590737118877085 2567572721096526419578907)
                      ·
                        rfl

theorem cell23_5000330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_5000330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000330 prefixEnd_5000330 := by exact prefixLift 5000330
  have htrace : WordTrace (prefixWord ++ tailWord_5000330) baseStart_5000330 baseEnd_5000330 := by
    simpa [prefixWord, tailWord_5000330, baseEnd_5000330] using wordTrace_append hprefix tailTrace_5000330
  have hstable : (prefixWord ++ tailWord_5000330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000330).length < 2 ^ (prefixWord ++ tailWord_5000330).sum := by decide
  have hdescent : baseEnd_5000330 < baseStart_5000330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000350 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_5000350 : Nat := 118140960795 + 5000350 * 2 ^ 59
def prefixEnd_5000350 : Nat := 4983230072969 + 3 ^ 40 * 5000350 * 2
def baseEnd_5000350 : Nat := 285286998967735149036535

theorem tailTrace_5000350 : CollatzResearch.WordTrace tailWord_5000350 prefixEnd_5000350 285286998967735149036535 := by
  unfold tailWord_5000350
  simp only [CollatzResearch.WordTrace]
  refine ⟨22797218429324177079418813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121585164956395611090233669 22797218429324177079418813)
  ·
    refine ⟨8548956910996566404782055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22797218429324177079418813 8548956910996566404782055)
    ·
      refine ⟨12823435366494849607173083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8548956910996566404782055 12823435366494849607173083)
      ·
        refine ⟨19235153049742274410759625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12823435366494849607173083 19235153049742274410759625)
        ·
          refine ⟨14426364787306705808069719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19235153049742274410759625 14426364787306705808069719)
          ·
            refine ⟨21639547180960058712104579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14426364787306705808069719 21639547180960058712104579)
            ·
              refine ⟨32459320771440088068156869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21639547180960058712104579 32459320771440088068156869)
              ·
                refine ⟨6086122644645016512779413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32459320771440088068156869 6086122644645016512779413)
                ·
                  refine ⟨285286998967735149036535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6086122644645016512779413 285286998967735149036535)
                  ·
                    rfl

theorem cell23_5000350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_5000350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000350 prefixEnd_5000350 := by exact prefixLift 5000350
  have htrace : WordTrace (prefixWord ++ tailWord_5000350) baseStart_5000350 baseEnd_5000350 := by
    simpa [prefixWord, tailWord_5000350, baseEnd_5000350] using wordTrace_append hprefix tailTrace_5000350
  have hstable : (prefixWord ++ tailWord_5000350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000350).length < 2 ^ (prefixWord ++ tailWord_5000350).sum := by decide
  have hdescent : baseEnd_5000350 < baseStart_5000350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000354 : List Nat := [3, 3, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_5000354 : Nat := 118140960795 + 5000354 * 2 ^ 59
def prefixEnd_5000354 : Nat := 4983230072969 + 3 ^ 40 * 5000354 * 2
def baseEnd_5000354 : Nat := 855861681544078108559599

theorem tailTrace_5000354 : CollatzResearch.WordTrace tailWord_5000354 prefixEnd_5000354 855861681544078108559599 := by
  unfold tailWord_5000354
  simp only [CollatzResearch.WordTrace]
  refine ⟨45594473331644731329624029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121585262217719283545664077 45594473331644731329624029)
  ·
    refine ⟨17097927499366774248609011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45594473331644731329624029 17097927499366774248609011)
    ·
      refine ⟨25646891249050161372913517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17097927499366774248609011 25646891249050161372913517)
      ·
        refine ⟨9617584218393810514842569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25646891249050161372913517 9617584218393810514842569)
        ·
          refine ⟨7213188163795357886131927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9617584218393810514842569 7213188163795357886131927)
          ·
            refine ⟨10819782245693036829197891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7213188163795357886131927 10819782245693036829197891)
            ·
              refine ⟨16229673368539555243796837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10819782245693036829197891 16229673368539555243796837)
              ·
                refine ⟨3043063756601166608211907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16229673368539555243796837 3043063756601166608211907)
                ·
                  refine ⟨4564595634901749912317861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043063756601166608211907 4564595634901749912317861)
                  ·
                    refine ⟨855861681544078108559599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564595634901749912317861 855861681544078108559599)
                    ·
                      rfl

theorem cell23_5000354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_5000354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000354 prefixEnd_5000354 := by exact prefixLift 5000354
  have htrace : WordTrace (prefixWord ++ tailWord_5000354) baseStart_5000354 baseEnd_5000354 := by
    simpa [prefixWord, tailWord_5000354, baseEnd_5000354] using wordTrace_append hprefix tailTrace_5000354
  have hstable : (prefixWord ++ tailWord_5000354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000354).length < 2 ^ (prefixWord ++ tailWord_5000354).sum := by decide
  have hdescent : baseEnd_5000354 < baseStart_5000354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000383 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_5000383 : Nat := 118140960795 + 5000383 * 2 ^ 59
def prefixEnd_5000383 : Nat := 4983230072969 + 3 ^ 40 * 5000383 * 2
def baseEnd_5000383 : Nat := 2567599935571214712216163

theorem tailTrace_5000383 : CollatzResearch.WordTrace tailWord_5000383 prefixEnd_5000383 2567599935571214712216163 := by
  unfold tailWord_5000383
  simp only [CollatzResearch.WordTrace]
  refine ⟨182378951043473863271301803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121585967362315908847534535 182378951043473863271301803)
  ·
    refine ⟨273568426565210794906952705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182378951043473863271301803 273568426565210794906952705)
    ·
      refine ⟨205176319923908096180214529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273568426565210794906952705 205176319923908096180214529)
      ·
        refine ⟨153882239942931072135160897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205176319923908096180214529 153882239942931072135160897)
        ·
          refine ⟨115411679957198304101370673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153882239942931072135160897 115411679957198304101370673)
          ·
            refine ⟨86558759967898728076028005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115411679957198304101370673 86558759967898728076028005)
            ·
              refine ⟨16229767493981011514255251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86558759967898728076028005 16229767493981011514255251)
              ·
                refine ⟨24344651240971517271382877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16229767493981011514255251 24344651240971517271382877)
                ·
                  refine ⟨9129244215364318976768579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24344651240971517271382877 9129244215364318976768579)
                  ·
                    refine ⟨13693866323046478465152869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9129244215364318976768579 13693866323046478465152869)
                    ·
                      refine ⟨2567599935571214712216163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13693866323046478465152869 2567599935571214712216163)
                      ·
                        rfl

theorem cell23_5000383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_5000383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000383 prefixEnd_5000383 := by exact prefixLift 5000383
  have htrace : WordTrace (prefixWord ++ tailWord_5000383) baseStart_5000383 baseEnd_5000383 := by
    simpa [prefixWord, tailWord_5000383, baseEnd_5000383] using wordTrace_append hprefix tailTrace_5000383
  have hstable : (prefixWord ++ tailWord_5000383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000383).length < 2 ^ (prefixWord ++ tailWord_5000383).sum := by decide
  have hdescent : baseEnd_5000383 < baseStart_5000383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000394 : List Nat := [3, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_5000394 : Nat := 118140960795 + 5000394 * 2 ^ 59
def prefixEnd_5000394 : Nat := 4983230072969 + 3 ^ 40 * 5000394 * 2
def baseEnd_5000394 : Nat := 2567605583858414169178613

theorem tailTrace_5000394 : CollatzResearch.WordTrace tailWord_5000394 prefixEnd_5000394 2567605583858414169178613 := by
  unfold tailWord_5000394
  simp only [CollatzResearch.WordTrace]
  refine ⟨45594838061608503037488059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121586234830956008099968157 45594838061608503037488059)
  ·
    refine ⟨68392257092412754556232089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45594838061608503037488059 68392257092412754556232089)
    ·
      refine ⟨51294192819309565917174067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68392257092412754556232089 51294192819309565917174067)
      ·
        refine ⟨76941289228964348875761101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51294192819309565917174067 76941289228964348875761101)
        ·
          refine ⟨28852983460861630828410413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76941289228964348875761101 28852983460861630828410413)
          ·
            refine ⟨10819868797823111560653905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28852983460861630828410413 10819868797823111560653905)
            ·
              refine ⟨8114901598367333670490429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10819868797823111560653905 8114901598367333670490429)
              ·
                refine ⟨3043088099387750126433911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8114901598367333670490429 3043088099387750126433911)
                ·
                  refine ⟨4564632149081625189650867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043088099387750126433911 4564632149081625189650867)
                  ·
                    refine ⟨6846948223622437784476301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4564632149081625189650867 6846948223622437784476301)
                    ·
                      refine ⟨2567605583858414169178613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6846948223622437784476301 2567605583858414169178613)
                      ·
                        rfl

theorem cell23_5000394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_5000394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000394 prefixEnd_5000394 := by exact prefixLift 5000394
  have htrace : WordTrace (prefixWord ++ tailWord_5000394) baseStart_5000394 baseEnd_5000394 := by
    simpa [prefixWord, tailWord_5000394, baseEnd_5000394] using wordTrace_append hprefix tailTrace_5000394
  have hstable : (prefixWord ++ tailWord_5000394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000394).length < 2 ^ (prefixWord ++ tailWord_5000394).sum := by decide
  have hdescent : baseEnd_5000394 < baseStart_5000394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000417 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_5000417 : Nat := 118140960795 + 5000417 * 2 ^ 59
def prefixEnd_5000417 : Nat := 4983230072969 + 3 ^ 40 * 5000417 * 2
def baseEnd_5000417 : Nat := 2567617393913467579191007

theorem tailTrace_5000417 : CollatzResearch.WordTrace tailWord_5000417 prefixEnd_5000417 2567617393913467579191007 := by
  unfold tailWord_5000417
  simp only [CollatzResearch.WordTrace]
  refine ⟨182380191125350687078039505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121586794083567124718693003 182380191125350687078039505)
  ·
    refine ⟨136785143344013015308529629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182380191125350687078039505 136785143344013015308529629)
    ·
      refine ⟨51294428754004880740698611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136785143344013015308529629 51294428754004880740698611)
      ·
        refine ⟨76941643131007321111047917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51294428754004880740698611 76941643131007321111047917)
        ·
          refine ⟨28853116174127745416642969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76941643131007321111047917 28853116174127745416642969)
          ·
            refine ⟨21639837130595809062482227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28853116174127745416642969 21639837130595809062482227)
            ·
              refine ⟨32459755695893713593723341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21639837130595809062482227 32459755695893713593723341)
              ·
                refine ⟨12172408385960142597646253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32459755695893713593723341 12172408385960142597646253)
                ·
                  refine ⟨4564653144735053474117345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12172408385960142597646253 4564653144735053474117345)
                  ·
                    refine ⟨3423489858551290105588009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564653144735053474117345 3423489858551290105588009)
                    ·
                      refine ⟨2567617393913467579191007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423489858551290105588009 2567617393913467579191007)
                      ·
                        rfl

theorem cell23_5000417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_5000417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000417 prefixEnd_5000417 := by exact prefixLift 5000417
  have htrace : WordTrace (prefixWord ++ tailWord_5000417) baseStart_5000417 baseEnd_5000417 := by
    simpa [prefixWord, tailWord_5000417, baseEnd_5000417] using wordTrace_append hprefix tailTrace_5000417
  have hstable : (prefixWord ++ tailWord_5000417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000417).length < 2 ^ (prefixWord ++ tailWord_5000417).sum := by decide
  have hdescent : baseEnd_5000417 < baseStart_5000417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000427 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 2, 4]
def baseStart_5000427 : Nat := 118140960795 + 5000427 * 2 ^ 59
def prefixEnd_5000427 : Nat := 4983230072969 + 3 ^ 40 * 5000427 * 2
def baseEnd_5000427 : Nat := 855874176240004180021987

theorem tailTrace_5000427 : CollatzResearch.WordTrace tailWord_5000427 prefixEnd_5000427 855874176240004180021987 := by
  unfold tailWord_5000427
  simp only [CollatzResearch.WordTrace]
  refine ⟨182380555855314458785903535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121587037236876305857269023 182380555855314458785903535)
  ·
    refine ⟨273570833782971688178855303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182380555855314458785903535 273570833782971688178855303)
    ·
      refine ⟨410356250674457532268282955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273570833782971688178855303 410356250674457532268282955)
      ·
        refine ⟨615534376011686298402424433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410356250674457532268282955 615534376011686298402424433)
        ·
          refine ⟨461650782008764723801818325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615534376011686298402424433 461650782008764723801818325)
          ·
            refine ⟨10819940203330423214105117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 461650782008764723801818325 10819940203330423214105117)
            ·
              refine ⟨4057477576248908705289419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10819940203330423214105117 4057477576248908705289419)
              ·
                refine ⟨6086216364373363057934129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057477576248908705289419 6086216364373363057934129)
                ·
                  refine ⟨4564662273280022293450597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6086216364373363057934129 4564662273280022293450597)
                  ·
                    refine ⟨855874176240004180021987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564662273280022293450597 855874176240004180021987)
                    ·
                      rfl

theorem cell23_5000427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 2, 4].length) (baseStart_5000427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000427 prefixEnd_5000427 := by exact prefixLift 5000427
  have htrace : WordTrace (prefixWord ++ tailWord_5000427) baseStart_5000427 baseEnd_5000427 := by
    simpa [prefixWord, tailWord_5000427, baseEnd_5000427] using wordTrace_append hprefix tailTrace_5000427
  have hstable : (prefixWord ++ tailWord_5000427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000427).length < 2 ^ (prefixWord ++ tailWord_5000427).sum := by decide
  have hdescent : baseEnd_5000427 < baseStart_5000427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000430 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_5000430 : Nat := 118140960795 + 5000430 * 2 ^ 59
def prefixEnd_5000430 : Nat := 4983230072969 + 3 ^ 40 * 5000430 * 2
def baseEnd_5000430 : Nat := 2567624069161976028328447

theorem tailTrace_5000430 : CollatzResearch.WordTrace tailWord_5000430 prefixEnd_5000430 2567624069161976028328447 := by
  unfold tailWord_5000430
  simp only [CollatzResearch.WordTrace]
  refine ⟨22797583159287948787282843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121587110182869060198841829 22797583159287948787282843)
  ·
    refine ⟨34196374738931923180924265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22797583159287948787282843 34196374738931923180924265)
    ·
      refine ⟨25647281054198942385693199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34196374738931923180924265 25647281054198942385693199)
      ·
        refine ⟨38470921581298413578539799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25647281054198942385693199 38470921581298413578539799)
        ·
          refine ⟨57706382371947620367809699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38470921581298413578539799 57706382371947620367809699)
          ·
            refine ⟨86559573557921430551714549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57706382371947620367809699 86559573557921430551714549)
            ·
              refine ⟨8114960021055134114223239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86559573557921430551714549 8114960021055134114223239)
              ·
                refine ⟨12172440031582701171334859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8114960021055134114223239 12172440031582701171334859)
                ·
                  refine ⟨18258660047374051757002289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12172440031582701171334859 18258660047374051757002289)
                  ·
                    refine ⟨13693995035530538817751717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18258660047374051757002289 13693995035530538817751717)
                    ·
                      refine ⟨2567624069161976028328447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13693995035530538817751717 2567624069161976028328447)
                      ·
                        rfl

theorem cell23_5000430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_5000430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000430 prefixEnd_5000430 := by exact prefixLift 5000430
  have htrace : WordTrace (prefixWord ++ tailWord_5000430) baseStart_5000430 baseEnd_5000430 := by
    simpa [prefixWord, tailWord_5000430, baseEnd_5000430] using wordTrace_append hprefix tailTrace_5000430
  have hstable : (prefixWord ++ tailWord_5000430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000430).length < 2 ^ (prefixWord ++ tailWord_5000430).sum := by decide
  have hdescent : baseEnd_5000430 < baseStart_5000430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000451 : List Nat := [1, 1, 1, 3, 2, 6, 1, 3, 1, 2, 2]
def baseStart_5000451 : Nat := 118140960795 + 5000451 * 2 ^ 59
def prefixEnd_5000451 : Nat := 4983230072969 + 3 ^ 40 * 5000451 * 2
def baseEnd_5000451 : Nat := 2567634852255720446165851

theorem tailTrace_5000451 : CollatzResearch.WordTrace tailWord_5000451 prefixEnd_5000451 2567634852255720446165851 := by
  unfold tailWord_5000451
  simp only [CollatzResearch.WordTrace]
  refine ⟨182381431207227510884777207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121587620804818340589851471 182381431207227510884777207)
  ·
    refine ⟨273572146810841266327165811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182381431207227510884777207 273572146810841266327165811)
    ·
      refine ⟨410358220216261899490748717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273572146810841266327165811 410358220216261899490748717)
      ·
        refine ⟨153884332581098212309030769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410358220216261899490748717 153884332581098212309030769)
        ·
          refine ⟨115413249435823659231773077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153884332581098212309030769 115413249435823659231773077)
          ·
            refine ⟨5409996067304234026489363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115413249435823659231773077 5409996067304234026489363)
            ·
              refine ⟨8114994100956351039734045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5409996067304234026489363 8114994100956351039734045)
              ·
                refine ⟨3043122787858631639900267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8114994100956351039734045 3043122787858631639900267)
                ·
                  refine ⟨4564684181787947459850401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043122787858631639900267 4564684181787947459850401)
                  ·
                    refine ⟨3423513136340960594887801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564684181787947459850401 3423513136340960594887801)
                    ·
                      refine ⟨2567634852255720446165851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423513136340960594887801 2567634852255720446165851)
                      ·
                        rfl

theorem cell23_5000451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_5000451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000451 prefixEnd_5000451 := by exact prefixLift 5000451
  have htrace : WordTrace (prefixWord ++ tailWord_5000451) baseStart_5000451 baseEnd_5000451 := by
    simpa [prefixWord, tailWord_5000451, baseEnd_5000451] using wordTrace_append hprefix tailTrace_5000451
  have hstable : (prefixWord ++ tailWord_5000451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000451).length < 2 ^ (prefixWord ++ tailWord_5000451).sum := by decide
  have hdescent : baseEnd_5000451 < baseStart_5000451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000478 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5000478 : Nat := 118140960795 + 5000478 * 2 ^ 59
def prefixEnd_5000478 : Nat := 4983230072969 + 3 ^ 40 * 5000478 * 2
def baseEnd_5000478 : Nat := 855882905411130613509409

theorem tailTrace_5000478 : CollatzResearch.WordTrace tailWord_5000478 prefixEnd_5000478 855882905411130613509409 := by
  unfold tailWord_5000478
  simp only [CollatzResearch.WordTrace]
  refine ⟨22797801997266211812001261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121588277318753129664006725 22797801997266211812001261)
  ·
    refine ⟨8549175748974829429500473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22797801997266211812001261 8549175748974829429500473)
    ·
      refine ⟨6411881811731122072125355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8549175748974829429500473 6411881811731122072125355)
      ·
        refine ⟨9617822717596683108188033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411881811731122072125355 9617822717596683108188033)
        ·
          refine ⟨7213367038197512331141025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9617822717596683108188033 7213367038197512331141025)
          ·
            refine ⟨5410025278648134248355769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7213367038197512331141025 5410025278648134248355769)
            ·
              refine ⟨4057518958986100686266827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5410025278648134248355769 4057518958986100686266827)
              ·
                refine ⟨6086278438479151029400241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4057518958986100686266827 6086278438479151029400241)
                ·
                  refine ⟨4564708828859363272050181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6086278438479151029400241 4564708828859363272050181)
                  ·
                    refine ⟨855882905411130613509409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564708828859363272050181 855882905411130613509409)
                    ·
                      rfl

theorem cell23_5000478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5000478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000478 prefixEnd_5000478 := by exact prefixLift 5000478
  have htrace : WordTrace (prefixWord ++ tailWord_5000478) baseStart_5000478 baseEnd_5000478 := by
    simpa [prefixWord, tailWord_5000478, baseEnd_5000478] using wordTrace_append hprefix tailTrace_5000478
  have hstable : (prefixWord ++ tailWord_5000478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000478).length < 2 ^ (prefixWord ++ tailWord_5000478).sum := by decide
  have hdescent : baseEnd_5000478 < baseStart_5000478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000503 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_5000503 : Nat := 118140960795 + 5000503 * 2 ^ 59
def prefixEnd_5000503 : Nat := 4983230072969 + 3 ^ 40 * 5000503 * 2
def baseEnd_5000503 : Nat := 2567661553249754242715611

theorem tailTrace_5000503 : CollatzResearch.WordTrace tailWord_5000503 prefixEnd_5000503 2567661553249754242715611 := by
  unfold tailWord_5000503
  simp only [CollatzResearch.WordTrace]
  refine ⟨182383327803039123765670163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121588885202026082510446775 182383327803039123765670163)
  ·
    refine ⟨273574991704558685648505245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182383327803039123765670163 273574991704558685648505245)
    ·
      refine ⟨102590621889209507118189467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273574991704558685648505245 102590621889209507118189467)
      ·
        refine ⟨153885932833814260677284201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102590621889209507118189467 153885932833814260677284201)
        ·
          refine ⟨115414449625360695507963151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153885932833814260677284201 115414449625360695507963151)
          ·
            refine ⟨173121674438041043261944727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115414449625360695507963151 173121674438041043261944727)
            ·
              refine ⟨259682511657061564892917091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173121674438041043261944727 259682511657061564892917091)
              ·
                refine ⟨389523767485592347339375637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259682511657061564892917091 389523767485592347339375637)
                ·
                  refine ⟨18258926600887141281533233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 389523767485592347339375637 18258926600887141281533233)
                  ·
                    refine ⟨13694194950665355961149925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18258926600887141281533233 13694194950665355961149925)
                    ·
                      refine ⟨2567661553249754242715611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13694194950665355961149925 2567661553249754242715611)
                      ·
                        rfl

theorem cell23_5000503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_5000503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000503 prefixEnd_5000503 := by exact prefixLift 5000503
  have htrace : WordTrace (prefixWord ++ tailWord_5000503) baseStart_5000503 baseEnd_5000503 := by
    simpa [prefixWord, tailWord_5000503, baseEnd_5000503] using wordTrace_append hprefix tailTrace_5000503
  have hstable : (prefixWord ++ tailWord_5000503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000503).length < 2 ^ (prefixWord ++ tailWord_5000503).sum := by decide
  have hdescent : baseEnd_5000503 < baseStart_5000503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000510 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5000510 : Nat := 118140960795 + 5000510 * 2 ^ 59
def prefixEnd_5000510 : Nat := 4983230072969 + 3 ^ 40 * 5000510 * 2
def baseEnd_5000510 : Nat := 2567665147614335715328079

theorem tailTrace_5000510 : CollatzResearch.WordTrace tailWord_5000510 prefixEnd_5000510 2567665147614335715328079 := by
  unfold tailWord_5000510
  simp only [CollatzResearch.WordTrace]
  refine ⟨22797947889251720495146873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121589055409342509307449989 22797947889251720495146873)
  ·
    refine ⟨17098460916938790371360155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22797947889251720495146873 17098460916938790371360155)
    ·
      refine ⟨25647691375408185557040233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17098460916938790371360155 25647691375408185557040233)
      ·
        refine ⟨19235768531556139167780175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25647691375408185557040233 19235768531556139167780175)
        ·
          refine ⟨28853652797334208751670263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19235768531556139167780175 28853652797334208751670263)
          ·
            refine ⟨43280479196001313127505395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28853652797334208751670263 43280479196001313127505395)
            ·
              refine ⟨64920718794001969691258093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43280479196001313127505395 64920718794001969691258093)
              ·
                refine ⟨24345269547750738634221785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64920718794001969691258093 24345269547750738634221785)
                ·
                  refine ⟨18258952160813053975666339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24345269547750738634221785 18258952160813053975666339)
                  ·
                    refine ⟨27388428241219580963499509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18258952160813053975666339 27388428241219580963499509)
                    ·
                      refine ⟨2567665147614335715328079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27388428241219580963499509 2567665147614335715328079)
                      ·
                        rfl

theorem cell23_5000510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5000510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000510 prefixEnd_5000510 := by exact prefixLift 5000510
  have htrace : WordTrace (prefixWord ++ tailWord_5000510) baseStart_5000510 baseEnd_5000510 := by
    simpa [prefixWord, tailWord_5000510, baseEnd_5000510] using wordTrace_append hprefix tailTrace_5000510
  have hstable : (prefixWord ++ tailWord_5000510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000510).length < 2 ^ (prefixWord ++ tailWord_5000510).sum := by decide
  have hdescent : baseEnd_5000510 < baseStart_5000510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000524 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 2, 2, 2]
def baseStart_5000524 : Nat := 118140960795 + 5000524 * 2 ^ 59
def prefixEnd_5000524 : Nat := 4983230072969 + 3 ^ 40 * 5000524 * 2
def baseEnd_5000524 : Nat := 2567672336343498660553015

theorem tailTrace_5000524 : CollatzResearch.WordTrace tailWord_5000524 prefixEnd_5000524 2567672336343498660553015 := by
  unfold tailWord_5000524
  simp only [CollatzResearch.WordTrace]
  refine ⟨91192046867981522176092313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121589395823975362901456417 91192046867981522176092313)
  ·
    refine ⟨68394035150986141632069235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91192046867981522176092313 68394035150986141632069235)
    ·
      refine ⟨102591052726479212448103853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68394035150986141632069235 102591052726479212448103853)
      ·
        refine ⟨38471644772429704668038945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102591052726479212448103853 38471644772429704668038945)
        ·
          refine ⟨28853733579322278501029209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38471644772429704668038945 28853733579322278501029209)
          ·
            refine ⟨21640300184491708875771907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28853733579322278501029209 21640300184491708875771907)
            ·
              refine ⟨32460450276737563313657861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21640300184491708875771907 32460450276737563313657861)
              ·
                refine ⟨6086334426888293121310849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32460450276737563313657861 6086334426888293121310849)
                ·
                  refine ⟨4564750820166219840983137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6086334426888293121310849 4564750820166219840983137)
                  ·
                    refine ⟨3423563115124664880737353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564750820166219840983137 3423563115124664880737353)
                    ·
                      refine ⟨2567672336343498660553015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423563115124664880737353 2567672336343498660553015)
                      ·
                        rfl

theorem cell23_5000524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_5000524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000524 prefixEnd_5000524 := by exact prefixLift 5000524
  have htrace : WordTrace (prefixWord ++ tailWord_5000524) baseStart_5000524 baseEnd_5000524 := by
    simpa [prefixWord, tailWord_5000524, baseEnd_5000524] using wordTrace_append hprefix tailTrace_5000524
  have hstable : (prefixWord ++ tailWord_5000524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000524).length < 2 ^ (prefixWord ++ tailWord_5000524).sum := by decide
  have hdescent : baseEnd_5000524 < baseStart_5000524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000543 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 1, 7]
def baseStart_5000543 : Nat := 118140960795 + 5000543 * 2 ^ 59
def prefixEnd_5000543 : Nat := 4983230072969 + 3 ^ 40 * 5000543 * 2
def baseEnd_5000543 : Nat := 855894030825311362071809

theorem tailTrace_5000543 : CollatzResearch.WordTrace tailWord_5000543 prefixEnd_5000543 855894030825311362071809 := by
  unfold tailWord_5000543
  simp only [CollatzResearch.WordTrace]
  refine ⟨182384786722894210597126283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121589857815262807064750855 182384786722894210597126283)
  ·
    refine ⟨273577180084341315895689425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182384786722894210597126283 273577180084341315895689425)
    ·
      refine ⟨205182885063255986921767069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273577180084341315895689425 205182885063255986921767069)
      ·
        refine ⟨76943581898720995095662651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205182885063255986921767069 76943581898720995095662651)
        ·
          refine ⟨115415372848081492643493977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76943581898720995095662651 115415372848081492643493977)
          ·
            refine ⟨86561529636061119482620483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115415372848081492643493977 86561529636061119482620483)
            ·
              refine ⟨129842294454091679223930725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86561529636061119482620483 129842294454091679223930725)
              ·
                refine ⟨24345430210142189854487011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129842294454091679223930725 24345430210142189854487011)
                ·
                  refine ⟨36518145315213284781730517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24345430210142189854487011 36518145315213284781730517)
                  ·
                    refine ⟨855894030825311362071809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36518145315213284781730517 855894030825311362071809)
                    ·
                      rfl

theorem cell23_5000543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_5000543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000543 prefixEnd_5000543 := by exact prefixLift 5000543
  have htrace : WordTrace (prefixWord ++ tailWord_5000543) baseStart_5000543 baseEnd_5000543 := by
    simpa [prefixWord, tailWord_5000543, baseEnd_5000543] using wordTrace_append hprefix tailTrace_5000543
  have hstable : (prefixWord ++ tailWord_5000543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000543).length < 2 ^ (prefixWord ++ tailWord_5000543).sum := by decide
  have hdescent : baseEnd_5000543 < baseStart_5000543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000553 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_5000553 : Nat := 118140960795 + 5000553 * 2 ^ 59
def prefixEnd_5000553 : Nat := 4983230072969 + 3 ^ 40 * 5000553 * 2
def baseEnd_5000553 : Nat := 2567687227282479047090381

theorem tailTrace_5000553 : CollatzResearch.WordTrace tailWord_5000553 prefixEnd_5000553 2567687227282479047090381 := by
  unfold tailWord_5000553
  simp only [CollatzResearch.WordTrace]
  refine ⟨182385151452857982304990313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121590100968571988203326875 182385151452857982304990313)
  ·
    refine ⟨136788863589643486728742735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182385151452857982304990313 136788863589643486728742735)
    ·
      refine ⟨205183295384465230093114103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136788863589643486728742735 205183295384465230093114103)
      ·
        refine ⟨307774943076697845139671155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205183295384465230093114103 307774943076697845139671155)
        ·
          refine ⟨461662414615046767709506733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307774943076697845139671155 461662414615046767709506733)
          ·
            refine ⟨173123405480642537891065025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 461662414615046767709506733 173123405480642537891065025)
            ·
              refine ⟨129842554110481903418298769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173123405480642537891065025 129842554110481903418298769)
              ·
                refine ⟨97381915582861427563724077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129842554110481903418298769 97381915582861427563724077)
                ·
                  refine ⟨36518218343573035336396529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97381915582861427563724077 36518218343573035336396529)
                  ·
                    refine ⟨27388663757679776502297397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36518218343573035336396529 27388663757679776502297397)
                    ·
                      refine ⟨2567687227282479047090381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27388663757679776502297397 2567687227282479047090381)
                      ·
                        rfl

theorem cell23_5000553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_5000553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000553 prefixEnd_5000553 := by exact prefixLift 5000553
  have htrace : WordTrace (prefixWord ++ tailWord_5000553) baseStart_5000553 baseEnd_5000553 := by
    simpa [prefixWord, tailWord_5000553, baseEnd_5000553] using wordTrace_append hprefix tailTrace_5000553
  have hstable : (prefixWord ++ tailWord_5000553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000553).length < 2 ^ (prefixWord ++ tailWord_5000553).sum := by decide
  have hdescent : baseEnd_5000553 < baseStart_5000553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000597 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_5000597 : Nat := 118140960795 + 5000597 * 2 ^ 59
def prefixEnd_5000597 : Nat := 4983230072969 + 3 ^ 40 * 5000597 * 2
def baseEnd_5000597 : Nat := 2567709820431276874940179

theorem tailTrace_5000597 : CollatzResearch.WordTrace tailWord_5000597 prefixEnd_5000597 2567709820431276874940179 := by
  unfold tailWord_5000597
  simp only [CollatzResearch.WordTrace]
  refine ⟨182386756264698577819592045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121591170843132385213061363 182386756264698577819592045)
  ·
    refine ⟨68395033599261966682347017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 182386756264698577819592045 68395033599261966682347017)
    ·
      refine ⟨51296275199446475011760263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68395033599261966682347017 51296275199446475011760263)
      ·
        refine ⟨76944412799169712517640395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51296275199446475011760263 76944412799169712517640395)
        ·
          refine ⟨115416619198754568776460593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76944412799169712517640395 115416619198754568776460593)
          ·
            refine ⟨86562464399065926582345445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115416619198754568776460593 86562464399065926582345445)
            ·
              refine ⟨16230462074824861234189771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86562464399065926582345445 16230462074824861234189771)
              ·
                refine ⟨24345693112237291851284657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16230462074824861234189771 24345693112237291851284657)
                ·
                  refine ⟨18259269834177968888463493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24345693112237291851284657 18259269834177968888463493)
                  ·
                    refine ⟨3423613093908369166586905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18259269834177968888463493 3423613093908369166586905)
                    ·
                      refine ⟨2567709820431276874940179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423613093908369166586905 2567709820431276874940179)
                      ·
                        rfl

theorem cell23_5000597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_5000597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000597 prefixEnd_5000597 := by exact prefixLift 5000597
  have htrace : WordTrace (prefixWord ++ tailWord_5000597) baseStart_5000597 baseEnd_5000597 := by
    simpa [prefixWord, tailWord_5000597, baseEnd_5000597] using wordTrace_append hprefix tailTrace_5000597
  have hstable : (prefixWord ++ tailWord_5000597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000597).length < 2 ^ (prefixWord ++ tailWord_5000597).sum := by decide
  have hdescent : baseEnd_5000597 < baseStart_5000597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000607 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 3, 4]
def baseStart_5000607 : Nat := 118140960795 + 5000607 * 2 ^ 59
def prefixEnd_5000607 : Nat := 4983230072969 + 3 ^ 40 * 5000607 * 2
def baseEnd_5000607 : Nat := 855904985079273945271711

theorem tailTrace_5000607 : CollatzResearch.WordTrace tailWord_5000607 prefixEnd_5000607 855904985079273945271711 := by
  unfold tailWord_5000607
  simp only [CollatzResearch.WordTrace]
  refine ⟨182387120994662349527456075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121591413996441566351637383 182387120994662349527456075)
  ·
    refine ⟨273580681491993524291184113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182387120994662349527456075 273580681491993524291184113)
    ·
      refine ⟨205185511118995143218388085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273580681491993524291184113 205185511118995143218388085)
      ·
        refine ⟨19236141667405794676723883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205185511118995143218388085 19236141667405794676723883)
        ·
          refine ⟨28854212501108692015085825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19236141667405794676723883 28854212501108692015085825)
          ·
            refine ⟨21640659375831519011314369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28854212501108692015085825 21640659375831519011314369)
            ·
              refine ⟨16230494531873639258485777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21640659375831519011314369 16230494531873639258485777)
              ·
                refine ⟨12172870898905229443864333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16230494531873639258485777 12172870898905229443864333)
                ·
                  refine ⟨4564826587089461041449125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12172870898905229443864333 4564826587089461041449125)
                  ·
                    refine ⟨855904985079273945271711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564826587089461041449125 855904985079273945271711)
                    ·
                      rfl

theorem cell23_5000607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_5000607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000607 prefixEnd_5000607 := by exact prefixLift 5000607
  have htrace : WordTrace (prefixWord ++ tailWord_5000607) baseStart_5000607 baseEnd_5000607 := by
    simpa [prefixWord, tailWord_5000607, baseEnd_5000607] using wordTrace_append hprefix tailTrace_5000607
  have hstable : (prefixWord ++ tailWord_5000607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000607).length < 2 ^ (prefixWord ++ tailWord_5000607).sum := by decide
  have hdescent : baseEnd_5000607 < baseStart_5000607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000687 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 4]
def baseStart_5000687 : Nat := 118140960795 + 5000687 * 2 ^ 59
def prefixEnd_5000687 : Nat := 4983230072969 + 3 ^ 40 * 5000687 * 2
def baseEnd_5000687 : Nat := 2567756033690181522814765

theorem tailTrace_5000687 : CollatzResearch.WordTrace tailWord_5000687 prefixEnd_5000687 2567756033690181522814765 := by
  unfold tailWord_5000687
  simp only [CollatzResearch.WordTrace]
  refine ⟨182390038834372523190368315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121593359222915015460245543 182390038834372523190368315)
  ·
    refine ⟨273585058251558784785552473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182390038834372523190368315 273585058251558784785552473)
    ·
      refine ⟨205188793688669088589164355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273585058251558784785552473 205188793688669088589164355)
      ·
        refine ⟨307783190533003632883746533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205188793688669088589164355 307783190533003632883746533)
        ·
          refine ⟨57709348224938181165702475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307783190533003632883746533 57709348224938181165702475)
          ·
            refine ⟨86564022337407271748553713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57709348224938181165702475 86564022337407271748553713)
            ·
              refine ⟨64923016753055453811415285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86564022337407271748553713 64923016753055453811415285)
              ·
                refine ⟨6086532820598948794820183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64923016753055453811415285 6086532820598948794820183)
                ·
                  refine ⟨9129799230898423192230275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6086532820598948794820183 9129799230898423192230275)
                  ·
                    refine ⟨13694698846347634788345413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9129799230898423192230275 13694698846347634788345413)
                    ·
                      refine ⟨2567756033690181522814765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13694698846347634788345413 2567756033690181522814765)
                      ·
                        rfl

theorem cell23_5000687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_5000687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000687 prefixEnd_5000687 := by exact prefixLift 5000687
  have htrace : WordTrace (prefixWord ++ tailWord_5000687) baseStart_5000687 baseEnd_5000687 := by
    simpa [prefixWord, tailWord_5000687, baseEnd_5000687] using wordTrace_append hprefix tailTrace_5000687
  have hstable : (prefixWord ++ tailWord_5000687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000687).length < 2 ^ (prefixWord ++ tailWord_5000687).sum := by decide
  have hdescent : baseEnd_5000687 < baseStart_5000687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000700 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_5000700 : Nat := 118140960795 + 5000700 * 2 ^ 59
def prefixEnd_5000700 : Nat := 4983230072969 + 3 ^ 40 * 5000700 * 2
def baseEnd_5000700 : Nat := 2567762708938689971952205

theorem tailTrace_5000700 : CollatzResearch.WordTrace tailWord_5000700 prefixEnd_5000700 2567762708938689971952205 := by
  unfold tailWord_5000700
  simp only [CollatzResearch.WordTrace]
  refine ⟨91195256491662713205295777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121593675322216950940394369 91195256491662713205295777)
  ·
    refine ⟨68396442368747034903971833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91195256491662713205295777 68396442368747034903971833)
    ·
      refine ⟨51297331776560276177978875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68396442368747034903971833 51297331776560276177978875)
      ·
        refine ⟨76945997664840414266968313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51297331776560276177978875 76945997664840414266968313)
        ·
          refine ⟨57709498248630310700226235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76945997664840414266968313 57709498248630310700226235)
          ·
            refine ⟨86564247372945466050339353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57709498248630310700226235 86564247372945466050339353)
            ·
              refine ⟨64923185529709099537754515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86564247372945466050339353 64923185529709099537754515)
              ·
                refine ⟨97384778294563649306631773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64923185529709099537754515 97384778294563649306631773)
                ·
                  refine ⟨36519291860461368489986915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97384778294563649306631773 36519291860461368489986915)
                  ·
                    refine ⟨54778937790692052734980373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36519291860461368489986915 54778937790692052734980373)
                    ·
                      refine ⟨2567762708938689971952205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54778937790692052734980373 2567762708938689971952205)
                      ·
                        rfl

theorem cell23_5000700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_5000700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000700 prefixEnd_5000700 := by exact prefixLift 5000700
  have htrace : WordTrace (prefixWord ++ tailWord_5000700) baseStart_5000700 baseEnd_5000700 := by
    simpa [prefixWord, tailWord_5000700, baseEnd_5000700] using wordTrace_append hprefix tailTrace_5000700
  have hstable : (prefixWord ++ tailWord_5000700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000700).length < 2 ^ (prefixWord ++ tailWord_5000700).sum := by decide
  have hdescent : baseEnd_5000700 < baseStart_5000700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000714 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_5000714 : Nat := 118140960795 + 5000714 * 2 ^ 59
def prefixEnd_5000714 : Nat := 4983230072969 + 3 ^ 40 * 5000714 * 2
def baseEnd_5000714 : Nat := 855923299222617639059047

theorem tailTrace_5000714 : CollatzResearch.WordTrace tailWord_5000714 prefixEnd_5000714 855923299222617639059047 := by
  unfold tailWord_5000714
  simp only [CollatzResearch.WordTrace]
  refine ⟨45597755901318676700400299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121594015736849804534400797 45597755901318676700400299)
  ·
    refine ⟨68396633851978015050600449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45597755901318676700400299 68396633851978015050600449)
    ·
      refine ⟨51297475388983511287950337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68396633851978015050600449 51297475388983511287950337)
      ·
        refine ⟨38473106541737633465962753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51297475388983511287950337 38473106541737633465962753)
        ·
          refine ⟨28854829906303225099472065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38473106541737633465962753 28854829906303225099472065)
          ·
            refine ⟨21641122429727418824604049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28854829906303225099472065 21641122429727418824604049)
            ·
              refine ⟨16230841822295564118453037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21641122429727418824604049 16230841822295564118453037)
              ·
                refine ⟨6086565683360836544419889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16230841822295564118453037 6086565683360836544419889)
                ·
                  refine ⟨4564924262520627408314917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6086565683360836544419889 4564924262520627408314917)
                  ·
                    refine ⟨855923299222617639059047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4564924262520627408314917 855923299222617639059047)
                    ·
                      rfl

theorem cell23_5000714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_5000714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000714 prefixEnd_5000714 := by exact prefixLift 5000714
  have htrace : WordTrace (prefixWord ++ tailWord_5000714) baseStart_5000714 baseEnd_5000714 := by
    simpa [prefixWord, tailWord_5000714, baseEnd_5000714] using wordTrace_append hprefix tailTrace_5000714
  have hstable : (prefixWord ++ tailWord_5000714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000714).length < 2 ^ (prefixWord ++ tailWord_5000714).sum := by decide
  have hdescent : baseEnd_5000714 < baseStart_5000714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000738 : List Nat := [3, 3, 1, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_5000738 : Nat := 118140960795 + 5000738 * 2 ^ 59
def prefixEnd_5000738 : Nat := 4983230072969 + 3 ^ 40 * 5000738 * 2
def baseEnd_5000738 : Nat := 2567782221203560823277031

theorem tailTrace_5000738 : CollatzResearch.WordTrace tailWord_5000738 prefixEnd_5000738 2567782221203560823277031 := by
  unfold tailWord_5000738
  simp only [CollatzResearch.WordTrace]
  refine ⟨45597974739296939725118717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121594599304791839266983245 45597974739296939725118717)
  ·
    refine ⟨17099240527236352396919519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45597974739296939725118717 17099240527236352396919519)
    ·
      refine ⟨25648860790854528595379279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17099240527236352396919519 25648860790854528595379279)
      ·
        refine ⟨38473291186281792893068919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25648860790854528595379279 38473291186281792893068919)
        ·
          refine ⟨57709936779422689339603379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38473291186281792893068919 57709936779422689339603379)
          ·
            refine ⟨86564905169134034009405069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57709936779422689339603379 86564905169134034009405069)
            ·
              refine ⟨32461839438425262753526901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86564905169134034009405069 32461839438425262753526901)
              ·
                refine ⟨3043297447352368383143147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32461839438425262753526901 3043297447352368383143147)
                ·
                  refine ⟨4564946171028552574714721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043297447352368383143147 4564946171028552574714721)
                  ·
                    refine ⟨3423709628271414431036041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4564946171028552574714721 3423709628271414431036041)
                    ·
                      refine ⟨2567782221203560823277031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423709628271414431036041 2567782221203560823277031)
                      ·
                        rfl

theorem cell23_5000738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_5000738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000738 prefixEnd_5000738 := by exact prefixLift 5000738
  have htrace : WordTrace (prefixWord ++ tailWord_5000738) baseStart_5000738 baseEnd_5000738 := by
    simpa [prefixWord, tailWord_5000738, baseEnd_5000738] using wordTrace_append hprefix tailTrace_5000738
  have hstable : (prefixWord ++ tailWord_5000738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000738).length < 2 ^ (prefixWord ++ tailWord_5000738).sum := by decide
  have hdescent : baseEnd_5000738 < baseStart_5000738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000794 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2]
def baseStart_5000794 : Nat := 118140960795 + 5000794 * 2 ^ 59
def prefixEnd_5000794 : Nat := 4983230072969 + 3 ^ 40 * 5000794 * 2
def baseEnd_5000794 : Nat := 2567810976120212604176773

theorem tailTrace_5000794 : CollatzResearch.WordTrace tailWord_5000794 prefixEnd_5000794 2567810976120212604176773 := by
  unfold tailWord_5000794
  simp only [CollatzResearch.WordTrace]
  refine ⟨45598485361246220116128359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121595960963323253643008957 45598485361246220116128359)
  ·
    refine ⟨68397728041869330174192539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45598485361246220116128359 68397728041869330174192539)
    ·
      refine ⟨102596592062803995261288809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68397728041869330174192539 102596592062803995261288809)
      ·
        refine ⟨76947444047102996445966607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102596592062803995261288809 76947444047102996445966607)
        ·
          refine ⟨115421166070654494668949911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76947444047102996445966607 115421166070654494668949911)
          ·
            refine ⟨173131749105981742003424867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115421166070654494668949911 173131749105981742003424867)
            ·
              refine ⟨259697623658972613005137301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173131749105981742003424867 259697623658972613005137301)
              ·
                refine ⟨12173326109014341234615811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 259697623658972613005137301 12173326109014341234615811)
                ·
                  refine ⟨18259989163521511851923717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12173326109014341234615811 18259989163521511851923717)
                  ·
                    refine ⟨3423747968160283472235697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18259989163521511851923717 3423747968160283472235697)
                    ·
                      refine ⟨2567810976120212604176773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423747968160283472235697 2567810976120212604176773)
                      ·
                        rfl

theorem cell23_5000794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_5000794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000794 prefixEnd_5000794 := by exact prefixLift 5000794
  have htrace : WordTrace (prefixWord ++ tailWord_5000794) baseStart_5000794 baseEnd_5000794 := by
    simpa [prefixWord, tailWord_5000794, baseEnd_5000794] using wordTrace_append hprefix tailTrace_5000794
  have hstable : (prefixWord ++ tailWord_5000794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000794).length < 2 ^ (prefixWord ++ tailWord_5000794).sum := by decide
  have hdescent : baseEnd_5000794 < baseStart_5000794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000807 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_5000807 : Nat := 118140960795 + 5000807 * 2 ^ 59
def prefixEnd_5000807 : Nat := 4983230072969 + 3 ^ 40 * 5000807 * 2
def baseEnd_5000807 : Nat := 2567817651368721053314213

theorem tailTrace_5000807 : CollatzResearch.WordTrace tailWord_5000807 prefixEnd_5000807 2567817651368721053314213 := by
  unfold tailWord_5000807
  simp only [CollatzResearch.WordTrace]
  refine ⟨182394415593937783684736675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121596277062625189123157783 182394415593937783684736675)
  ·
    refine ⟨273591623390906675527105013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182394415593937783684736675 273591623390906675527105013)
    ·
      refine ⟨25649214692897500830666095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 273591623390906675527105013 25649214692897500830666095)
      ·
        refine ⟨38473822039346251245999143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25649214692897500830666095 38473822039346251245999143)
        ·
          refine ⟨57710733059019376868998715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38473822039346251245999143 57710733059019376868998715)
          ·
            refine ⟨86566099588529065303498073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57710733059019376868998715 86566099588529065303498073)
            ·
              refine ⟨64924574691396798977623555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86566099588529065303498073 64924574691396798977623555)
              ·
                refine ⟨97386862037095198466435333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64924574691396798977623555 97386862037095198466435333)
                ·
                  refine ⟨18260036631955349712456625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97386862037095198466435333 18260036631955349712456625)
                  ·
                    refine ⟨13695027473966512284342469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18260036631955349712456625 13695027473966512284342469)
                    ·
                      refine ⟨2567817651368721053314213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13695027473966512284342469 2567817651368721053314213)
                      ·
                        rfl

theorem cell23_5000807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_5000807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000807 prefixEnd_5000807 := by exact prefixLift 5000807
  have htrace : WordTrace (prefixWord ++ tailWord_5000807) baseStart_5000807 baseEnd_5000807 := by
    simpa [prefixWord, tailWord_5000807, baseEnd_5000807] using wordTrace_append hprefix tailTrace_5000807
  have hstable : (prefixWord ++ tailWord_5000807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000807).length < 2 ^ (prefixWord ++ tailWord_5000807).sum := by decide
  have hdescent : baseEnd_5000807 < baseStart_5000807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000827 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 3]
def baseStart_5000827 : Nat := 118140960795 + 5000827 * 2 ^ 59
def prefixEnd_5000827 : Nat := 4983230072969 + 3 ^ 40 * 5000827 * 2
def baseEnd_5000827 : Nat := 2567827920981810975064121

theorem tailTrace_5000827 : CollatzResearch.WordTrace tailWord_5000827 prefixEnd_5000827 2567827920981810975064121 := by
  unfold tailWord_5000827
  simp only [CollatzResearch.WordTrace]
  refine ⟨182395145053865327100464735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121596763369243551400309823 182395145053865327100464735)
  ·
    refine ⟨273592717580797990650697103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182395145053865327100464735 273592717580797990650697103)
    ·
      refine ⟨410389076371196985976045655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273592717580797990650697103 410389076371196985976045655)
      ·
        refine ⟨615583614556795478964068483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410389076371196985976045655 615583614556795478964068483)
        ·
          refine ⟨923375421835193218446102725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615583614556795478964068483 923375421835193218446102725)
          ·
            refine ⟨173132891594098728458644261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 923375421835193218446102725 173132891594098728458644261)
            ·
              refine ⟨32462417173893511585995799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173132891594098728458644261 32462417173893511585995799)
              ·
                refine ⟨48693625760840267378993699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32462417173893511585995799 48693625760840267378993699)
                ·
                  refine ⟨73040438641260401068490549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48693625760840267378993699 73040438641260401068490549)
                  ·
                    refine ⟨6847541122618162600170989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73040438641260401068490549 6847541122618162600170989)
                    ·
                      refine ⟨2567827920981810975064121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6847541122618162600170989 2567827920981810975064121)
                      ·
                        rfl

theorem cell23_5000827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 3].length) (baseStart_5000827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000827 prefixEnd_5000827 := by exact prefixLift 5000827
  have htrace : WordTrace (prefixWord ++ tailWord_5000827) baseStart_5000827 baseEnd_5000827 := by
    simpa [prefixWord, tailWord_5000827, baseEnd_5000827] using wordTrace_append hprefix tailTrace_5000827
  have hstable : (prefixWord ++ tailWord_5000827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000827).length < 2 ^ (prefixWord ++ tailWord_5000827).sum := by decide
  have hdescent : baseEnd_5000827 < baseStart_5000827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000864 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 2, 5]
def baseStart_5000864 : Nat := 118140960795 + 5000864 * 2 ^ 59
def prefixEnd_5000864 : Nat := 4983230072969 + 3 ^ 40 * 5000864 * 2
def baseEnd_5000864 : Nat := 855948973255342443433817

theorem tailTrace_5000864 : CollatzResearch.WordTrace tailWord_5000864 prefixEnd_5000864 855948973255342443433817 := by
  unfold tailWord_5000864
  simp only [CollatzResearch.WordTrace]
  refine ⟨91198247277365641209780823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121597663036487521613041097 91198247277365641209780823)
  ·
    refine ⟨136797370916048461814671235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91198247277365641209780823 136797370916048461814671235)
    ·
      refine ⟨205196056374072692722006853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136797370916048461814671235 205196056374072692722006853)
      ·
        refine ⟨38474260570138629885376285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205196056374072692722006853 38474260570138629885376285)
        ·
          refine ⟨14427847713801986207016107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38474260570138629885376285 14427847713801986207016107)
          ·
            refine ⟨21641771570702979310524161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14427847713801986207016107 21641771570702979310524161)
            ·
              refine ⟨16231328678027234482893121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21641771570702979310524161 16231328678027234482893121)
              ·
                refine ⟨12173496508520425862169841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16231328678027234482893121 12173496508520425862169841)
                ·
                  refine ⟨9130122381390319396627381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12173496508520425862169841 9130122381390319396627381)
                  ·
                    refine ⟨855948973255342443433817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9130122381390319396627381 855948973255342443433817)
                    ·
                      rfl

theorem cell23_5000864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_5000864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000864 prefixEnd_5000864 := by exact prefixLift 5000864
  have htrace : WordTrace (prefixWord ++ tailWord_5000864) baseStart_5000864 baseEnd_5000864 := by
    simpa [prefixWord, tailWord_5000864, baseEnd_5000864] using wordTrace_append hprefix tailTrace_5000864
  have hstable : (prefixWord ++ tailWord_5000864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000864).length < 2 ^ (prefixWord ++ tailWord_5000864).sum := by decide
  have hdescent : baseEnd_5000864 < baseStart_5000864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000868 : List Nat := [2, 3, 1, 2, 2, 4, 2, 2, 5]
def baseStart_5000868 : Nat := 118140960795 + 5000868 * 2 ^ 59
def prefixEnd_5000868 : Nat := 4983230072969 + 3 ^ 40 * 5000868 * 2
def baseEnd_5000868 : Nat := 285316552632071701627937

theorem tailTrace_5000868 : CollatzResearch.WordTrace tailWord_5000868 prefixEnd_5000868 285316552632071701627937 := by
  unfold tailWord_5000868
  simp only [CollatzResearch.WordTrace]
  refine ⟨91198320223358395551353629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121597760297811194068471505 91198320223358395551353629)
  ·
    refine ⟨34199370083759398331757611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91198320223358395551353629 34199370083759398331757611)
    ·
      refine ⟨51299055125639097497636417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34199370083759398331757611 51299055125639097497636417)
      ·
        refine ⟨38474291344229323123227313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51299055125639097497636417 38474291344229323123227313)
        ·
          refine ⟨28855718508171992342420485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38474291344229323123227313 28855718508171992342420485)
          ·
            refine ⟨5410447220282248564203841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28855718508171992342420485 5410447220282248564203841)
            ·
              refine ⟨4057835415211686423152881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5410447220282248564203841 4057835415211686423152881)
              ·
                refine ⟨3043376561408764817364661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4057835415211686423152881 3043376561408764817364661)
                ·
                  refine ⟨285316552632071701627937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3043376561408764817364661 285316552632071701627937)
                  ·
                    rfl

theorem cell23_5000868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_5000868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000868 prefixEnd_5000868 := by exact prefixLift 5000868
  have htrace : WordTrace (prefixWord ++ tailWord_5000868) baseStart_5000868 baseEnd_5000868 := by
    simpa [prefixWord, tailWord_5000868, baseEnd_5000868] using wordTrace_append hprefix tailTrace_5000868
  have hstable : (prefixWord ++ tailWord_5000868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000868).length < 2 ^ (prefixWord ++ tailWord_5000868).sum := by decide
  have hdescent : baseEnd_5000868 < baseStart_5000868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000878 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5000878 : Nat := 118140960795 + 5000878 * 2 ^ 59
def prefixEnd_5000878 : Nat := 4983230072969 + 3 ^ 40 * 5000878 * 2
def baseEnd_5000878 : Nat := 2567854108495190275526387

theorem tailTrace_5000878 : CollatzResearch.WordTrace tailWord_5000878 prefixEnd_5000878 2567854108495190275526387 := by
  unfold tailWord_5000878
  simp only [CollatzResearch.WordTrace]
  refine ⟨22799625647085070351321411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 121598003451120375207047525 22799625647085070351321411)
  ·
    refine ⟨34199438470627605526982117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22799625647085070351321411 34199438470627605526982117)
    ·
      refine ⟨6412394713242676036309147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34199438470627605526982117 6412394713242676036309147)
      ·
        refine ⟨9618592069864014054463721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6412394713242676036309147 9618592069864014054463721)
        ·
          refine ⟨7213944052398010540847791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9618592069864014054463721 7213944052398010540847791)
          ·
            refine ⟨10820916078597015811271687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7213944052398010540847791 10820916078597015811271687)
            ·
              refine ⟨16231374117895523716907531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10820916078597015811271687 16231374117895523716907531)
              ·
                refine ⟨24347061176843285575361297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16231374117895523716907531 24347061176843285575361297)
                ·
                  refine ⟨18260295882632464181520973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24347061176843285575361297 18260295882632464181520973)
                  ·
                    refine ⟨6847610955987174068070365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18260295882632464181520973 6847610955987174068070365)
                    ·
                      refine ⟨2567854108495190275526387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6847610955987174068070365 2567854108495190275526387)
                      ·
                        rfl

theorem cell23_5000878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5000878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000878 prefixEnd_5000878 := by exact prefixLift 5000878
  have htrace : WordTrace (prefixWord ++ tailWord_5000878) baseStart_5000878 baseEnd_5000878 := by
    simpa [prefixWord, tailWord_5000878, baseEnd_5000878] using wordTrace_append hprefix tailTrace_5000878
  have hstable : (prefixWord ++ tailWord_5000878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000878).length < 2 ^ (prefixWord ++ tailWord_5000878).sum := by decide
  have hdescent : baseEnd_5000878 < baseStart_5000878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000904 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_5000904 : Nat := 118140960795 + 5000904 * 2 ^ 59
def prefixEnd_5000904 : Nat := 4983230072969 + 3 ^ 40 * 5000904 * 2
def baseEnd_5000904 : Nat := 2567867458992207173801267

theorem tailTrace_5000904 : CollatzResearch.WordTrace tailWord_5000904 prefixEnd_5000904 2567867458992207173801267 := by
  unfold tailWord_5000904
  simp only [CollatzResearch.WordTrace]
  refine ⟨91198976737293184625508883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121598635649724246167345177 91198976737293184625508883)
  ·
    refine ⟨136798465105939776938263325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91198976737293184625508883 136798465105939776938263325)
    ·
      refine ⟨51299424414727416351848747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136798465105939776938263325 51299424414727416351848747)
      ·
        refine ⟨76949136622091124527773121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51299424414727416351848747 76949136622091124527773121)
        ·
          refine ⟨57711852466568343395829841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76949136622091124527773121 57711852466568343395829841)
          ·
            refine ⟨43283889349926257546872381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57711852466568343395829841 43283889349926257546872381)
            ·
              refine ⟨16231458506222346580077143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43283889349926257546872381 16231458506222346580077143)
              ·
                refine ⟨24347187759333519870115715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16231458506222346580077143 24347187759333519870115715)
                ·
                  refine ⟨36520781639000279805173573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24347187759333519870115715 36520781639000279805173573)
                  ·
                    refine ⟨6847646557312552463470045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36520781639000279805173573 6847646557312552463470045)
                    ·
                      refine ⟨2567867458992207173801267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6847646557312552463470045 2567867458992207173801267)
                      ·
                        rfl

theorem cell23_5000904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_5000904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000904 prefixEnd_5000904 := by exact prefixLift 5000904
  have htrace : WordTrace (prefixWord ++ tailWord_5000904) baseStart_5000904 baseEnd_5000904 := by
    simpa [prefixWord, tailWord_5000904, baseEnd_5000904] using wordTrace_append hprefix tailTrace_5000904
  have hstable : (prefixWord ++ tailWord_5000904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000904).length < 2 ^ (prefixWord ++ tailWord_5000904).sum := by decide
  have hdescent : baseEnd_5000904 < baseStart_5000904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000914 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5000914 : Nat := 118140960795 + 5000914 * 2 ^ 59
def prefixEnd_5000914 : Nat := 4983230072969 + 3 ^ 40 * 5000914 * 2
def baseEnd_5000914 : Nat := 2567872593798752134676221

theorem tailTrace_5000914 : CollatzResearch.WordTrace tailWord_5000914 prefixEnd_5000914 2567872593798752134676221 := by
  unfold tailWord_5000914
  simp only [CollatzResearch.WordTrace]
  refine ⟨45599579551137535239720449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121598878803033427305921197 45599579551137535239720449)
  ·
    refine ⟨34199684663353151429790337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45599579551137535239720449 34199684663353151429790337)
    ·
      refine ⟨25649763497514863572342753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34199684663353151429790337 25649763497514863572342753)
      ·
        refine ⟨19237322623136147679257065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25649763497514863572342753 19237322623136147679257065)
        ·
          refine ⟨14427991967352110759442799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19237322623136147679257065 14427991967352110759442799)
          ·
            refine ⟨21641987951028166139164199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14427991967352110759442799 21641987951028166139164199)
            ·
              refine ⟨32462981926542249208746299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21641987951028166139164199 32462981926542249208746299)
              ·
                refine ⟨48694472889813373813119449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32462981926542249208746299 48694472889813373813119449)
                ·
                  refine ⟨36520854667360030359839587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48694472889813373813119449 36520854667360030359839587)
                  ·
                    refine ⟨54781282001040045539759381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36520854667360030359839587 54781282001040045539759381)
                    ·
                      refine ⟨2567872593798752134676221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54781282001040045539759381 2567872593798752134676221)
                      ·
                        rfl

theorem cell23_5000914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5000914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000914 prefixEnd_5000914 := by exact prefixLift 5000914
  have htrace : WordTrace (prefixWord ++ tailWord_5000914) baseStart_5000914 baseEnd_5000914 := by
    simpa [prefixWord, tailWord_5000914, baseEnd_5000914] using wordTrace_append hprefix tailTrace_5000914
  have hstable : (prefixWord ++ tailWord_5000914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000914).length < 2 ^ (prefixWord ++ tailWord_5000914).sum := by decide
  have hdescent : baseEnd_5000914 < baseStart_5000914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000927 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_5000927 : Nat := 118140960795 + 5000927 * 2 ^ 59
def prefixEnd_5000927 : Nat := 4983230072969 + 3 ^ 40 * 5000927 * 2
def baseEnd_5000927 : Nat := 2567879269047260583813661

theorem tailTrace_5000927 : CollatzResearch.WordTrace tailWord_5000927 prefixEnd_5000927 2567879269047260583813661 := by
  unfold tailWord_5000927
  simp only [CollatzResearch.WordTrace]
  refine ⟨182398792353503044179105035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121599194902335362786070023 182398792353503044179105035)
  ·
    refine ⟨273598188530254566268657553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182398792353503044179105035 273598188530254566268657553)
    ·
      refine ⟨205198641397690924701493165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273598188530254566268657553 205198641397690924701493165)
      ·
        refine ⟨76949490524134096763059937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205198641397690924701493165 76949490524134096763059937)
        ·
          refine ⟨57712117893100572572294953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76949490524134096763059937 57712117893100572572294953)
          ·
            refine ⟨43284088419825429429221215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57712117893100572572294953 43284088419825429429221215)
            ·
              refine ⟨64926132629738144143831823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43284088419825429429221215 64926132629738144143831823)
              ·
                refine ⟨97389198944607216215747735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64926132629738144143831823 97389198944607216215747735)
                ·
                  refine ⟨146083798416910824323621603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97389198944607216215747735 146083798416910824323621603)
                  ·
                    refine ⟨219125697625366236485432405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146083798416910824323621603 219125697625366236485432405)
                    ·
                      refine ⟨2567879269047260583813661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 219125697625366236485432405 2567879269047260583813661)
                      ·
                        rfl

theorem cell23_5000927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_5000927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000927 prefixEnd_5000927 := by exact prefixLift 5000927
  have htrace : WordTrace (prefixWord ++ tailWord_5000927) baseStart_5000927 baseEnd_5000927 := by
    simpa [prefixWord, tailWord_5000927, baseEnd_5000927] using wordTrace_append hprefix tailTrace_5000927
  have hstable : (prefixWord ++ tailWord_5000927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000927).length < 2 ^ (prefixWord ++ tailWord_5000927).sum := by decide
  have hdescent : baseEnd_5000927 < baseStart_5000927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000947 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7]
def baseStart_5000947 : Nat := 118140960795 + 5000947 * 2 ^ 59
def prefixEnd_5000947 : Nat := 4983230072969 + 3 ^ 40 * 5000947 * 2
def baseEnd_5000947 : Nat := 2567889538660350505563569

theorem tailTrace_5000947 : CollatzResearch.WordTrace tailWord_5000947 prefixEnd_5000947 2567889538660350505563569 := by
  unfold tailWord_5000947
  simp only [CollatzResearch.WordTrace]
  refine ⟨182399521813430587594833095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121599681208953725063222063 182399521813430587594833095)
  ·
    refine ⟨273599282720145881392249643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182399521813430587594833095 273599282720145881392249643)
    ·
      refine ⟨410398924080218822088374465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273599282720145881392249643 410398924080218822088374465)
      ·
        refine ⟨307799193060164116566280849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410398924080218822088374465 307799193060164116566280849)
        ·
          refine ⟨230849394795123087424710637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307799193060164116566280849 230849394795123087424710637)
          ·
            refine ⟨86568523048171157784266489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230849394795123087424710637 86568523048171157784266489)
            ·
              refine ⟨64926392286128368338199867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86568523048171157784266489 64926392286128368338199867)
              ·
                refine ⟨97389588429192552507299801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64926392286128368338199867 97389588429192552507299801)
                ·
                  refine ⟨73042191321894414380474851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97389588429192552507299801 73042191321894414380474851)
                  ·
                    refine ⟨109563286982841621570712277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73042191321894414380474851 109563286982841621570712277)
                    ·
                      refine ⟨2567889538660350505563569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109563286982841621570712277 2567889538660350505563569)
                      ·
                        rfl

theorem cell23_5000947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_5000947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000947 prefixEnd_5000947 := by exact prefixLift 5000947
  have htrace : WordTrace (prefixWord ++ tailWord_5000947) baseStart_5000947 baseEnd_5000947 := by
    simpa [prefixWord, tailWord_5000947, baseEnd_5000947] using wordTrace_append hprefix tailTrace_5000947
  have hstable : (prefixWord ++ tailWord_5000947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000947).length < 2 ^ (prefixWord ++ tailWord_5000947).sum := by decide
  have hdescent : baseEnd_5000947 < baseStart_5000947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000951 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_5000951 : Nat := 118140960795 + 5000951 * 2 ^ 59
def prefixEnd_5000951 : Nat := 4983230072969 + 3 ^ 40 * 5000951 * 2
def baseEnd_5000951 : Nat := 2567891592582968489913551

theorem tailTrace_5000951 : CollatzResearch.WordTrace tailWord_5000951 prefixEnd_5000951 2567891592582968489913551 := by
  unfold tailWord_5000951
  simp only [CollatzResearch.WordTrace]
  refine ⟨182399667705416096277978707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121599778470277397518652471 182399667705416096277978707)
  ·
    refine ⟨273599501558124144416968061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182399667705416096277978707 273599501558124144416968061)
    ·
      refine ⟨102599813084296554156363023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273599501558124144416968061 102599813084296554156363023)
      ·
        refine ⟨153899719626444831234544535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102599813084296554156363023 153899719626444831234544535)
        ·
          refine ⟨230849579439667246851816803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153899719626444831234544535 230849579439667246851816803)
          ·
            refine ⟨346274369159500870277725205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230849579439667246851816803 346274369159500870277725205)
            ·
              refine ⟨16231611054351603294268369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 346274369159500870277725205 16231611054351603294268369)
              ·
                refine ⟨12173708290763702470701277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16231611054351603294268369 12173708290763702470701277)
                ·
                  refine ⟨4565140609036388426512979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12173708290763702470701277 4565140609036388426512979)
                  ·
                    refine ⟨6847710913554582639769469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4565140609036388426512979 6847710913554582639769469)
                    ·
                      refine ⟨2567891592582968489913551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6847710913554582639769469 2567891592582968489913551)
                      ·
                        rfl

theorem cell23_5000951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_5000951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000951 prefixEnd_5000951 := by exact prefixLift 5000951
  have htrace : WordTrace (prefixWord ++ tailWord_5000951) baseStart_5000951 baseEnd_5000951 := by
    simpa [prefixWord, tailWord_5000951, baseEnd_5000951] using wordTrace_append hprefix tailTrace_5000951
  have hstable : (prefixWord ++ tailWord_5000951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000951).length < 2 ^ (prefixWord ++ tailWord_5000951).sum := by decide
  have hdescent : baseEnd_5000951 < baseStart_5000951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5000961 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_5000961 : Nat := 118140960795 + 5000961 * 2 ^ 59
def prefixEnd_5000961 : Nat := 4983230072969 + 3 ^ 40 * 5000961 * 2
def baseEnd_5000961 : Nat := 2567896727389513450788505

theorem tailTrace_5000961 : CollatzResearch.WordTrace tailWord_5000961 prefixEnd_5000961 2567896727389513450788505 := by
  unfold tailWord_5000961
  simp only [CollatzResearch.WordTrace]
  refine ⟨182400032435379867985842737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121600021623586578657228491 182400032435379867985842737)
  ·
    refine ⟨136800024326534900989382053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182400032435379867985842737 136800024326534900989382053)
    ·
      refine ⟨25650004561225293935509135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136800024326534900989382053 25650004561225293935509135)
      ·
        refine ⟨38475006841837940903263703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25650004561225293935509135 38475006841837940903263703)
        ·
          refine ⟨57712510262756911354895555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38475006841837940903263703 57712510262756911354895555)
          ·
            refine ⟨86568765394135367032343333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57712510262756911354895555 86568765394135367032343333)
            ·
              refine ⟨16231643511400381318564375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86568765394135367032343333 16231643511400381318564375)
              ·
                refine ⟨24347465267100571977846563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16231643511400381318564375 24347465267100571977846563)
                ·
                  refine ⟨36521197900650857966769845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24347465267100571977846563 36521197900650857966769845)
                  ·
                    refine ⟨3423862303186017934384673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36521197900650857966769845 3423862303186017934384673)
                    ·
                      refine ⟨2567896727389513450788505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423862303186017934384673 2567896727389513450788505)
                      ·
                        rfl

theorem cell23_5000961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_5000961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5000961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5000961 prefixEnd_5000961 := by exact prefixLift 5000961
  have htrace : WordTrace (prefixWord ++ tailWord_5000961) baseStart_5000961 baseEnd_5000961 := by
    simpa [prefixWord, tailWord_5000961, baseEnd_5000961] using wordTrace_append hprefix tailTrace_5000961
  have hstable : (prefixWord ++ tailWord_5000961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5000961).length < 2 ^ (prefixWord ++ tailWord_5000961).sum := by decide
  have hdescent : baseEnd_5000961 < baseStart_5000961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5000961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001004 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_5001004 : Nat := 118140960795 + 5001004 * 2 ^ 59
def prefixEnd_5001004 : Nat := 4983230072969 + 3 ^ 40 * 5001004 * 2
def baseEnd_5001004 : Nat := 2567918807057656782550807

theorem tailTrace_5001004 : CollatzResearch.WordTrace tailWord_5001004 prefixEnd_5001004 2567918807057656782550807 := by
  unfold tailWord_5001004
  simp only [CollatzResearch.WordTrace]
  refine ⟨91200800387112043164829033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121601067182816057553105377 91200800387112043164829033)
  ·
    refine ⟨68400600290334032373621775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91200800387112043164829033 68400600290334032373621775)
    ·
      refine ⟨102600900435501048560432663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68400600290334032373621775 102600900435501048560432663)
      ·
        refine ⟨153901350653251572840648995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102600900435501048560432663 153901350653251572840648995)
        ·
          refine ⟨230852025979877359260973493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153901350653251572840648995 230852025979877359260973493)
          ·
            refine ⟨21642377435613502430716265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 230852025979877359260973493 21642377435613502430716265)
            ·
              refine ⟨16231783076710126823037199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21642377435613502430716265 16231783076710126823037199)
              ·
                refine ⟨24347674615065190234555799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16231783076710126823037199 24347674615065190234555799)
                ·
                  refine ⟨36521511922597785351833699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24347674615065190234555799 36521511922597785351833699)
                  ·
                    refine ⟨54782267883896678027750549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36521511922597785351833699 54782267883896678027750549)
                    ·
                      refine ⟨2567918807057656782550807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54782267883896678027750549 2567918807057656782550807)
                      ·
                        rfl

theorem cell23_5001004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_5001004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001004 prefixEnd_5001004 := by exact prefixLift 5001004
  have htrace : WordTrace (prefixWord ++ tailWord_5001004) baseStart_5001004 baseEnd_5001004 := by
    simpa [prefixWord, tailWord_5001004, baseEnd_5001004] using wordTrace_append hprefix tailTrace_5001004
  have hstable : (prefixWord ++ tailWord_5001004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001004).length < 2 ^ (prefixWord ++ tailWord_5001004).sum := by decide
  have hdescent : baseEnd_5001004 < baseStart_5001004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001021 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5001021 : Nat := 118140960795 + 5001021 * 2 ^ 59
def prefixEnd_5001021 : Nat := 4983230072969 + 3 ^ 40 * 5001021 * 2
def baseEnd_5001021 : Nat := 2567927536228783216038229

theorem tailTrace_5001021 : CollatzResearch.WordTrace tailWord_5001021 prefixEnd_5001021 2567927536228783216038229 := by
  unfold tailWord_5001021
  simp only [CollatzResearch.WordTrace]
  refine ⟨182402220815162498233026917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121601480543441665488684611 182402220815162498233026917)
  ·
    refine ⟨34200416402842968418692547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 182402220815162498233026917 34200416402842968418692547)
    ·
      refine ⟨51300624604264452628038821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34200416402842968418692547 51300624604264452628038821)
      ·
        refine ⟨9618867113299584867757279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51300624604264452628038821 9618867113299584867757279)
        ·
          refine ⟨14428300669949377301635919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9618867113299584867757279 14428300669949377301635919)
          ·
            refine ⟨21642451004924065952453879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14428300669949377301635919 21642451004924065952453879)
            ·
              refine ⟨32463676507386098928680819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21642451004924065952453879 32463676507386098928680819)
              ·
                refine ⟨48695514761079148393021229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32463676507386098928680819 48695514761079148393021229)
                ·
                  refine ⟨18260818035404680647382961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48695514761079148393021229 18260818035404680647382961)
                  ·
                    refine ⟨13695613526553510485537221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18260818035404680647382961 13695613526553510485537221)
                    ·
                      refine ⟨2567927536228783216038229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13695613526553510485537221 2567927536228783216038229)
                      ·
                        rfl

theorem cell23_5001021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5001021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001021 prefixEnd_5001021 := by exact prefixLift 5001021
  have htrace : WordTrace (prefixWord ++ tailWord_5001021) baseStart_5001021 baseEnd_5001021 := by
    simpa [prefixWord, tailWord_5001021, baseEnd_5001021] using wordTrace_append hprefix tailTrace_5001021
  have hstable : (prefixWord ++ tailWord_5001021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001021).length < 2 ^ (prefixWord ++ tailWord_5001021).sum := by decide
  have hdescent : baseEnd_5001021 < baseStart_5001021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001042 : List Nat := [3, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_5001042 : Nat := 118140960795 + 5001042 * 2 ^ 59
def prefixEnd_5001042 : Nat := 4983230072969 + 3 ^ 40 * 5001042 * 2
def baseEnd_5001042 : Nat := 2567938319322527633875633

theorem tailTrace_5001042 : CollatzResearch.WordTrace tailWord_5001042 prefixEnd_5001042 2567938319322527633875633 := by
  unfold tailWord_5001042
  simp only [CollatzResearch.WordTrace]
  refine ⟨45600746687021604704885345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121601991165390945879694253 45600746687021604704885345)
  ·
    refine ⟨34200560015266203528664009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45600746687021604704885345 34200560015266203528664009)
    ·
      refine ⟨25650420011449652646498007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34200560015266203528664009 25650420011449652646498007)
      ·
        refine ⟨38475630017174478969747011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25650420011449652646498007 38475630017174478969747011)
        ·
          refine ⟨57713445025761718454620517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38475630017174478969747011 57713445025761718454620517)
          ·
            refine ⟨10821270942330322210241347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57713445025761718454620517 10821270942330322210241347)
            ·
              refine ⟨16231906413495483315362021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10821270942330322210241347 16231906413495483315362021)
              ·
                refine ⟨3043482452530403121630379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16231906413495483315362021 3043482452530403121630379)
                ·
                  refine ⟨4565223678795604682445569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043482452530403121630379 4565223678795604682445569)
                  ·
                    refine ⟨3423917759096703511834177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4565223678795604682445569 3423917759096703511834177)
                    ·
                      refine ⟨2567938319322527633875633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423917759096703511834177 2567938319322527633875633)
                      ·
                        rfl

theorem cell23_5001042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_5001042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001042 prefixEnd_5001042 := by exact prefixLift 5001042
  have htrace : WordTrace (prefixWord ++ tailWord_5001042) baseStart_5001042 baseEnd_5001042 := by
    simpa [prefixWord, tailWord_5001042, baseEnd_5001042] using wordTrace_append hprefix tailTrace_5001042
  have hstable : (prefixWord ++ tailWord_5001042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001042).length < 2 ^ (prefixWord ++ tailWord_5001042).sum := by decide
  have hdescent : baseEnd_5001042 < baseStart_5001042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001058 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5001058 : Nat := 118140960795 + 5001058 * 2 ^ 59
def prefixEnd_5001058 : Nat := 4983230072969 + 3 ^ 40 * 5001058 * 2
def baseEnd_5001058 : Nat := 2567946535012999571275559

theorem tailTrace_5001058 : CollatzResearch.WordTrace tailWord_5001058 prefixEnd_5001058 2567946535012999571275559 := by
  unfold tailWord_5001058
  simp only [CollatzResearch.WordTrace]
  refine ⟨45600892579007113388030957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121602380210685635701415885 45600892579007113388030957)
  ·
    refine ⟨17100334717127667520511609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45600892579007113388030957 17100334717127667520511609)
    ·
      refine ⟨12825251037845750640383707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17100334717127667520511609 12825251037845750640383707)
      ·
        refine ⟨19237876556768625960575561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12825251037845750640383707 19237876556768625960575561)
        ·
          refine ⟨14428407417576469470431671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19237876556768625960575561 14428407417576469470431671)
          ·
            refine ⟨21642611126364704205647507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14428407417576469470431671 21642611126364704205647507)
            ·
              refine ⟨32463916689547056308471261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21642611126364704205647507 32463916689547056308471261)
              ·
                refine ⟨12173968758580146115676723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32463916689547056308471261 12173968758580146115676723)
                ·
                  refine ⟨18260953137870219173515085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12173968758580146115676723 18260953137870219173515085)
                  ·
                    refine ⟨6847857426701332190068157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18260953137870219173515085 6847857426701332190068157)
                    ·
                      refine ⟨2567946535012999571275559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6847857426701332190068157 2567946535012999571275559)
                      ·
                        rfl

theorem cell23_5001058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5001058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001058 prefixEnd_5001058 := by exact prefixLift 5001058
  have htrace : WordTrace (prefixWord ++ tailWord_5001058) baseStart_5001058 baseEnd_5001058 := by
    simpa [prefixWord, tailWord_5001058, baseEnd_5001058] using wordTrace_append hprefix tailTrace_5001058
  have hstable : (prefixWord ++ tailWord_5001058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001058).length < 2 ^ (prefixWord ++ tailWord_5001058).sum := by decide
  have hdescent : baseEnd_5001058 < baseStart_5001058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001068 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 3, 3, 2]
def baseStart_5001068 : Nat := 118140960795 + 5001068 * 2 ^ 59
def prefixEnd_5001068 : Nat := 4983230072969 + 3 ^ 40 * 5001068 * 2
def baseEnd_5001068 : Nat := 2567951669819544532150513

theorem tailTrace_5001068 : CollatzResearch.WordTrace tailWord_5001068 prefixEnd_5001068 2567951669819544532150513 := by
  unfold tailWord_5001068
  simp only [CollatzResearch.WordTrace]
  refine ⟨91201967522996112629993929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121602623363994816839991905 91201967522996112629993929)
  ·
    refine ⟨68401475642247084472495447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91201967522996112629993929 68401475642247084472495447)
    ·
      refine ⟨102602213463370626708743171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68401475642247084472495447 102602213463370626708743171)
      ·
        refine ⟨153903320195055940063114757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102602213463370626708743171 153903320195055940063114757)
        ·
          refine ⟨28856872536572988761834017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153903320195055940063114757 28856872536572988761834017)
          ·
            refine ⟨21642654402429741571375513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28856872536572988761834017 21642654402429741571375513)
            ·
              refine ⟨16231990801822306178531635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21642654402429741571375513 16231990801822306178531635)
              ·
                refine ⟨24347986202733459267797453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16231990801822306178531635 24347986202733459267797453)
                ·
                  refine ⟨9130494826025047225424045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24347986202733459267797453 9130494826025047225424045)
                  ·
                    refine ⟨3423935559759392709534017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9130494826025047225424045 3423935559759392709534017)
                    ·
                      refine ⟨2567951669819544532150513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3423935559759392709534017 2567951669819544532150513)
                      ·
                        rfl

theorem cell23_5001068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_5001068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001068 prefixEnd_5001068 := by exact prefixLift 5001068
  have htrace : WordTrace (prefixWord ++ tailWord_5001068) baseStart_5001068 baseEnd_5001068 := by
    simpa [prefixWord, tailWord_5001068, baseEnd_5001068] using wordTrace_append hprefix tailTrace_5001068
  have hstable : (prefixWord ++ tailWord_5001068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001068).length < 2 ^ (prefixWord ++ tailWord_5001068).sum := by decide
  have hdescent : baseEnd_5001068 < baseStart_5001068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001074 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_5001074 : Nat := 118140960795 + 5001074 * 2 ^ 59
def prefixEnd_5001074 : Nat := 4983230072969 + 3 ^ 40 * 5001074 * 2
def baseEnd_5001074 : Nat := 855984916901157169558495

theorem tailTrace_5001074 : CollatzResearch.WordTrace tailWord_5001074 prefixEnd_5001074 855984916901157169558495 := by
  unfold tailWord_5001074
  simp only [CollatzResearch.WordTrace]
  refine ⟨45601038470992622071176569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121602769255980325523137517 45601038470992622071176569)
  ·
    refine ⟨34200778853244466553382427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45601038470992622071176569 34200778853244466553382427)
    ·
      refine ⟨51301168279866699830073641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34200778853244466553382427 51301168279866699830073641)
      ·
        refine ⟨38475876209900024872555231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51301168279866699830073641 38475876209900024872555231)
        ·
          refine ⟨57713814314850037308832847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38475876209900024872555231 57713814314850037308832847)
          ·
            refine ⟨86570721472275055963249271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57713814314850037308832847 86570721472275055963249271)
            ·
              refine ⟨129856082208412583944873907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86570721472275055963249271 129856082208412583944873907)
              ·
                refine ⟨194784123312618875917310861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129856082208412583944873907 194784123312618875917310861)
                ·
                  refine ⟨73044046242232078468991573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194784123312618875917310861 73044046242232078468991573)
                  ·
                    refine ⟨855984916901157169558495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73044046242232078468991573 855984916901157169558495)
                    ·
                      rfl

theorem cell23_5001074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_5001074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001074 prefixEnd_5001074 := by exact prefixLift 5001074
  have htrace : WordTrace (prefixWord ++ tailWord_5001074) baseStart_5001074 baseEnd_5001074 := by
    simpa [prefixWord, tailWord_5001074, baseEnd_5001074] using wordTrace_append hprefix tailTrace_5001074
  have hstable : (prefixWord ++ tailWord_5001074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001074).length < 2 ^ (prefixWord ++ tailWord_5001074).sum := by decide
  have hdescent : baseEnd_5001074 < baseStart_5001074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001104 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 7]
def baseStart_5001104 : Nat := 118140960795 + 5001104 * 2 ^ 59
def prefixEnd_5001104 : Nat := 4983230072969 + 3 ^ 40 * 5001104 * 2
def baseEnd_5001104 : Nat := 285330017235900710144483

theorem tailTrace_5001104 : CollatzResearch.WordTrace tailWord_5001104 prefixEnd_5001104 285330017235900710144483 := by
  unfold tailWord_5001104
  simp only [CollatzResearch.WordTrace]
  refine ⟨91202624036930901704149183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121603498715907868938865577 91202624036930901704149183)
  ·
    refine ⟨136803936055396352556223775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91202624036930901704149183 136803936055396352556223775)
    ·
      refine ⟨205205904083094528834335663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136803936055396352556223775 205205904083094528834335663)
      ·
        refine ⟨307808856124641793251503495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205205904083094528834335663 307808856124641793251503495)
        ·
          refine ⟨461713284186962689877255243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307808856124641793251503495 461713284186962689877255243)
          ·
            refine ⟨692569926280444034815882865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461713284186962689877255243 692569926280444034815882865)
            ·
              refine ⟨519427444710333026111912149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692569926280444034815882865 519427444710333026111912149)
              ·
                refine ⟨12174080735398430299497941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 519427444710333026111912149 12174080735398430299497941)
                ·
                  refine ⟨285330017235900710144483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12174080735398430299497941 285330017235900710144483)
                  ·
                    rfl

theorem cell23_5001104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_5001104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001104 prefixEnd_5001104 := by exact prefixLift 5001104
  have htrace : WordTrace (prefixWord ++ tailWord_5001104) baseStart_5001104 baseEnd_5001104 := by
    simpa [prefixWord, tailWord_5001104, baseEnd_5001104] using wordTrace_append hprefix tailTrace_5001104
  have hstable : (prefixWord ++ tailWord_5001104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001104).length < 2 ^ (prefixWord ++ tailWord_5001104).sum := by decide
  have hdescent : baseEnd_5001104 < baseStart_5001104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001111 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_5001111 : Nat := 118140960795 + 5001111 * 2 ^ 59
def prefixEnd_5001111 : Nat := 4983230072969 + 3 ^ 40 * 5001111 * 2
def baseEnd_5001111 : Nat := 2567973749487687863912815

theorem tailTrace_5001111 : CollatzResearch.WordTrace tailWord_5001111 prefixEnd_5001111 2567973749487687863912815 := by
  unfold tailWord_5001111
  simp only [CollatzResearch.WordTrace]
  refine ⟨182405503384836443603803187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121603668923224295735868791 182405503384836443603803187)
  ·
    refine ⟨273608255077254665405704781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182405503384836443603803187 273608255077254665405704781)
    ·
      refine ⟨102603095653970499527139293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273608255077254665405704781 102603095653970499527139293)
      ·
        refine ⟨38476160870238937322677235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102603095653970499527139293 38476160870238937322677235)
        ·
          refine ⟨57714241305358405984015853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38476160870238937322677235 57714241305358405984015853)
          ·
            refine ⟨21642840489509402244005945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57714241305358405984015853 21642840489509402244005945)
            ·
              refine ⟨16232130367132051683004459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21642840489509402244005945 16232130367132051683004459)
              ·
                refine ⟨24348195550698077524506689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16232130367132051683004459 24348195550698077524506689)
                ·
                  refine ⟨18261146663023558143380017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24348195550698077524506689 18261146663023558143380017)
                  ·
                    refine ⟨13695859997267668607535013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18261146663023558143380017 13695859997267668607535013)
                    ·
                      refine ⟨2567973749487687863912815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13695859997267668607535013 2567973749487687863912815)
                      ·
                        rfl

theorem cell23_5001111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_5001111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001111 prefixEnd_5001111 := by exact prefixLift 5001111
  have htrace : WordTrace (prefixWord ++ tailWord_5001111) baseStart_5001111 baseEnd_5001111 := by
    simpa [prefixWord, tailWord_5001111, baseEnd_5001111] using wordTrace_append hprefix tailTrace_5001111
  have hstable : (prefixWord ++ tailWord_5001111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001111).length < 2 ^ (prefixWord ++ tailWord_5001111).sum := by decide
  have hdescent : baseEnd_5001111 < baseStart_5001111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001151 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 2, 5]
def baseStart_5001151 : Nat := 118140960795 + 5001151 * 2 ^ 59
def prefixEnd_5001151 : Nat := 4983230072969 + 3 ^ 40 * 5001151 * 2
def baseEnd_5001151 : Nat := 855998096237955902470877

theorem tailTrace_5001151 : CollatzResearch.WordTrace tailWord_5001151 prefixEnd_5001151 855998096237955902470877 := by
  unfold tailWord_5001151
  simp only [CollatzResearch.WordTrace]
  refine ⟨182406962304691530435259307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121604641536461020290172871 182406962304691530435259307)
  ·
    refine ⟨273610443457037295652888961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182406962304691530435259307 273610443457037295652888961)
    ·
      refine ⟨205207832592777971739666721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273610443457037295652888961 205207832592777971739666721)
      ·
        refine ⟨153905874444583478804750041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205207832592777971739666721 153905874444583478804750041)
        ·
          refine ⟨115429405833437609103562531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153905874444583478804750041 115429405833437609103562531)
          ·
            refine ⟨173144108750156413655343797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115429405833437609103562531 173144108750156413655343797)
            ·
              refine ⟨16232260195327163780188481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173144108750156413655343797 16232260195327163780188481)
              ·
                refine ⟨12174195146495372835141361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16232260195327163780188481 12174195146495372835141361)
                ·
                  refine ⟨9130646359871529626356021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12174195146495372835141361 9130646359871529626356021)
                  ·
                    refine ⟨855998096237955902470877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9130646359871529626356021 855998096237955902470877)
                    ·
                      rfl

theorem cell23_5001151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_5001151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001151 prefixEnd_5001151 := by exact prefixLift 5001151
  have htrace : WordTrace (prefixWord ++ tailWord_5001151) baseStart_5001151 baseEnd_5001151 := by
    simpa [prefixWord, tailWord_5001151, baseEnd_5001151] using wordTrace_append hprefix tailTrace_5001151
  have hstable : (prefixWord ++ tailWord_5001151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001151).length < 2 ^ (prefixWord ++ tailWord_5001151).sum := by decide
  have hdescent : baseEnd_5001151 < baseStart_5001151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001188 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_5001188 : Nat := 118140960795 + 5001188 * 2 ^ 59
def prefixEnd_5001188 : Nat := 4983230072969 + 3 ^ 40 * 5001188 * 2
def baseEnd_5001188 : Nat := 2568013287498084062649961

theorem tailTrace_5001188 : CollatzResearch.WordTrace tailWord_5001188 prefixEnd_5001188 2568013287498084062649961 := by
  unfold tailWord_5001188
  simp only [CollatzResearch.WordTrace]
  refine ⟨91204155902778742877178109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121605541203704990502904145 91204155902778742877178109)
  ·
    refine ⟨34201558463542028578941791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91204155902778742877178109 34201558463542028578941791)
    ·
      refine ⟨51302337695313042868412687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34201558463542028578941791 51302337695313042868412687)
      ·
        refine ⟨76953506542969564302619031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51302337695313042868412687 76953506542969564302619031)
        ·
          refine ⟨115430259814454346453928547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76953506542969564302619031 115430259814454346453928547)
          ·
            refine ⟨173145389721681519680892821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115430259814454346453928547 173145389721681519680892821)
            ·
              refine ⟨8116190143203821235041851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173145389721681519680892821 8116190143203821235041851)
              ·
                refine ⟨12174285214805731852562777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8116190143203821235041851 12174285214805731852562777)
                ·
                  refine ⟨9130713911104298889422083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12174285214805731852562777 9130713911104298889422083)
                  ·
                    refine ⟨13696070866656448334133125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9130713911104298889422083 13696070866656448334133125)
                    ·
                      refine ⟨2568013287498084062649961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13696070866656448334133125 2568013287498084062649961)
                      ·
                        rfl

theorem cell23_5001188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_5001188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001188 prefixEnd_5001188 := by exact prefixLift 5001188
  have htrace : WordTrace (prefixWord ++ tailWord_5001188) baseStart_5001188 baseEnd_5001188 := by
    simpa [prefixWord, tailWord_5001188, baseEnd_5001188] using wordTrace_append hprefix tailTrace_5001188
  have hstable : (prefixWord ++ tailWord_5001188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001188).length < 2 ^ (prefixWord ++ tailWord_5001188).sum := by decide
  have hdescent : baseEnd_5001188 < baseStart_5001188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001208 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_5001208 : Nat := 118140960795 + 5001208 * 2 ^ 59
def prefixEnd_5001208 : Nat := 4983230072969 + 3 ^ 40 * 5001208 * 2
def baseEnd_5001208 : Nat := 2568023557111173984399869

theorem tailTrace_5001208 : CollatzResearch.WordTrace tailWord_5001208 prefixEnd_5001208 2568023557111173984399869 := by
  unfold tailWord_5001208
  simp only [CollatzResearch.WordTrace]
  refine ⟨91204520632742514585042139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121606027510323352780056185 91204520632742514585042139)
  ·
    refine ⟨136806780949113771877563209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91204520632742514585042139 136806780949113771877563209)
    ·
      refine ⟨102605085711835328908172407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136806780949113771877563209 102605085711835328908172407)
      ·
        refine ⟨153907628567752993362258611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102605085711835328908172407 153907628567752993362258611)
        ·
          refine ⟨230861442851629490043387917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153907628567752993362258611 230861442851629490043387917)
          ·
            refine ⟨86573041069361058766270469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 230861442851629490043387917 86573041069361058766270469)
            ·
              refine ⟨16232445200505198518675713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86573041069361058766270469 16232445200505198518675713)
              ·
                refine ⟨12174333900378898889006785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16232445200505198518675713 12174333900378898889006785)
                ·
                  refine ⟨9130750425284174166755089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12174333900378898889006785 9130750425284174166755089)
                  ·
                    refine ⟨6848062818963130625066317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9130750425284174166755089 6848062818963130625066317)
                    ·
                      refine ⟨2568023557111173984399869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6848062818963130625066317 2568023557111173984399869)
                      ·
                        rfl

theorem cell23_5001208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_5001208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001208 prefixEnd_5001208 := by exact prefixLift 5001208
  have htrace : WordTrace (prefixWord ++ tailWord_5001208) baseStart_5001208 baseEnd_5001208 := by
    simpa [prefixWord, tailWord_5001208, baseEnd_5001208] using wordTrace_append hprefix tailTrace_5001208
  have hstable : (prefixWord ++ tailWord_5001208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001208).length < 2 ^ (prefixWord ++ tailWord_5001208).sum := by decide
  have hdescent : baseEnd_5001208 < baseStart_5001208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001211 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 6]
def baseStart_5001211 : Nat := 118140960795 + 5001211 * 2 ^ 59
def prefixEnd_5001211 : Nat := 4983230072969 + 3 ^ 40 * 5001211 * 2
def baseEnd_5001211 : Nat := 285336121950348608073595

theorem tailTrace_5001211 : CollatzResearch.WordTrace tailWord_5001211 prefixEnd_5001211 285336121950348608073595 := by
  unfold tailWord_5001211
  simp only [CollatzResearch.WordTrace]
  refine ⟨182409150684474160682443487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121606100456316107121628991 182409150684474160682443487)
  ·
    refine ⟨273613726026711241023665231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182409150684474160682443487 273613726026711241023665231)
    ·
      refine ⟨410420589040066861535497847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273613726026711241023665231 410420589040066861535497847)
      ·
        refine ⟨615630883560100292303246771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410420589040066861535497847 615630883560100292303246771)
        ·
          refine ⟨923446325340150438454870157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615630883560100292303246771 923446325340150438454870157)
          ·
            refine ⟨346292372002556414420576309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 923446325340150438454870157 346292372002556414420576309)
            ·
              refine ⟨32464909875239663851929029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 346292372002556414420576309 32464909875239663851929029)
              ·
                refine ⟨6087170601607436972236693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32464909875239663851929029 6087170601607436972236693)
                ·
                  refine ⟨285336121950348608073595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6087170601607436972236693 285336121950348608073595)
                  ·
                    rfl

theorem cell23_5001211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 6].length) (baseStart_5001211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001211 prefixEnd_5001211 := by exact prefixLift 5001211
  have htrace : WordTrace (prefixWord ++ tailWord_5001211) baseStart_5001211 baseEnd_5001211 := by
    simpa [prefixWord, tailWord_5001211, baseEnd_5001211] using wordTrace_append hprefix tailTrace_5001211
  have hstable : (prefixWord ++ tailWord_5001211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001211).length < 2 ^ (prefixWord ++ tailWord_5001211).sum := by decide
  have hdescent : baseEnd_5001211 < baseStart_5001211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001271 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 3, 6]
def baseStart_5001271 : Nat := 118140960795 + 5001271 * 2 ^ 59
def prefixEnd_5001271 : Nat := 4983230072969 + 3 ^ 40 * 5001271 * 2
def baseEnd_5001271 : Nat := 856018635464135745970693

theorem tailTrace_5001271 : CollatzResearch.WordTrace tailWord_5001271 prefixEnd_5001271 856018635464135745970693 := by
  unfold tailWord_5001271
  simp only [CollatzResearch.WordTrace]
  refine ⟨182411339064256790929627667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121607559376171193953085111 182411339064256790929627667)
  ·
    refine ⟨273617008596385186394441501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182411339064256790929627667 273617008596385186394441501)
    ·
      refine ⟨102606378223644444897915563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273617008596385186394441501 102606378223644444897915563)
      ·
        refine ⟨153909567335466667346873345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102606378223644444897915563 153909567335466667346873345)
        ·
          refine ⟨115432175501600000510155009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153909567335466667346873345 115432175501600000510155009)
          ·
            refine ⟨86574131626200000382616257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115432175501600000510155009 86574131626200000382616257)
            ·
              refine ⟨64930598719650000286962193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86574131626200000382616257 64930598719650000286962193)
              ·
                refine ⟨48697949039737500215221645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64930598719650000286962193 48697949039737500215221645)
                ·
                  refine ⟨18261730889901562580708117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48697949039737500215221645 18261730889901562580708117)
                  ·
                    refine ⟨856018635464135745970693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18261730889901562580708117 856018635464135745970693)
                    ·
                      rfl

theorem cell23_5001271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_5001271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001271 prefixEnd_5001271 := by exact prefixLift 5001271
  have htrace : WordTrace (prefixWord ++ tailWord_5001271) baseStart_5001271 baseEnd_5001271 := by
    simpa [prefixWord, tailWord_5001271, baseEnd_5001271] using wordTrace_append hprefix tailTrace_5001271
  have hstable : (prefixWord ++ tailWord_5001271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001271).length < 2 ^ (prefixWord ++ tailWord_5001271).sum := by decide
  have hdescent : baseEnd_5001271 < baseStart_5001271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001272 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_5001272 : Nat := 118140960795 + 5001272 * 2 ^ 59
def prefixEnd_5001272 : Nat := 4983230072969 + 3 ^ 40 * 5001272 * 2
def baseEnd_5001272 : Nat := 2568056419873061733999575

theorem tailTrace_5001272 : CollatzResearch.WordTrace tailWord_5001272 prefixEnd_5001272 2568056419873061733999575 := by
  unfold tailWord_5001272
  simp only [CollatzResearch.WordTrace]
  refine ⟨91205687768626584050207035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121607583691502112066942713 91205687768626584050207035)
  ·
    refine ⟨136808531652939876075310553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91205687768626584050207035 136808531652939876075310553)
    ·
      refine ⟨102606398739704907056482915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136808531652939876075310553 102606398739704907056482915)
      ·
        refine ⟨153909598109557360584724373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102606398739704907056482915 153909598109557360584724373)
        ·
          refine ⟨7214512411385501277408955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153909598109557360584724373 7214512411385501277408955)
          ·
            refine ⟨10821768617078251916113433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214512411385501277408955 10821768617078251916113433)
            ·
              refine ⟨8116326462808688937085075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10821768617078251916113433 8116326462808688937085075)
              ·
                refine ⟨12174489694213033405627613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8116326462808688937085075 12174489694213033405627613)
                ·
                  refine ⟨4565433635329887527110355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12174489694213033405627613 4565433635329887527110355)
                  ·
                    refine ⟨6848150452994831290665533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4565433635329887527110355 6848150452994831290665533)
                    ·
                      refine ⟨2568056419873061733999575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6848150452994831290665533 2568056419873061733999575)
                      ·
                        rfl

theorem cell23_5001272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_5001272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001272 prefixEnd_5001272 := by exact prefixLift 5001272
  have htrace : WordTrace (prefixWord ++ tailWord_5001272) baseStart_5001272 baseEnd_5001272 := by
    simpa [prefixWord, tailWord_5001272, baseEnd_5001272] using wordTrace_append hprefix tailTrace_5001272
  have hstable : (prefixWord ++ tailWord_5001272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001272).length < 2 ^ (prefixWord ++ tailWord_5001272).sum := by decide
  have hdescent : baseEnd_5001272 < baseStart_5001272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001291 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6]
def baseStart_5001291 : Nat := 118140960795 + 5001291 * 2 ^ 59
def prefixEnd_5001291 : Nat := 4983230072969 + 3 ^ 40 * 5001291 * 2
def baseEnd_5001291 : Nat := 2568066176005497159661987

theorem tailTrace_5001291 : CollatzResearch.WordTrace tailWord_5001291 prefixEnd_5001291 2568066176005497159661987 := by
  unfold tailWord_5001291
  simp only [CollatzResearch.WordTrace]
  refine ⟨182412068524184334345355727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121608045682789556230237151 182412068524184334345355727)
  ·
    refine ⟨273618102786276501518033591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182412068524184334345355727 273618102786276501518033591)
    ·
      refine ⟨410427154179414752277050387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273618102786276501518033591 410427154179414752277050387)
      ·
        refine ⟨615640731269122128415575581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410427154179414752277050387 615640731269122128415575581)
        ·
          refine ⟨230865274225920798155840843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 615640731269122128415575581 230865274225920798155840843)
          ·
            refine ⟨346297911338881197233761265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230865274225920798155840843 346297911338881197233761265)
            ·
              refine ⟨259723433504160897925320949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346297911338881197233761265 259723433504160897925320949)
              ·
                refine ⟨24349071891015084180498839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259723433504160897925320949 24349071891015084180498839)
                ·
                  refine ⟨36523607836522626270748259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24349071891015084180498839 36523607836522626270748259)
                  ·
                    refine ⟨54785411754783939406122389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36523607836522626270748259 54785411754783939406122389)
                    ·
                      refine ⟨2568066176005497159661987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54785411754783939406122389 2568066176005497159661987)
                      ·
                        rfl

theorem cell23_5001291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_5001291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001291 prefixEnd_5001291 := by exact prefixLift 5001291
  have htrace : WordTrace (prefixWord ++ tailWord_5001291) baseStart_5001291 baseEnd_5001291 := by
    simpa [prefixWord, tailWord_5001291, baseEnd_5001291] using wordTrace_append hprefix tailTrace_5001291
  have hstable : (prefixWord ++ tailWord_5001291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001291).length < 2 ^ (prefixWord ++ tailWord_5001291).sum := by decide
  have hdescent : baseEnd_5001291 < baseStart_5001291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001315 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 3]
def baseStart_5001315 : Nat := 118140960795 + 5001315 * 2 ^ 59
def prefixEnd_5001315 : Nat := 4983230072969 + 3 ^ 40 * 5001315 * 2
def baseEnd_5001315 : Nat := 2568078499541205065761877

theorem tailTrace_5001315 : CollatzResearch.WordTrace tailWord_5001315 prefixEnd_5001315 2568078499541205065761877 := by
  unfold tailWord_5001315
  simp only [CollatzResearch.WordTrace]
  refine ⟨182412943876097386444229399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121608629250731590962819599 182412943876097386444229399)
  ·
    refine ⟨273619415814146079666344099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182412943876097386444229399 273619415814146079666344099)
    ·
      refine ⟨410429123721219119499516149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273619415814146079666344099 410429123721219119499516149)
      ·
        refine ⟨38477730348864292453079639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 410429123721219119499516149 38477730348864292453079639)
        ·
          refine ⟨57716595523296438679619459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38477730348864292453079639 57716595523296438679619459)
          ·
            refine ⟨86574893284944658019429189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57716595523296438679619459 86574893284944658019429189)
            ·
              refine ⟨16232792490927123378642973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86574893284944658019429189 16232792490927123378642973)
              ·
                refine ⟨6087297184097671266991115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16232792490927123378642973 6087297184097671266991115)
                ·
                  refine ⟨9130945776146506900486673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6087297184097671266991115 9130945776146506900486673)
                  ·
                    refine ⟨6848209332109880175365005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9130945776146506900486673 6848209332109880175365005)
                    ·
                      refine ⟨2568078499541205065761877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6848209332109880175365005 2568078499541205065761877)
                      ·
                        rfl

theorem cell23_5001315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_5001315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001315 prefixEnd_5001315 := by exact prefixLift 5001315
  have htrace : WordTrace (prefixWord ++ tailWord_5001315) baseStart_5001315 baseEnd_5001315 := by
    simpa [prefixWord, tailWord_5001315, baseEnd_5001315] using wordTrace_append hprefix tailTrace_5001315
  have hstable : (prefixWord ++ tailWord_5001315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001315).length < 2 ^ (prefixWord ++ tailWord_5001315).sum := by decide
  have hdescent : baseEnd_5001315 < baseStart_5001315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001380 : List Nat := [2, 3, 1, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_5001380 : Nat := 118140960795 + 5001380 * 2 ^ 59
def prefixEnd_5001380 : Nat := 4983230072969 + 3 ^ 40 * 5001380 * 2
def baseEnd_5001380 : Nat := 2568111875783747311449079

theorem tailTrace_5001380 : CollatzResearch.WordTrace tailWord_5001380 prefixEnd_5001380 2568111875783747311449079 := by
  unfold tailWord_5001380
  simp only [CollatzResearch.WordTrace]
  refine ⟨91207657310430951272672797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121610209747241268363563729 91207657310430951272672797)
  ·
    refine ⟨34202871491411606727252299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91207657310430951272672797 34202871491411606727252299)
    ·
      refine ⟨51304307237117410090878449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34202871491411606727252299 51304307237117410090878449)
      ·
        refine ⟨38478230427838057568158837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51304307237117410090878449 38478230427838057568158837)
        ·
          refine ⟨3607334102609817897014891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38478230427838057568158837 3607334102609817897014891)
          ·
            refine ⟨5411001153914726845522337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607334102609817897014891 5411001153914726845522337)
            ·
              refine ⟨4058250865436045134141753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5411001153914726845522337 4058250865436045134141753)
              ·
                refine ⟨3043688149077033850606315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4058250865436045134141753 3043688149077033850606315)
                ·
                  refine ⟨4565532223615550775909473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043688149077033850606315 4565532223615550775909473)
                  ·
                    refine ⟨3424149167711663081932105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4565532223615550775909473 3424149167711663081932105)
                    ·
                      refine ⟨2568111875783747311449079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424149167711663081932105 2568111875783747311449079)
                      ·
                        rfl

theorem cell23_5001380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_5001380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001380 prefixEnd_5001380 := by exact prefixLift 5001380
  have htrace : WordTrace (prefixWord ++ tailWord_5001380) baseStart_5001380 baseEnd_5001380 := by
    simpa [prefixWord, tailWord_5001380, baseEnd_5001380] using wordTrace_append hprefix tailTrace_5001380
  have hstable : (prefixWord ++ tailWord_5001380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001380).length < 2 ^ (prefixWord ++ tailWord_5001380).sum := by decide
  have hdescent : baseEnd_5001380 < baseStart_5001380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001408 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 9]
def baseStart_5001408 : Nat := 118140960795 + 5001408 * 2 ^ 59
def prefixEnd_5001408 : Nat := 4983230072969 + 3 ^ 40 * 5001408 * 2
def baseEnd_5001408 : Nat := 285347361471341466877661

theorem tailTrace_5001408 : CollatzResearch.WordTrace tailWord_5001408 prefixEnd_5001408 285347361471341466877661 := by
  unfold tailWord_5001408
  simp only [CollatzResearch.WordTrace]
  refine ⟨91208167932380231663682439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121610890576506975551576585 91208167932380231663682439)
  ·
    refine ⟨136812251898570347495523659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91208167932380231663682439 136812251898570347495523659)
    ·
      refine ⟨205218377847855521243285489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136812251898570347495523659 205218377847855521243285489)
      ·
        refine ⟨153913783385891640932464117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205218377847855521243285489 153913783385891640932464117)
        ·
          refine ⟨14429417192427341337418511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153913783385891640932464117 14429417192427341337418511)
          ·
            refine ⟨21644125788641012006127767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14429417192427341337418511 21644125788641012006127767)
            ·
              refine ⟨32466188682961518009191651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21644125788641012006127767 32466188682961518009191651)
              ·
                refine ⟨48699283024442277013787477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32466188682961518009191651 48699283024442277013787477)
                ·
                  refine ⟨285347361471341466877661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48699283024442277013787477 285347361471341466877661)
                  ·
                    rfl

theorem cell23_5001408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_5001408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001408 prefixEnd_5001408 := by exact prefixLift 5001408
  have htrace : WordTrace (prefixWord ++ tailWord_5001408) baseStart_5001408 baseEnd_5001408 := by
    simpa [prefixWord, tailWord_5001408, baseEnd_5001408] using wordTrace_append hprefix tailTrace_5001408
  have hstable : (prefixWord ++ tailWord_5001408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001408).length < 2 ^ (prefixWord ++ tailWord_5001408).sum := by decide
  have hdescent : baseEnd_5001408 < baseStart_5001408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001425 : List Nat := [1, 2, 2, 1, 2, 2, 3, 5, 5]
def baseStart_5001425 : Nat := 118140960795 + 5001425 * 2 ^ 59
def prefixEnd_5001425 : Nat := 4983230072969 + 3 ^ 40 * 5001425 * 2
def baseEnd_5001425 : Nat := 285348331379244403931819

theorem tailTrace_5001425 : CollatzResearch.WordTrace tailWord_5001425 prefixEnd_5001425 285348331379244403931819 := by
  unfold tailWord_5001425
  simp only [CollatzResearch.WordTrace]
  refine ⟨182416955905698875230733729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121611303937132583487155819 182416955905698875230733729)
  ·
    refine ⟨136812716929274156423050297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182416955905698875230733729 136812716929274156423050297)
    ·
      refine ⟨102609537696955617317287723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136812716929274156423050297 102609537696955617317287723)
      ·
        refine ⟨153914306545433425975931585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102609537696955617317287723 153914306545433425975931585)
        ·
          refine ⟨115435729909075069481948689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153914306545433425975931585 115435729909075069481948689)
          ·
            refine ⟨86576797431806302111461517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115435729909075069481948689 86576797431806302111461517)
            ·
              refine ⟨32466299036927363291798069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86576797431806302111461517 32466299036927363291798069)
              ·
                refine ⟨3043715534711940308606069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32466299036927363291798069 3043715534711940308606069)
                ·
                  refine ⟨285348331379244403931819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3043715534711940308606069 285348331379244403931819)
                  ·
                    rfl

theorem cell23_5001425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 5].length) (baseStart_5001425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001425 prefixEnd_5001425 := by exact prefixLift 5001425
  have htrace : WordTrace (prefixWord ++ tailWord_5001425) baseStart_5001425 baseEnd_5001425 := by
    simpa [prefixWord, tailWord_5001425, baseEnd_5001425] using wordTrace_append hprefix tailTrace_5001425
  have hstable : (prefixWord ++ tailWord_5001425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001425).length < 2 ^ (prefixWord ++ tailWord_5001425).sum := by decide
  have hdescent : baseEnd_5001425 < baseStart_5001425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001453 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5001453 : Nat := 118140960795 + 5001453 * 2 ^ 59
def prefixEnd_5001453 : Nat := 4983230072969 + 3 ^ 40 * 5001453 * 2
def baseEnd_5001453 : Nat := 2568149359871525525836243

theorem tailTrace_5001453 : CollatzResearch.WordTrace tailWord_5001453 prefixEnd_5001453 2568149359871525525836243 := by
  unfold tailWord_5001453
  simp only [CollatzResearch.WordTrace]
  refine ⟨182417977149597436012753013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121611984766398290675168675 182417977149597436012753013)
  ·
    refine ⟨17101685357774759626195595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 182417977149597436012753013 17101685357774759626195595)
    ·
      refine ⟨25652528036662139439293393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17101685357774759626195595 25652528036662139439293393)
      ·
        refine ⟨19239396027496604579470045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25652528036662139439293393 19239396027496604579470045)
        ·
          refine ⟨7214773510311226717301267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19239396027496604579470045 7214773510311226717301267)
          ·
            refine ⟨10822160265466840075951901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214773510311226717301267 10822160265466840075951901)
            ·
              refine ⟨4058310099550065028481963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10822160265466840075951901 4058310099550065028481963)
              ·
                refine ⟨6087465149325097542722945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058310099550065028481963 6087465149325097542722945)
                ·
                  refine ⟨4565598861993823157042209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6087465149325097542722945 4565598861993823157042209)
                  ·
                    refine ⟨3424199146495367367781657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4565598861993823157042209 3424199146495367367781657)
                    ·
                      refine ⟨2568149359871525525836243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424199146495367367781657 2568149359871525525836243)
                      ·
                        rfl

theorem cell23_5001453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5001453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001453 prefixEnd_5001453 := by exact prefixLift 5001453
  have htrace : WordTrace (prefixWord ++ tailWord_5001453) baseStart_5001453 baseEnd_5001453 := by
    simpa [prefixWord, tailWord_5001453, baseEnd_5001453] using wordTrace_append hprefix tailTrace_5001453
  have hstable : (prefixWord ++ tailWord_5001453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001453).length < 2 ^ (prefixWord ++ tailWord_5001453).sum := by decide
  have hdescent : baseEnd_5001453 < baseStart_5001453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001462 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_5001462 : Nat := 118140960795 + 5001462 * 2 ^ 59
def prefixEnd_5001462 : Nat := 4983230072969 + 3 ^ 40 * 5001462 * 2
def baseEnd_5001462 : Nat := 2568153981197415990623701

theorem tailTrace_5001462 : CollatzResearch.WordTrace tailWord_5001462 prefixEnd_5001462 2568153981197415990623701 := by
  unfold tailWord_5001462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11401144087910301909364415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 121612203604376553699887093 11401144087910301909364415)
  ·
    refine ⟨17101716131865452864046623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11401144087910301909364415 17101716131865452864046623)
    ·
      refine ⟨25652574197798179296069935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17101716131865452864046623 25652574197798179296069935)
      ·
        refine ⟨38478861296697268944104903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25652574197798179296069935 38478861296697268944104903)
        ·
          refine ⟨57718291945045903416157355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38478861296697268944104903 57718291945045903416157355)
          ·
            refine ⟨86577437917568855124236033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57718291945045903416157355 86577437917568855124236033)
            ·
              refine ⟨64933078438176641343177025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86577437917568855124236033 64933078438176641343177025)
              ·
                refine ⟨48699808828632481007382769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64933078438176641343177025 48699808828632481007382769)
                ·
                  refine ⟨36524856621474360755537077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48699808828632481007382769 36524856621474360755537077)
                  ·
                    refine ⟨3424205308263221320831601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36524856621474360755537077 3424205308263221320831601)
                    ·
                      refine ⟨2568153981197415990623701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424205308263221320831601 2568153981197415990623701)
                      ·
                        rfl

theorem cell23_5001462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_5001462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001462 prefixEnd_5001462 := by exact prefixLift 5001462
  have htrace : WordTrace (prefixWord ++ tailWord_5001462) baseStart_5001462 baseEnd_5001462 := by
    simpa [prefixWord, tailWord_5001462, baseEnd_5001462] using wordTrace_append hprefix tailTrace_5001462
  have hstable : (prefixWord ++ tailWord_5001462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001462).length < 2 ^ (prefixWord ++ tailWord_5001462).sum := by decide
  have hdescent : baseEnd_5001462 < baseStart_5001462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001475 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 4]
def baseStart_5001475 : Nat := 118140960795 + 5001475 * 2 ^ 59
def prefixEnd_5001475 : Nat := 4983230072969 + 3 ^ 40 * 5001475 * 2
def baseEnd_5001475 : Nat := 2568160656445924439761141

theorem tailTrace_5001475 : CollatzResearch.WordTrace tailWord_5001475 prefixEnd_5001475 2568160656445924439761141 := by
  unfold tailWord_5001475
  simp only [CollatzResearch.WordTrace]
  refine ⟨182418779555517733770053879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121612519703678489180035919 182418779555517733770053879)
  ·
    refine ⟨273628169333276600655080819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182418779555517733770053879 273628169333276600655080819)
    ·
      refine ⟨410442253999914900982621229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273628169333276600655080819 410442253999914900982621229)
      ·
        refine ⟨153915845249968087868482961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410442253999914900982621229 153915845249968087868482961)
        ·
          refine ⟨115436883937476065901362221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153915845249968087868482961 115436883937476065901362221)
          ·
            refine ⟨43288831476553524713010833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115436883937476065901362221 43288831476553524713010833)
            ·
              refine ⟨32466623607415143534758125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43288831476553524713010833 32466623607415143534758125)
              ·
                refine ⟨12174983852780678825534297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32466623607415143534758125 12174983852780678825534297)
                ·
                  refine ⟨9131237889585509119150723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12174983852780678825534297 9131237889585509119150723)
                  ·
                    refine ⟨13696856834378263678726085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9131237889585509119150723 13696856834378263678726085)
                    ·
                      refine ⟨2568160656445924439761141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13696856834378263678726085 2568160656445924439761141)
                      ·
                        rfl

theorem cell23_5001475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_5001475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001475 prefixEnd_5001475 := by exact prefixLift 5001475
  have htrace : WordTrace (prefixWord ++ tailWord_5001475) baseStart_5001475 baseEnd_5001475 := by
    simpa [prefixWord, tailWord_5001475, baseEnd_5001475] using wordTrace_append hprefix tailTrace_5001475
  have hstable : (prefixWord ++ tailWord_5001475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001475).length < 2 ^ (prefixWord ++ tailWord_5001475).sum := by decide
  have hdescent : baseEnd_5001475 < baseStart_5001475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001476 : List Nat := [2, 3, 2, 2, 4, 1, 1, 3, 5]
def baseStart_5001476 : Nat := 118140960795 + 5001476 * 2 ^ 59
def prefixEnd_5001476 : Nat := 4983230072969 + 3 ^ 40 * 5001476 * 2
def baseEnd_5001476 : Nat := 285351241102953215094293

theorem tailTrace_5001476 : CollatzResearch.WordTrace tailWord_5001476 prefixEnd_5001476 285351241102953215094293 := by
  unfold tailWord_5001476
  simp only [CollatzResearch.WordTrace]
  refine ⟨91209408014257055470420141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121612544019009407293893521 91209408014257055470420141)
  ·
    refine ⟨34203528005346395801407553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91209408014257055470420141 34203528005346395801407553)
    ·
      refine ⟨25652646004009796851055665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34203528005346395801407553 25652646004009796851055665)
      ·
        refine ⟨19239484503007347638291749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25652646004009796851055665 19239484503007347638291749)
        ·
          refine ⟨3607403344313877682179703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19239484503007347638291749 3607403344313877682179703)
          ·
            refine ⟨5411105016470816523269555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607403344313877682179703 5411105016470816523269555)
            ·
              refine ⟨8116657524706224784904333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411105016470816523269555 8116657524706224784904333)
              ·
                refine ⟨3043746571764834294339125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8116657524706224784904333 3043746571764834294339125)
                ·
                  refine ⟨285351241102953215094293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3043746571764834294339125 285351241102953215094293)
                  ·
                    rfl

theorem cell23_5001476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_5001476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001476 prefixEnd_5001476 := by exact prefixLift 5001476
  have htrace : WordTrace (prefixWord ++ tailWord_5001476) baseStart_5001476 baseEnd_5001476 := by
    simpa [prefixWord, tailWord_5001476, baseEnd_5001476] using wordTrace_append hprefix tailTrace_5001476
  have hstable : (prefixWord ++ tailWord_5001476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001476).length < 2 ^ (prefixWord ++ tailWord_5001476).sum := by decide
  have hdescent : baseEnd_5001476 < baseStart_5001476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001529 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5001529 : Nat := 118140960795 + 5001529 * 2 ^ 59
def prefixEnd_5001529 : Nat := 4983230072969 + 3 ^ 40 * 5001529 * 2
def baseEnd_5001529 : Nat := 2568188384401267228485893

theorem tailTrace_5001529 : CollatzResearch.WordTrace tailWord_5001529 prefixEnd_5001529 2568188384401267228485893 := by
  unfold tailWord_5001529
  simp only [CollatzResearch.WordTrace]
  refine ⟨182420749097322100992519641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121613832731548067328346427 182420749097322100992519641)
  ·
    refine ⟨136815561822991575744389731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182420749097322100992519641 136815561822991575744389731)
    ·
      refine ⟨205223342734487363616584597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136815561822991575744389731 205223342734487363616584597)
      ·
        refine ⟨9619844190679095169527403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 205223342734487363616584597 9619844190679095169527403)
        ·
          refine ⟨14429766286018642754291105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9619844190679095169527403 14429766286018642754291105)
          ·
            refine ⟨10822324714513982065718329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14429766286018642754291105 10822324714513982065718329)
            ·
              refine ⟨8116743535885486549288747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10822324714513982065718329 8116743535885486549288747)
              ·
                refine ⟨12175115303828229823933121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8116743535885486549288747 12175115303828229823933121)
                ·
                  refine ⟨9131336477871172367949841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12175115303828229823933121 9131336477871172367949841)
                  ·
                    refine ⟨6848502358403379275962381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9131336477871172367949841 6848502358403379275962381)
                    ·
                      refine ⟨2568188384401267228485893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6848502358403379275962381 2568188384401267228485893)
                      ·
                        rfl

theorem cell23_5001529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5001529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001529 prefixEnd_5001529 := by exact prefixLift 5001529
  have htrace : WordTrace (prefixWord ++ tailWord_5001529) baseStart_5001529 baseEnd_5001529 := by
    simpa [prefixWord, tailWord_5001529, baseEnd_5001529] using wordTrace_append hprefix tailTrace_5001529
  have hstable : (prefixWord ++ tailWord_5001529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001529).length < 2 ^ (prefixWord ++ tailWord_5001529).sum := by decide
  have hdescent : baseEnd_5001529 < baseStart_5001529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001586 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_5001586 : Nat := 118140960795 + 5001586 * 2 ^ 59
def prefixEnd_5001586 : Nat := 4983230072969 + 3 ^ 40 * 5001586 * 2
def baseEnd_5001586 : Nat := 2568217652798573505473131

theorem tailTrace_5001586 : CollatzResearch.WordTrace tailWord_5001586 prefixEnd_5001586 2568217652798573505473131 := by
  unfold tailWord_5001586
  simp only [CollatzResearch.WordTrace]
  refine ⟨45605707014528899931836153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121615218705410399818229741 45605707014528899931836153)
  ·
    refine ⟨34204280260896674948877115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45605707014528899931836153 34204280260896674948877115)
    ·
      refine ⟨51306420391345012423315673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34204280260896674948877115 51306420391345012423315673)
      ·
        refine ⟨38479815293508759317486755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51306420391345012423315673 38479815293508759317486755)
        ·
          refine ⟨57719722940263138976230133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38479815293508759317486755 57719722940263138976230133)
          ·
            refine ⟨5411224025649669279021575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57719722940263138976230133 5411224025649669279021575)
            ·
              refine ⟨8116836038474503918532363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411224025649669279021575 8116836038474503918532363)
              ·
                refine ⟨12175254057711755877798545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8116836038474503918532363 12175254057711755877798545)
                ·
                  refine ⟨9131440543283816908348909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12175254057711755877798545 9131440543283816908348909)
                  ·
                    refine ⟨3424290203731431340630841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9131440543283816908348909 3424290203731431340630841)
                    ·
                      refine ⟨2568217652798573505473131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3424290203731431340630841 2568217652798573505473131)
                      ·
                        rfl

theorem cell23_5001586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_5001586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001586 prefixEnd_5001586 := by exact prefixLift 5001586
  have htrace : WordTrace (prefixWord ++ tailWord_5001586) baseStart_5001586 baseEnd_5001586 := by
    simpa [prefixWord, tailWord_5001586, baseEnd_5001586] using wordTrace_append hprefix tailTrace_5001586
  have hstable : (prefixWord ++ tailWord_5001586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001586).length < 2 ^ (prefixWord ++ tailWord_5001586).sum := by decide
  have hdescent : baseEnd_5001586 < baseStart_5001586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5001609 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 2, 4]
def baseStart_5001609 : Nat := 118140960795 + 5001609 * 2 ^ 59
def prefixEnd_5001609 : Nat := 4983230072969 + 3 ^ 40 * 5001609 * 2
def baseEnd_5001609 : Nat := 856076487617875638495175

theorem tailTrace_5001609 : CollatzResearch.WordTrace tailWord_5001609 prefixEnd_5001609 856076487617875638495175 := by
  unfold tailWord_5001609
  simp only [CollatzResearch.WordTrace]
  refine ⟨182423666937032274655431881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121615777958021516436954587 182423666937032274655431881)
  ·
    refine ⟨136817750202774205991573911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182423666937032274655431881 136817750202774205991573911)
    ·
      refine ⟨205226625304161308987360867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136817750202774205991573911 205226625304161308987360867)
      ·
        refine ⟨307839937956241963481041301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205226625304161308987360867 307839937956241963481041301)
        ·
          refine ⟨14429997091698842038173811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 307839937956241963481041301 14429997091698842038173811)
          ·
            refine ⟨21644995637548263057260717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14429997091698842038173811 21644995637548263057260717)
            ·
              refine ⟨8116873364080598646472769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21644995637548263057260717 8116873364080598646472769)
              ·
                refine ⟨6087655023060448984854577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8116873364080598646472769 6087655023060448984854577)
                ·
                  refine ⟨4565741267295336738640933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6087655023060448984854577 4565741267295336738640933)
                  ·
                    refine ⟨856076487617875638495175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4565741267295336738640933 856076487617875638495175)
                    ·
                      rfl

theorem cell23_5001609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_5001609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5001609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5001609 prefixEnd_5001609 := by exact prefixLift 5001609
  have htrace : WordTrace (prefixWord ++ tailWord_5001609) baseStart_5001609 baseEnd_5001609 := by
    simpa [prefixWord, tailWord_5001609, baseEnd_5001609] using wordTrace_append hprefix tailTrace_5001609
  have hstable : (prefixWord ++ tailWord_5001609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5001609).length < 2 ^ (prefixWord ++ tailWord_5001609).sum := by decide
  have hdescent : baseEnd_5001609 < baseStart_5001609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5001609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
