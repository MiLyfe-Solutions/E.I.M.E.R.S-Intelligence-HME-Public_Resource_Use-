import V185TrunkScan22Chunk033

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_304878 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_304878 : Nat := 118140960795 + 304878 * 2 ^ 59
def prefixEnd_304878 : Nat := 4983230072969 + 3 ^ 40 * 304878 * 2
def baseEnd_304878 : Nat := 104365969987708931415265

theorem tailTrace_304878 : CollatzResearch.WordTrace tailWord_304878 prefixEnd_304878 104365969987708931415265 := by
  unfold tailWord_304878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1389976773685818732760411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7413209459657699908055525 1389976773685818732760411)
  ·
    refine ⟨2084965160528728099140617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1389976773685818732760411 2084965160528728099140617)
    ·
      refine ⟨1563723870396546074355463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2084965160528728099140617 1563723870396546074355463)
      ·
        refine ⟨2345585805594819111533195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563723870396546074355463 2345585805594819111533195)
        ·
          refine ⟨3518378708392228667299793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345585805594819111533195 3518378708392228667299793)
          ·
            refine ⟨2638784031294171500474845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518378708392228667299793 2638784031294171500474845)
            ·
              refine ⟨989544011735314312678067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2638784031294171500474845 989544011735314312678067)
              ·
                refine ⟨1484316017602971469017101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989544011735314312678067 1484316017602971469017101)
                ·
                  refine ⟨556618506601114300881413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1484316017602971469017101 556618506601114300881413)
                  ·
                    refine ⟨104365969987708931415265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 556618506601114300881413 104365969987708931415265)
                    ·
                      rfl

theorem cell22_304878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_304878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304878 prefixEnd_304878 := by exact prefixLift 304878
  have htrace : WordTrace (prefixWord ++ tailWord_304878) baseStart_304878 baseEnd_304878 := by
    simpa [prefixWord, tailWord_304878, baseEnd_304878] using wordTrace_append hprefix tailTrace_304878
  have hstable : (prefixWord ++ tailWord_304878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304878).length < 2 ^ (prefixWord ++ tailWord_304878).sum := by decide
  have hdescent : baseEnd_304878 < baseStart_304878 := by decide
  rcases family_descends (prefixWord ++ tailWord_304878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304908 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_304908 : Nat := 118140960795 + 304908 * 2 ^ 59
def prefixEnd_304908 : Nat := 4983230072969 + 3 ^ 40 * 304908 * 2
def baseEnd_304908 : Nat := 104376239600798853165173

theorem tailTrace_304908 : CollatzResearch.WordTrace tailWord_304908 prefixEnd_304908 104376239600798853165173 := by
  unfold tailWord_304908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560454189688932492837689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7413938919585243323783585 5560454189688932492837689)
  ·
    refine ⟨4170340642266699369628267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5560454189688932492837689 4170340642266699369628267)
    ·
      refine ⟨6255510963400049054442401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4170340642266699369628267 6255510963400049054442401)
      ·
        refine ⟨4691633222550036790831801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6255510963400049054442401 4691633222550036790831801)
        ·
          refine ⟨3518724916912527593123851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4691633222550036790831801 3518724916912527593123851)
          ·
            refine ⟨5278087375368791389685777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518724916912527593123851 5278087375368791389685777)
            ·
              refine ⟨3958565531526593542264333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278087375368791389685777 3958565531526593542264333)
              ·
                refine ⟨1484462074322472578349125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3958565531526593542264333 1484462074322472578349125)
                ·
                  refine ⟨278336638935463608440461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484462074322472578349125 278336638935463608440461)
                  ·
                    refine ⟨104376239600798853165173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278336638935463608440461 104376239600798853165173)
                    ·
                      rfl

theorem cell22_304908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_304908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304908 prefixEnd_304908 := by exact prefixLift 304908
  have htrace : WordTrace (prefixWord ++ tailWord_304908) baseStart_304908 baseEnd_304908 := by
    simpa [prefixWord, tailWord_304908, baseEnd_304908] using wordTrace_append hprefix tailTrace_304908
  have hstable : (prefixWord ++ tailWord_304908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304908).length < 2 ^ (prefixWord ++ tailWord_304908).sum := by decide
  have hdescent : baseEnd_304908 < baseStart_304908 := by decide
  rcases family_descends (prefixWord ++ tailWord_304908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304940 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_304940 : Nat := 118140960795 + 304940 * 2 ^ 59
def prefixEnd_304940 : Nat := 4983230072969 + 3 ^ 40 * 304940 * 2
def baseEnd_304940 : Nat := 104387193854761436365075

theorem tailTrace_304940 : CollatzResearch.WordTrace tailWord_304940 prefixEnd_304940 104387193854761436365075 := by
  unfold tailWord_304940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5561037757630967225420137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7414717010174622967226849 5561037757630967225420137)
  ·
    refine ⟨4170778318223225419065103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5561037757630967225420137 4170778318223225419065103)
    ·
      refine ⟨6256167477334838128597655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4170778318223225419065103 6256167477334838128597655)
      ·
        refine ⟨9384251216002257192896483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256167477334838128597655 9384251216002257192896483)
        ·
          refine ⟨14076376824003385789344725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9384251216002257192896483 14076376824003385789344725)
          ·
            refine ⟨329915081812579354437767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14076376824003385789344725 329915081812579354437767)
            ·
              refine ⟨494872622718869031656651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329915081812579354437767 494872622718869031656651)
              ·
                refine ⟨742308934078303547484977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494872622718869031656651 742308934078303547484977)
                ·
                  refine ⟨556731700558727660613733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 742308934078303547484977 556731700558727660613733)
                  ·
                    refine ⟨104387193854761436365075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 556731700558727660613733 104387193854761436365075)
                    ·
                      rfl

theorem cell22_304940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_304940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304940 prefixEnd_304940 := by exact prefixLift 304940
  have htrace : WordTrace (prefixWord ++ tailWord_304940) baseStart_304940 baseEnd_304940 := by
    simpa [prefixWord, tailWord_304940, baseEnd_304940] using wordTrace_append hprefix tailTrace_304940
  have hstable : (prefixWord ++ tailWord_304940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304940).length < 2 ^ (prefixWord ++ tailWord_304940).sum := by decide
  have hdescent : baseEnd_304940 < baseStart_304940 := by decide
  rcases family_descends (prefixWord ++ tailWord_304940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304951 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 8]
def baseStart_304951 : Nat := 118140960795 + 304951 * 2 ^ 59
def prefixEnd_304951 : Nat := 4983230072969 + 3 ^ 40 * 304951 * 2
def baseEnd_304951 : Nat := 104390959379561074340041

theorem tailTrace_304951 : CollatzResearch.WordTrace tailWord_304951 prefixEnd_304951 104390959379561074340041 := by
  unfold tailWord_304951
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122476718222083329490707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7414984478814722219660471 11122476718222083329490707)
  ·
    refine ⟨16683715077333124994236061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11122476718222083329490707 16683715077333124994236061)
    ·
      refine ⟨6256393153999921872838523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16683715077333124994236061 6256393153999921872838523)
      ·
        refine ⟨9384589730999882809257785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256393153999921872838523 9384589730999882809257785)
        ·
          refine ⟨7038442298249912106943339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9384589730999882809257785 7038442298249912106943339)
          ·
            refine ⟨10557663447374868160415009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038442298249912106943339 10557663447374868160415009)
            ·
              refine ⟨7918247585531151120311257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10557663447374868160415009 7918247585531151120311257)
              ·
                refine ⟨5938685689148363340233443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7918247585531151120311257 5938685689148363340233443)
                ·
                  refine ⟨8908028533722545010350165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938685689148363340233443 8908028533722545010350165)
                  ·
                    refine ⟨104390959379561074340041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8908028533722545010350165 104390959379561074340041)
                    ·
                      rfl

theorem cell22_304951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_304951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304951 prefixEnd_304951 := by exact prefixLift 304951
  have htrace : WordTrace (prefixWord ++ tailWord_304951) baseStart_304951 baseEnd_304951 := by
    simpa [prefixWord, tailWord_304951, baseEnd_304951] using wordTrace_append hprefix tailTrace_304951
  have hstable : (prefixWord ++ tailWord_304951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304951).length < 2 ^ (prefixWord ++ tailWord_304951).sum := by decide
  have hdescent : baseEnd_304951 < baseStart_304951 := by decide
  rcases family_descends (prefixWord ++ tailWord_304951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304959 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 2, 3]
def baseStart_304959 : Nat := 118140960795 + 304959 * 2 ^ 59
def prefixEnd_304959 : Nat := 4983230072969 + 3 ^ 40 * 304959 * 2
def baseEnd_304959 : Nat := 104393697943051720140017

theorem tailTrace_304959 : CollatzResearch.WordTrace tailWord_304959 prefixEnd_304959 104393697943051720140017 := by
  unfold tailWord_304959
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122768502193100695781931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7415179001462067130521287 11122768502193100695781931)
  ·
    refine ⟨16684152753289651043672897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11122768502193100695781931 16684152753289651043672897)
    ·
      refine ⟨12513114564967238282754673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16684152753289651043672897 12513114564967238282754673)
      ·
        refine ⟨9384835923725428712066005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12513114564967238282754673 9384835923725428712066005)
        ·
          refine ⟨219957091962314735439047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9384835923725428712066005 219957091962314735439047)
          ·
            refine ⟨329935637943472103158571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219957091962314735439047 329935637943472103158571)
            ·
              refine ⟨494903456915208154737857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329935637943472103158571 494903456915208154737857)
              ·
                refine ⟨371177592686406116053393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494903456915208154737857 371177592686406116053393)
                ·
                  refine ⟨278383194514804587040045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371177592686406116053393 278383194514804587040045)
                  ·
                    refine ⟨104393697943051720140017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278383194514804587040045 104393697943051720140017)
                    ·
                      rfl

theorem cell22_304959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_304959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304959 prefixEnd_304959 := by exact prefixLift 304959
  have htrace : WordTrace (prefixWord ++ tailWord_304959) baseStart_304959 baseEnd_304959 := by
    simpa [prefixWord, tailWord_304959, baseEnd_304959] using wordTrace_append hprefix tailTrace_304959
  have hstable : (prefixWord ++ tailWord_304959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304959).length < 2 ^ (prefixWord ++ tailWord_304959).sum := by decide
  have hdescent : baseEnd_304959 < baseStart_304959 := by decide
  rcases family_descends (prefixWord ++ tailWord_304959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304970 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_304970 : Nat := 118140960795 + 304970 * 2 ^ 59
def prefixEnd_304970 : Nat := 4983230072969 + 3 ^ 40 * 304970 * 2
def baseEnd_304970 : Nat := 104397463467851358114983

theorem tailTrace_304970 : CollatzResearch.WordTrace tailWord_304970 prefixEnd_304970 104397463467851358114983 := by
  unfold tailWord_304970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2780792426288312393608091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7415446470102166382954909 2780792426288312393608091)
  ·
    refine ⟨4171188639432468590412137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2780792426288312393608091 4171188639432468590412137)
    ·
      refine ⟨3128391479574351442809103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4171188639432468590412137 3128391479574351442809103)
      ·
        refine ⟨4692587219361527164213655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3128391479574351442809103 4692587219361527164213655)
        ·
          refine ⟨7038880829042290746320483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692587219361527164213655 7038880829042290746320483)
          ·
            refine ⟨10558321243563436119480725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038880829042290746320483 10558321243563436119480725)
            ·
              refine ⟨494921308292036068100659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10558321243563436119480725 494921308292036068100659)
              ·
                refine ⟨742381962438054102150989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494921308292036068100659 742381962438054102150989)
                ·
                  refine ⟨278393235914270288306621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742381962438054102150989 278393235914270288306621)
                  ·
                    refine ⟨104397463467851358114983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278393235914270288306621 104397463467851358114983)
                    ·
                      rfl

theorem cell22_304970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_304970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_304970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_304970 prefixEnd_304970 := by exact prefixLift 304970
  have htrace : WordTrace (prefixWord ++ tailWord_304970) baseStart_304970 baseEnd_304970 := by
    simpa [prefixWord, tailWord_304970, baseEnd_304970] using wordTrace_append hprefix tailTrace_304970
  have hstable : (prefixWord ++ tailWord_304970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304970).length < 2 ^ (prefixWord ++ tailWord_304970).sum := by decide
  have hdescent : baseEnd_304970 < baseStart_304970 := by decide
  rcases family_descends (prefixWord ++ tailWord_304970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305004 : List Nat := [2, 2, 1, 1, 4, 4, 1, 3, 1, 3]
def baseStart_305004 : Nat := 118140960795 + 305004 * 2 ^ 59
def prefixEnd_305004 : Nat := 4983230072969 + 3 ^ 40 * 305004 * 2
def baseEnd_305004 : Nat := 104409102362686602764879

theorem tailTrace_305004 : CollatzResearch.WordTrace tailWord_305004 prefixEnd_305004 104409102362686602764879 := by
  unfold tailWord_305004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5562204893515036690585033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7416273191353382254113377 5562204893515036690585033)
  ·
    refine ⟨4171653670136277517938775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5562204893515036690585033 4171653670136277517938775)
    ·
      refine ⟨6257480505204416276908163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4171653670136277517938775 6257480505204416276908163)
      ·
        refine ⟨9386220757806624415362245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6257480505204416276908163 9386220757806624415362245)
        ·
          refine ⟨1759916392088742077880421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9386220757806624415362245 1759916392088742077880421)
          ·
            refine ⟨329984323516639139602579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1759916392088742077880421 329984323516639139602579)
            ·
              refine ⟨494976485274958709403869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329984323516639139602579 494976485274958709403869)
              ·
                refine ⟨185616181978109516026451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494976485274958709403869 185616181978109516026451)
                ·
                  refine ⟨278424272967164274039677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185616181978109516026451 278424272967164274039677)
                  ·
                    refine ⟨104409102362686602764879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278424272967164274039677 104409102362686602764879)
                    ·
                      rfl

theorem cell22_305004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_305004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305004 prefixEnd_305004 := by exact prefixLift 305004
  have htrace : WordTrace (prefixWord ++ tailWord_305004) baseStart_305004 baseEnd_305004 := by
    simpa [prefixWord, tailWord_305004, baseEnd_305004] using wordTrace_append hprefix tailTrace_305004
  have hstable : (prefixWord ++ tailWord_305004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305004).length < 2 ^ (prefixWord ++ tailWord_305004).sum := by decide
  have hdescent : baseEnd_305004 < baseStart_305004 := by decide
  rcases family_descends (prefixWord ++ tailWord_305004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305034 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_305034 : Nat := 118140960795 + 305034 * 2 ^ 59
def prefixEnd_305034 : Nat := 4983230072969 + 3 ^ 40 * 305034 * 2
def baseEnd_305034 : Nat := 34806457325258841504929

theorem tailTrace_305034 : CollatzResearch.WordTrace tailWord_305034 prefixEnd_305034 34806457325258841504929 := by
  unfold tailWord_305034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2781375994230347126190539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7417002651280925669841437 2781375994230347126190539)
  ·
    refine ⟨4172063991345520689285809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2781375994230347126190539 4172063991345520689285809)
    ·
      refine ⟨3129047993509140516964357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4172063991345520689285809 3129047993509140516964357)
      ·
        refine ⟨586696498782963846930817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3129047993509140516964357 586696498782963846930817)
        ·
          refine ⟨440022374087222885198113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586696498782963846930817 440022374087222885198113)
          ·
            refine ⟨330016780565417163898585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440022374087222885198113 330016780565417163898585)
            ·
              refine ⟨247512585424062872923939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330016780565417163898585 247512585424062872923939)
              ·
                refine ⟨371268878136094309385909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247512585424062872923939 371268878136094309385909)
                ·
                  refine ⟨34806457325258841504929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371268878136094309385909 34806457325258841504929)
                  ·
                    rfl

theorem cell22_305034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_305034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305034 prefixEnd_305034 := by exact prefixLift 305034
  have htrace : WordTrace (prefixWord ++ tailWord_305034) baseStart_305034 baseEnd_305034 := by
    simpa [prefixWord, tailWord_305034, baseEnd_305034] using wordTrace_append hprefix tailTrace_305034
  have hstable : (prefixWord ++ tailWord_305034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305034).length < 2 ^ (prefixWord ++ tailWord_305034).sum := by decide
  have hdescent : baseEnd_305034 < baseStart_305034 := by decide
  rcases family_descends (prefixWord ++ tailWord_305034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305047 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 1, 4]
def baseStart_305047 : Nat := 118140960795 + 305047 * 2 ^ 59
def prefixEnd_305047 : Nat := 4983230072969 + 3 ^ 40 * 305047 * 2
def baseEnd_305047 : Nat := 104423822141448823939747

theorem tailTrace_305047 : CollatzResearch.WordTrace tailWord_305047 prefixEnd_305047 104423822141448823939747 := by
  unfold tailWord_305047
  simp only [CollatzResearch.WordTrace]
  refine ⟨11125978125874291724985395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7417318750582861149990263 11125978125874291724985395)
  ·
    refine ⟨16688967188811437587478093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11125978125874291724985395 16688967188811437587478093)
    ·
      refine ⟨6258362695804289095304285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16688967188811437587478093 6258362695804289095304285)
      ·
        refine ⟨2346886010926608410739107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6258362695804289095304285 2346886010926608410739107)
        ·
          refine ⟨3520329016389912616108661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346886010926608410739107 3520329016389912616108661)
          ·
            refine ⟨330030845286554307760187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3520329016389912616108661 330030845286554307760187)
            ·
              refine ⟨495046267929831461640281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330030845286554307760187 495046267929831461640281)
              ·
                refine ⟨371284700947373596230211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495046267929831461640281 371284700947373596230211)
                ·
                  refine ⟨556927051421060394345317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 371284700947373596230211 556927051421060394345317)
                  ·
                    refine ⟨104423822141448823939747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 556927051421060394345317 104423822141448823939747)
                    ·
                      rfl

theorem cell22_305047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_305047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305047 prefixEnd_305047 := by exact prefixLift 305047
  have htrace : WordTrace (prefixWord ++ tailWord_305047) baseStart_305047 baseEnd_305047 := by
    simpa [prefixWord, tailWord_305047, baseEnd_305047] using wordTrace_append hprefix tailTrace_305047
  have hstable : (prefixWord ++ tailWord_305047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305047).length < 2 ^ (prefixWord ++ tailWord_305047).sum := by decide
  have hdescent : baseEnd_305047 < baseStart_305047 := by decide
  rcases family_descends (prefixWord ++ tailWord_305047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305060 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_305060 : Nat := 118140960795 + 305060 * 2 ^ 59
def prefixEnd_305060 : Nat := 4983230072969 + 3 ^ 40 * 305060 * 2
def baseEnd_305060 : Nat := 104428272307121123364707

theorem tailTrace_305060 : CollatzResearch.WordTrace tailWord_305060 prefixEnd_305060 104428272307121123364707 := by
  unfold tailWord_305060
  simp only [CollatzResearch.WordTrace]
  refine ⟨5563226137413597472604317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7417634849884796630139089 5563226137413597472604317)
  ·
    refine ⟨2086209801530099052226619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5563226137413597472604317 2086209801530099052226619)
    ·
      refine ⟨3129314702295148578339929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2086209801530099052226619 3129314702295148578339929)
      ·
        refine ⟨2346986026721361433754947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3129314702295148578339929 2346986026721361433754947)
        ·
          refine ⟨3520479040082042150632421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346986026721361433754947 3520479040082042150632421)
          ·
            refine ⟨660089820015382903243579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3520479040082042150632421 660089820015382903243579)
            ·
              refine ⟨990134730023074354865369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660089820015382903243579 990134730023074354865369)
              ·
                refine ⟨742601047517305766149027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990134730023074354865369 742601047517305766149027)
                ·
                  refine ⟨1113901571275958649223541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 742601047517305766149027 1113901571275958649223541)
                  ·
                    refine ⟨104428272307121123364707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1113901571275958649223541 104428272307121123364707)
                    ·
                      rfl

theorem cell22_305060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_305060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305060 prefixEnd_305060 := by exact prefixLift 305060
  have htrace : WordTrace (prefixWord ++ tailWord_305060) baseStart_305060 baseEnd_305060 := by
    simpa [prefixWord, tailWord_305060, baseEnd_305060] using wordTrace_append hprefix tailTrace_305060
  have hstable : (prefixWord ++ tailWord_305060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305060).length < 2 ^ (prefixWord ++ tailWord_305060).sum := by decide
  have hdescent : baseEnd_305060 < baseStart_305060 := by decide
  rcases family_descends (prefixWord ++ tailWord_305060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305073 : List Nat := [1, 2, 2, 4, 2, 11]
def baseStart_305073 : Nat := 118140960795 + 305073 * 2 ^ 59
def prefixEnd_305073 : Nat := 4983230072969 + 3 ^ 40 * 305073 * 2
def baseEnd_305073 : Nat := 1289292870034486701107

theorem tailTrace_305073 : CollatzResearch.WordTrace tailWord_305073 prefixEnd_305073 1289292870034486701107 := by
  unfold tailWord_305073
  simp only [CollatzResearch.WordTrace]
  refine ⟨11126926423780098165431873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7417950949186732110287915 11126926423780098165431873)
  ·
    refine ⟨8345194817835073624073905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11126926423780098165431873 8345194817835073624073905)
    ·
      refine ⟨6258896113376305218055429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8345194817835073624073905 6258896113376305218055429)
      ·
        refine ⟨1173543021258057228385393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6258896113376305218055429 1173543021258057228385393)
        ·
          refine ⟨880157265943542921289045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173543021258057228385393 880157265943542921289045)
          ·
            refine ⟨1289292870034486701107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 880157265943542921289045 1289292870034486701107)
            ·
              rfl

theorem cell22_305073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 11].length) (baseStart_305073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305073 prefixEnd_305073 := by exact prefixLift 305073
  have htrace : WordTrace (prefixWord ++ tailWord_305073) baseStart_305073 baseEnd_305073 := by
    simpa [prefixWord, tailWord_305073, baseEnd_305073] using wordTrace_append hprefix tailTrace_305073
  have hstable : (prefixWord ++ tailWord_305073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305073).length < 2 ^ (prefixWord ++ tailWord_305073).sum := by decide
  have hdescent : baseEnd_305073 < baseStart_305073 := by decide
  rcases family_descends (prefixWord ++ tailWord_305073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305077 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_305077 : Nat := 118140960795 + 305077 * 2 ^ 59
def prefixEnd_305077 : Nat := 4983230072969 + 3 ^ 40 * 305077 * 2
def baseEnd_305077 : Nat := 104434091754538745689655

theorem tailTrace_305077 : CollatzResearch.WordTrace tailWord_305077 prefixEnd_305077 104434091754538745689655 := by
  unfold tailWord_305077
  simp only [CollatzResearch.WordTrace]
  refine ⟨11127072315765606848577485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7418048210510404565718323 11127072315765606848577485)
  ·
    refine ⟨4172652118412102568216557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11127072315765606848577485 4172652118412102568216557)
    ·
      refine ⟨1564744544404538463081209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4172652118412102568216557 1564744544404538463081209)
      ·
        refine ⟨1173558408303403847310907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1564744544404538463081209 1173558408303403847310907)
        ·
          refine ⟨1760337612455105770966361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173558408303403847310907 1760337612455105770966361)
          ·
            refine ⟨1320253209341329328224771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1760337612455105770966361 1320253209341329328224771)
            ·
              refine ⟨1980379814011993992337157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320253209341329328224771 1980379814011993992337157)
              ·
                refine ⟨371321215127248873563217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1980379814011993992337157 371321215127248873563217)
                ·
                  refine ⟨278490911345436655172413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371321215127248873563217 278490911345436655172413)
                  ·
                    refine ⟨104434091754538745689655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278490911345436655172413 104434091754538745689655)
                    ·
                      rfl

theorem cell22_305077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_305077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305077 prefixEnd_305077 := by exact prefixLift 305077
  have htrace : WordTrace (prefixWord ++ tailWord_305077) baseStart_305077 baseEnd_305077 := by
    simpa [prefixWord, tailWord_305077, baseEnd_305077] using wordTrace_append hprefix tailTrace_305077
  have hstable : (prefixWord ++ tailWord_305077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305077).length < 2 ^ (prefixWord ++ tailWord_305077).sum := by decide
  have hdescent : baseEnd_305077 < baseStart_305077 := by decide
  rcases family_descends (prefixWord ++ tailWord_305077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305103 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 2, 6]
def baseStart_305103 : Nat := 118140960795 + 305103 * 2 ^ 59
def prefixEnd_305103 : Nat := 4983230072969 + 3 ^ 40 * 305103 * 2
def baseEnd_305103 : Nat := 104442992085883344539575

theorem tailTrace_305103 : CollatzResearch.WordTrace tailWord_305103 prefixEnd_305103 104442992085883344539575 := by
  unfold tailWord_305103
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128020613671413289023963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7418680409114275526015975 11128020613671413289023963)
  ·
    refine ⟨16692030920507119933535945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11128020613671413289023963 16692030920507119933535945)
    ·
      refine ⟨12519023190380339950151959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16692030920507119933535945 12519023190380339950151959)
      ·
        refine ⟨18778534785570509925227939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12519023190380339950151959 18778534785570509925227939)
        ·
          refine ⟨28167802178355764887841909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18778534785570509925227939 28167802178355764887841909)
          ·
            refine ⟨2640731454220852958235179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28167802178355764887841909 2640731454220852958235179)
            ·
              refine ⟨3961097181331279437352769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640731454220852958235179 3961097181331279437352769)
              ·
                refine ⟨2970822885998459578014577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3961097181331279437352769 2970822885998459578014577)
                ·
                  refine ⟨2228117164498844683510933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2970822885998459578014577 2228117164498844683510933)
                  ·
                    refine ⟨104442992085883344539575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2228117164498844683510933 104442992085883344539575)
                    ·
                      rfl

theorem cell22_305103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_305103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305103 prefixEnd_305103 := by exact prefixLift 305103
  have htrace : WordTrace (prefixWord ++ tailWord_305103) baseStart_305103 baseEnd_305103 := by
    simpa [prefixWord, tailWord_305103, baseEnd_305103] using wordTrace_append hprefix tailTrace_305103
  have hstable : (prefixWord ++ tailWord_305103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305103).length < 2 ^ (prefixWord ++ tailWord_305103).sum := by decide
  have hdescent : baseEnd_305103 < baseStart_305103 := by decide
  rcases family_descends (prefixWord ++ tailWord_305103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305173 : List Nat := [1, 3, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_305173 : Nat := 118140960795 + 305173 * 2 ^ 59
def prefixEnd_305173 : Nat := 4983230072969 + 3 ^ 40 * 305173 * 2
def baseEnd_305173 : Nat := 104466954516426495289361

theorem tailTrace_305173 : CollatzResearch.WordTrace tailWord_305173 prefixEnd_305173 104466954516426495289361 := by
  unfold tailWord_305173
  simp only [CollatzResearch.WordTrace]
  refine ⟨11130573723417815244072173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7420382482278543496048115 11130573723417815244072173)
  ·
    refine ⟨4173965146281680716527065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11130573723417815244072173 4173965146281680716527065)
    ·
      refine ⟨3130473859711260537395299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4173965146281680716527065 3130473859711260537395299)
      ·
        refine ⟨4695710789566890806092949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130473859711260537395299 4695710789566890806092949)
        ·
          refine ⟨220111443260948006535607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4695710789566890806092949 220111443260948006535607)
          ·
            refine ⟨330167164891422009803411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220111443260948006535607 330167164891422009803411)
            ·
              refine ⟨495250747337133014705117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330167164891422009803411 495250747337133014705117)
              ·
                refine ⟨185719030251424880514419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495250747337133014705117 185719030251424880514419)
                ·
                  refine ⟨278578545377137320771629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185719030251424880514419 278578545377137320771629)
                  ·
                    refine ⟨104466954516426495289361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278578545377137320771629 104466954516426495289361)
                    ·
                      rfl

theorem cell22_305173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_305173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305173 prefixEnd_305173 := by exact prefixLift 305173
  have htrace : WordTrace (prefixWord ++ tailWord_305173) baseStart_305173 baseEnd_305173 := by
    simpa [prefixWord, tailWord_305173, baseEnd_305173] using wordTrace_append hprefix tailTrace_305173
  have hstable : (prefixWord ++ tailWord_305173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305173).length < 2 ^ (prefixWord ++ tailWord_305173).sum := by decide
  have hdescent : baseEnd_305173 < baseStart_305173 := by decide
  rcases family_descends (prefixWord ++ tailWord_305173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305210 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_305210 : Nat := 118140960795 + 305210 * 2 ^ 59
def prefixEnd_305210 : Nat := 4983230072969 + 3 ^ 40 * 305210 * 2
def baseEnd_305210 : Nat := 104479620372570732114247

theorem tailTrace_305210 : CollatzResearch.WordTrace tailWord_305210 prefixEnd_305210 104479620372570732114247 := by
  unfold tailWord_305210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782980806070942640792271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7421282149522513708779389 2782980806070942640792271)
  ·
    refine ⟨4174471209106413961188407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2782980806070942640792271 4174471209106413961188407)
    ·
      refine ⟨6261706813659620941782611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4174471209106413961188407 6261706813659620941782611)
      ·
        refine ⟨9392560220489431412673917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261706813659620941782611 9392560220489431412673917)
        ·
          refine ⟨3522210082683536779752719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9392560220489431412673917 3522210082683536779752719)
          ·
            refine ⟨5283315124025305169629079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522210082683536779752719 5283315124025305169629079)
            ·
              refine ⟨7924972686037957754443619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5283315124025305169629079 7924972686037957754443619)
              ·
                refine ⟨11887459029056936631665429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7924972686037957754443619 11887459029056936631665429)
                ·
                  refine ⟨557224641987043904609317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11887459029056936631665429 557224641987043904609317)
                  ·
                    refine ⟨104479620372570732114247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 557224641987043904609317 104479620372570732114247)
                    ·
                      rfl

theorem cell22_305210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_305210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305210 prefixEnd_305210 := by exact prefixLift 305210
  have htrace : WordTrace (prefixWord ++ tailWord_305210) baseStart_305210 baseEnd_305210 := by
    simpa [prefixWord, tailWord_305210, baseEnd_305210] using wordTrace_append hprefix tailTrace_305210
  have hstable : (prefixWord ++ tailWord_305210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305210).length < 2 ^ (prefixWord ++ tailWord_305210).sum := by decide
  have hdescent : baseEnd_305210 < baseStart_305210 := by decide
  rcases family_descends (prefixWord ++ tailWord_305210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305255 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 8]
def baseStart_305255 : Nat := 118140960795 + 305255 * 2 ^ 59
def prefixEnd_305255 : Nat := 4983230072969 + 3 ^ 40 * 305255 * 2
def baseEnd_305255 : Nat := 104495024792205614739109

theorem tailTrace_305255 : CollatzResearch.WordTrace tailWord_305255 prefixEnd_305255 104495024792205614739109 := by
  unfold tailWord_305255
  simp only [CollatzResearch.WordTrace]
  refine ⟨11133564509120743248557219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7422376339413828832371479 11133564509120743248557219)
  ·
    refine ⟨16700346763681114872835829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11133564509120743248557219 16700346763681114872835829)
    ·
      refine ⟨1565657509095104519328359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16700346763681114872835829 1565657509095104519328359)
      ·
        refine ⟨2348486263642656778992539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565657509095104519328359 2348486263642656778992539)
        ·
          refine ⟨3522729395463985168488809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348486263642656778992539 3522729395463985168488809)
          ·
            refine ⟨2642047046597988876366607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3522729395463985168488809 2642047046597988876366607)
            ·
              refine ⟨3963070569896983314549911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642047046597988876366607 3963070569896983314549911)
              ·
                refine ⟨5944605854845474971824867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963070569896983314549911 5944605854845474971824867)
                ·
                  refine ⟨8916908782268212457737301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5944605854845474971824867 8916908782268212457737301)
                  ·
                    refine ⟨104495024792205614739109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8916908782268212457737301 104495024792205614739109)
                    ·
                      rfl

theorem cell22_305255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_305255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305255 prefixEnd_305255 := by exact prefixLift 305255
  have htrace : WordTrace (prefixWord ++ tailWord_305255) baseStart_305255 baseEnd_305255 := by
    simpa [prefixWord, tailWord_305255, baseEnd_305255] using wordTrace_append hprefix tailTrace_305255
  have hstable : (prefixWord ++ tailWord_305255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305255).length < 2 ^ (prefixWord ++ tailWord_305255).sum := by decide
  have hdescent : baseEnd_305255 < baseStart_305255 := by decide
  rcases family_descends (prefixWord ++ tailWord_305255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305257 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 3, 3]
def baseStart_305257 : Nat := 118140960795 + 305257 * 2 ^ 59
def prefixEnd_305257 : Nat := 4983230072969 + 3 ^ 40 * 305257 * 2
def baseEnd_305257 : Nat := 104495709433078276189103

theorem tailTrace_305257 : CollatzResearch.WordTrace tailWord_305257 prefixEnd_305257 104495709433078276189103 := by
  unfold tailWord_305257
  simp only [CollatzResearch.WordTrace]
  refine ⟨11133637455113497590130025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7422424970075665060086683 11133637455113497590130025)
  ·
    refine ⟨8350228091335123192597519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11133637455113497590130025 8350228091335123192597519)
    ·
      refine ⟨12525342137002684788896279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8350228091335123192597519 12525342137002684788896279)
      ·
        refine ⟨18788013205504027183344419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12525342137002684788896279 18788013205504027183344419)
        ·
          refine ⟨28182019808256040775016629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18788013205504027183344419 28182019808256040775016629)
          ·
            refine ⟨2642064357024003822657809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28182019808256040775016629 2642064357024003822657809)
            ·
              refine ⟨1981548267768002866993357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642064357024003822657809 1981548267768002866993357)
              ·
                refine ⟨743080600413001075122509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1981548267768002866993357 743080600413001075122509)
                ·
                  refine ⟨278655225154875403170941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743080600413001075122509 278655225154875403170941)
                  ·
                    refine ⟨104495709433078276189103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278655225154875403170941 104495709433078276189103)
                    ·
                      rfl

theorem cell22_305257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 3].length) (baseStart_305257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305257 prefixEnd_305257 := by exact prefixLift 305257
  have htrace : WordTrace (prefixWord ++ tailWord_305257) baseStart_305257 baseEnd_305257 := by
    simpa [prefixWord, tailWord_305257, baseEnd_305257] using wordTrace_append hprefix tailTrace_305257
  have hstable : (prefixWord ++ tailWord_305257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305257).length < 2 ^ (prefixWord ++ tailWord_305257).sum := by decide
  have hdescent : baseEnd_305257 < baseStart_305257 := by decide
  rcases family_descends (prefixWord ++ tailWord_305257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305349 : List Nat := [1, 3, 1, 1, 1, 1, 7, 3, 4]
def baseStart_305349 : Nat := 118140960795 + 305349 * 2 ^ 59
def prefixEnd_305349 : Nat := 4983230072969 + 3 ^ 40 * 305349 * 2
def baseEnd_305349 : Nat := 34842400971073567629607

theorem tailTrace_305349 : CollatzResearch.WordTrace tailWord_305349 prefixEnd_305349 34842400971073567629607 := by
  unfold tailWord_305349
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136992970780197302479101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7424661980520131534986067 11136992970780197302479101)
  ·
    refine ⟨4176372364042573988429663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11136992970780197302479101 4176372364042573988429663)
    ·
      refine ⟨6264558546063860982644495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176372364042573988429663 6264558546063860982644495)
      ·
        refine ⟨9396837819095791473966743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264558546063860982644495 9396837819095791473966743)
        ·
          refine ⟨14095256728643687210950115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396837819095791473966743 14095256728643687210950115)
          ·
            refine ⟨21142885092965530816425173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14095256728643687210950115 21142885092965530816425173)
            ·
              refine ⟨495536369366379628509965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21142885092965530816425173 495536369366379628509965)
              ·
                refine ⟨185826138512392360691237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495536369366379628509965 185826138512392360691237)
                ·
                  refine ⟨34842400971073567629607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185826138512392360691237 34842400971073567629607)
                  ·
                    rfl

theorem cell22_305349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_305349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305349 prefixEnd_305349 := by exact prefixLift 305349
  have htrace : WordTrace (prefixWord ++ tailWord_305349) baseStart_305349 baseEnd_305349 := by
    simpa [prefixWord, tailWord_305349, baseEnd_305349] using wordTrace_append hprefix tailTrace_305349
  have hstable : (prefixWord ++ tailWord_305349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305349).length < 2 ^ (prefixWord ++ tailWord_305349).sum := by decide
  have hdescent : baseEnd_305349 < baseStart_305349 := by decide
  rcases family_descends (prefixWord ++ tailWord_305349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305366 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_305366 : Nat := 118140960795 + 305366 * 2 ^ 59
def prefixEnd_305366 : Nat := 4983230072969 + 3 ^ 40 * 305366 * 2
def baseEnd_305366 : Nat := 34844340786879441737923

theorem tailTrace_305366 : CollatzResearch.WordTrace tailWord_305366 prefixEnd_305366 34844340786879441737923 := by
  unfold tailWord_305366
  simp only [CollatzResearch.WordTrace]
  refine ⟨696100813232413075365497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7425075341145739470565301 696100813232413075365497)
  ·
    refine ⟨522075609924309806524123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 696100813232413075365497 522075609924309806524123)
    ·
      refine ⟨783113414886464709786185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522075609924309806524123 783113414886464709786185)
      ·
        refine ⟨587335061164848532339639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 783113414886464709786185 587335061164848532339639)
        ·
          refine ⟨881002591747272798509459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587335061164848532339639 881002591747272798509459)
          ·
            refine ⟨1321503887620909197764189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881002591747272798509459 1321503887620909197764189)
            ·
              refine ⟨495563957857840949161571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1321503887620909197764189 495563957857840949161571)
              ·
                refine ⟨743345936786761423742357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495563957857840949161571 743345936786761423742357)
                ·
                  refine ⟨34844340786879441737923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 743345936786761423742357 34844340786879441737923)
                  ·
                    rfl

theorem cell22_305366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_305366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305366 prefixEnd_305366 := by exact prefixLift 305366
  have htrace : WordTrace (prefixWord ++ tailWord_305366) baseStart_305366 baseEnd_305366 := by
    simpa [prefixWord, tailWord_305366, baseEnd_305366] using wordTrace_append hprefix tailTrace_305366
  have hstable : (prefixWord ++ tailWord_305366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305366).length < 2 ^ (prefixWord ++ tailWord_305366).sum := by decide
  have hdescent : baseEnd_305366 < baseStart_305366 := by decide
  rcases family_descends (prefixWord ++ tailWord_305366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305377 : List Nat := [1, 2, 3, 1, 3, 1, 4, 7]
def baseStart_305377 : Nat := 118140960795 + 305377 * 2 ^ 59
def prefixEnd_305377 : Nat := 4983230072969 + 3 ^ 40 * 305377 * 2
def baseEnd_305377 : Nat := 11615198653937551465415

theorem tailTrace_305377 : CollatzResearch.WordTrace tailWord_305377 prefixEnd_305377 11615198653937551465415 := by
  unfold tailWord_305377
  simp only [CollatzResearch.WordTrace]
  refine ⟨11138014214678758084498385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7425342809785838722998923 11138014214678758084498385)
  ·
    refine ⟨8353510661009068563373789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11138014214678758084498385 8353510661009068563373789)
    ·
      refine ⟨3132566497878400711265171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8353510661009068563373789 3132566497878400711265171)
      ·
        refine ⟨4698849746817601066897757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3132566497878400711265171 4698849746817601066897757)
        ·
          refine ⟨1762068655056600400086659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4698849746817601066897757 1762068655056600400086659)
          ·
            refine ⟨2643102982584900600129989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762068655056600400086659 2643102982584900600129989)
            ·
              refine ⟨495581809234668862524373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2643102982584900600129989 495581809234668862524373)
              ·
                refine ⟨11615198653937551465415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 495581809234668862524373 11615198653937551465415)
                ·
                  rfl

theorem cell22_305377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 7].length) (baseStart_305377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305377 prefixEnd_305377 := by exact prefixLift 305377
  have htrace : WordTrace (prefixWord ++ tailWord_305377) baseStart_305377 baseEnd_305377 := by
    simpa [prefixWord, tailWord_305377, baseEnd_305377] using wordTrace_append hprefix tailTrace_305377
  have hstable : (prefixWord ++ tailWord_305377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305377).length < 2 ^ (prefixWord ++ tailWord_305377).sum := by decide
  have hdescent : baseEnd_305377 < baseStart_305377 := by decide
  rcases family_descends (prefixWord ++ tailWord_305377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305381 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_305381 : Nat := 118140960795 + 305381 * 2 ^ 59
def prefixEnd_305381 : Nat := 4983230072969 + 3 ^ 40 * 305381 * 2
def baseEnd_305381 : Nat := 104538157167183286088723

theorem tailTrace_305381 : CollatzResearch.WordTrace tailWord_305381 prefixEnd_305381 104538157167183286088723 := by
  unfold tailWord_305381
  simp only [CollatzResearch.WordTrace]
  refine ⟨11138160106664266767643997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7425440071109511178429331 11138160106664266767643997)
  ·
    refine ⟨4176810039999100037866499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11138160106664266767643997 4176810039999100037866499)
    ·
      refine ⟨6265215059998650056799749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4176810039999100037866499 6265215059998650056799749)
      ·
        refine ⟨1174727823749746885649953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6265215059998650056799749 1174727823749746885649953)
        ·
          refine ⟨881045867812310164237465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1174727823749746885649953 881045867812310164237465)
          ·
            refine ⟨660784400859232623178099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881045867812310164237465 660784400859232623178099)
            ·
              refine ⟨991176601288848934767149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660784400859232623178099 991176601288848934767149)
              ·
                refine ⟨371691225483318350537681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 991176601288848934767149 371691225483318350537681)
                ·
                  refine ⟨278768419112488762903261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371691225483318350537681 278768419112488762903261)
                  ·
                    refine ⟨104538157167183286088723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278768419112488762903261 104538157167183286088723)
                    ·
                      rfl

theorem cell22_305381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_305381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305381 prefixEnd_305381 := by exact prefixLift 305381
  have htrace : WordTrace (prefixWord ++ tailWord_305381) baseStart_305381 baseEnd_305381 := by
    simpa [prefixWord, tailWord_305381, baseEnd_305381] using wordTrace_append hprefix tailTrace_305381
  have hstable : (prefixWord ++ tailWord_305381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305381).length < 2 ^ (prefixWord ++ tailWord_305381).sum := by decide
  have hdescent : baseEnd_305381 < baseStart_305381 := by decide
  rcases family_descends (prefixWord ++ tailWord_305381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305439 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 5]
def baseStart_305439 : Nat := 118140960795 + 305439 * 2 ^ 59
def prefixEnd_305439 : Nat := 4983230072969 + 3 ^ 40 * 305439 * 2
def baseEnd_305439 : Nat := 34852670584163489379515

theorem tailTrace_305439 : CollatzResearch.WordTrace tailWord_305439 prefixEnd_305439 34852670584163489379515 := by
  unfold tailWord_305439
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140275540454142673255371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7426850360302761782170247 11140275540454142673255371)
  ·
    refine ⟨16710413310681214009883057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11140275540454142673255371 16710413310681214009883057)
    ·
      refine ⟨12532809983010910507412293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16710413310681214009883057 12532809983010910507412293)
      ·
        refine ⟨2349901871814545720139805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12532809983010910507412293 2349901871814545720139805)
        ·
          refine ⟨881213201930454645052427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2349901871814545720139805 881213201930454645052427)
          ·
            refine ⟨1321819802895681967578641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881213201930454645052427 1321819802895681967578641)
            ·
              refine ⟨991364852171761475683981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321819802895681967578641 991364852171761475683981)
              ·
                refine ⟨371761819564410553381493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 991364852171761475683981 371761819564410553381493)
                ·
                  refine ⟨34852670584163489379515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371761819564410553381493 34852670584163489379515)
                  ·
                    rfl

theorem cell22_305439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 5].length) (baseStart_305439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305439 prefixEnd_305439 := by exact prefixLift 305439
  have htrace : WordTrace (prefixWord ++ tailWord_305439) baseStart_305439 baseEnd_305439 := by
    simpa [prefixWord, tailWord_305439, baseEnd_305439] using wordTrace_append hprefix tailTrace_305439
  have hstable : (prefixWord ++ tailWord_305439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305439).length < 2 ^ (prefixWord ++ tailWord_305439).sum := by decide
  have hdescent : baseEnd_305439 < baseStart_305439 := by decide
  rcases family_descends (prefixWord ++ tailWord_305439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305447 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 2, 4]
def baseStart_305447 : Nat := 118140960795 + 305447 * 2 ^ 59
def prefixEnd_305447 : Nat := 4983230072969 + 3 ^ 40 * 305447 * 2
def baseEnd_305447 : Nat := 104560750315981113938521

theorem tailTrace_305447 : CollatzResearch.WordTrace tailWord_305447 prefixEnd_305447 104560750315981113938521 := by
  unfold tailWord_305447
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140567324425160039546595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7427044882950106693031063 11140567324425160039546595)
  ·
    refine ⟨16710850986637740059319893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11140567324425160039546595 16710850986637740059319893)
    ·
      refine ⟨195830284999661016320155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 16710850986637740059319893 195830284999661016320155)
      ·
        refine ⟨293745427499491524480233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195830284999661016320155 293745427499491524480233)
        ·
          refine ⟨220309070624618643360175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293745427499491524480233 220309070624618643360175)
          ·
            refine ⟨330463605936927965040263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220309070624618643360175 330463605936927965040263)
            ·
              refine ⟨495695408905391947560395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330463605936927965040263 495695408905391947560395)
              ·
                refine ⟨743543113358087921340593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495695408905391947560395 743543113358087921340593)
                ·
                  refine ⟨557657335018565941005445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 743543113358087921340593 557657335018565941005445)
                  ·
                    refine ⟨104560750315981113938521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 557657335018565941005445 104560750315981113938521)
                    ·
                      rfl

theorem cell22_305447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_305447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305447 prefixEnd_305447 := by exact prefixLift 305447
  have htrace : WordTrace (prefixWord ++ tailWord_305447) baseStart_305447 baseEnd_305447 := by
    simpa [prefixWord, tailWord_305447, baseEnd_305447] using wordTrace_append hprefix tailTrace_305447
  have hstable : (prefixWord ++ tailWord_305447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305447).length < 2 ^ (prefixWord ++ tailWord_305447).sum := by decide
  have hdescent : baseEnd_305447 < baseStart_305447 := by decide
  rcases family_descends (prefixWord ++ tailWord_305447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305460 : List Nat := [2, 5, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_305460 : Nat := 118140960795 + 305460 * 2 ^ 59
def prefixEnd_305460 : Nat := 4983230072969 + 3 ^ 40 * 305460 * 2
def baseEnd_305460 : Nat := 104565200481653413363481

theorem tailTrace_305460 : CollatzResearch.WordTrace tailWord_305460 prefixEnd_305460 104565200481653413363481 := by
  unfold tailWord_305460
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570520736689031629884917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7427360982252042173179889 5570520736689031629884917)
  ·
    refine ⟨522236319064596715301711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5570520736689031629884917 522236319064596715301711)
    ·
      refine ⟨783354478596895072952567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522236319064596715301711 783354478596895072952567)
      ·
        refine ⟨1175031717895342609428851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783354478596895072952567 1175031717895342609428851)
        ·
          refine ⟨1762547576843013914143277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175031717895342609428851 1762547576843013914143277)
          ·
            refine ⟨660955341316130217803729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1762547576843013914143277 660955341316130217803729)
            ·
              refine ⟨495716505987097663352797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660955341316130217803729 495716505987097663352797)
              ·
                refine ⟨185893689745161623757299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495716505987097663352797 185893689745161623757299)
                ·
                  refine ⟨278840534617742435635949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185893689745161623757299 278840534617742435635949)
                  ·
                    refine ⟨104565200481653413363481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278840534617742435635949 104565200481653413363481)
                    ·
                      rfl

theorem cell22_305460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_305460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305460 prefixEnd_305460 := by exact prefixLift 305460
  have htrace : WordTrace (prefixWord ++ tailWord_305460) baseStart_305460 baseEnd_305460 := by
    simpa [prefixWord, tailWord_305460, baseEnd_305460] using wordTrace_append hprefix tailTrace_305460
  have hstable : (prefixWord ++ tailWord_305460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305460).length < 2 ^ (prefixWord ++ tailWord_305460).sum := by decide
  have hdescent : baseEnd_305460 < baseStart_305460 := by decide
  rcases family_descends (prefixWord ++ tailWord_305460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305473 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 5]
def baseStart_305473 : Nat := 118140960795 + 305473 * 2 ^ 59
def prefixEnd_305473 : Nat := 4983230072969 + 3 ^ 40 * 305473 * 2
def baseEnd_305473 : Nat := 34856550215775237596147

theorem tailTrace_305473 : CollatzResearch.WordTrace tailWord_305473 prefixEnd_305473 34856550215775237596147 := by
  unfold tailWord_305473
  simp only [CollatzResearch.WordTrace]
  refine ⟨11141515622330966479993073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7427677081553977653328715 11141515622330966479993073)
  ·
    refine ⟨8356136716748224859994805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11141515622330966479993073 8356136716748224859994805)
    ·
      refine ⟨783387817195146080624513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8356136716748224859994805 783387817195146080624513)
      ·
        refine ⟨587540862896359560468385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 783387817195146080624513 587540862896359560468385)
        ·
          refine ⟨440655647172269670351289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587540862896359560468385 440655647172269670351289)
          ·
            refine ⟨330491735379202252763467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440655647172269670351289 330491735379202252763467)
            ·
              refine ⟨495737603068803379145201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330491735379202252763467 495737603068803379145201)
              ·
                refine ⟨371803202301602534358901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495737603068803379145201 371803202301602534358901)
                ·
                  refine ⟨34856550215775237596147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371803202301602534358901 34856550215775237596147)
                  ·
                    rfl

theorem cell22_305473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 5].length) (baseStart_305473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305473 prefixEnd_305473 := by exact prefixLift 305473
  have htrace : WordTrace (prefixWord ++ tailWord_305473) baseStart_305473 baseEnd_305473 := by
    simpa [prefixWord, tailWord_305473, baseEnd_305473] using wordTrace_append hprefix tailTrace_305473
  have hstable : (prefixWord ++ tailWord_305473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305473).length < 2 ^ (prefixWord ++ tailWord_305473).sum := by decide
  have hdescent : baseEnd_305473 < baseStart_305473 := by decide
  rcases family_descends (prefixWord ++ tailWord_305473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305482 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_305482 : Nat := 118140960795 + 305482 * 2 ^ 59
def prefixEnd_305482 : Nat := 4983230072969 + 3 ^ 40 * 305482 * 2
def baseEnd_305482 : Nat := 104572731531252689313413

theorem tailTrace_305482 : CollatzResearch.WordTrace tailWord_305482 prefixEnd_305482 104572731531252689313413 := by
  unfold tailWord_305482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785460969824590254267675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7427895919532240678047133 2785460969824590254267675)
  ·
    refine ⟨4178191454736885381401513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2785460969824590254267675 4178191454736885381401513)
    ·
      refine ⟨3133643591052664036051135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4178191454736885381401513 3133643591052664036051135)
      ·
        refine ⟨4700465386578996054076703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133643591052664036051135 4700465386578996054076703)
        ·
          refine ⟨7050698079868494081115055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4700465386578996054076703 7050698079868494081115055)
          ·
            refine ⟨10576047119802741121672583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7050698079868494081115055 10576047119802741121672583)
            ·
              refine ⟨15864070679704111682508875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10576047119802741121672583 15864070679704111682508875)
              ·
                refine ⟨23796106019556167523763313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15864070679704111682508875 23796106019556167523763313)
                ·
                  refine ⟨17847079514667125642822485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23796106019556167523763313 17847079514667125642822485)
                  ·
                    refine ⟨104572731531252689313413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17847079514667125642822485 104572731531252689313413)
                    ·
                      rfl

theorem cell22_305482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_305482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305482 prefixEnd_305482 := by exact prefixLift 305482
  have htrace : WordTrace (prefixWord ++ tailWord_305482) baseStart_305482 baseEnd_305482 := by
    simpa [prefixWord, tailWord_305482, baseEnd_305482] using wordTrace_append hprefix tailTrace_305482
  have hstable : (prefixWord ++ tailWord_305482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305482).length < 2 ^ (prefixWord ++ tailWord_305482).sum := by decide
  have hdescent : baseEnd_305482 < baseStart_305482 := by decide
  rcases family_descends (prefixWord ++ tailWord_305482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305484 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 6]
def baseStart_305484 : Nat := 118140960795 + 305484 * 2 ^ 59
def prefixEnd_305484 : Nat := 4983230072969 + 3 ^ 40 * 305484 * 2
def baseEnd_305484 : Nat := 34857805390708450254469

theorem tailTrace_305484 : CollatzResearch.WordTrace tailWord_305484 prefixEnd_305484 34857805390708450254469 := by
  unfold tailWord_305484
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570958412645557679321753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7427944550194076905762337 5570958412645557679321753)
  ·
    refine ⟨4178218809484168259491315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5570958412645557679321753 4178218809484168259491315)
    ·
      refine ⟨6267328214226252389236973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4178218809484168259491315 6267328214226252389236973)
      ·
        refine ⟨2350248080334844645963865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6267328214226252389236973 2350248080334844645963865)
        ·
          refine ⟨1762686060251133484472899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2350248080334844645963865 1762686060251133484472899)
          ·
            refine ⟨2644029090376700226709349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762686060251133484472899 2644029090376700226709349)
            ·
              refine ⟨495755454445631292508003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2644029090376700226709349 495755454445631292508003)
              ·
                refine ⟨743633181668446938762005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495755454445631292508003 743633181668446938762005)
                ·
                  refine ⟨34857805390708450254469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 743633181668446938762005 34857805390708450254469)
                  ·
                    rfl

theorem cell22_305484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_305484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305484 prefixEnd_305484 := by exact prefixLift 305484
  have htrace : WordTrace (prefixWord ++ tailWord_305484) baseStart_305484 baseEnd_305484 := by
    simpa [prefixWord, tailWord_305484, baseEnd_305484] using wordTrace_append hprefix tailTrace_305484
  have hstable : (prefixWord ++ tailWord_305484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305484).length < 2 ^ (prefixWord ++ tailWord_305484).sum := by decide
  have hdescent : baseEnd_305484 < baseStart_305484 := by decide
  rcases family_descends (prefixWord ++ tailWord_305484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305550 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_305550 : Nat := 118140960795 + 305550 * 2 ^ 59
def prefixEnd_305550 : Nat := 4983230072969 + 3 ^ 40 * 305550 * 2
def baseEnd_305550 : Nat := 104596009320923178613205

theorem tailTrace_305550 : CollatzResearch.WordTrace tailWord_305550 prefixEnd_305550 104596009320923178613205 := by
  unfold tailWord_305550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393040505381501078818263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7429549362034672420364069 1393040505381501078818263)
  ·
    refine ⟨2089560758072251618227395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393040505381501078818263 2089560758072251618227395)
    ·
      refine ⟨3134341137108377427341093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2089560758072251618227395 3134341137108377427341093)
      ·
        refine ⟨587688963207820767626455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3134341137108377427341093 587688963207820767626455)
        ·
          refine ⟨881533444811731151439683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587688963207820767626455 881533444811731151439683)
          ·
            refine ⟨1322300167217596727159525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881533444811731151439683 1322300167217596727159525)
            ·
              refine ⟨247931281353299386342411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1322300167217596727159525 247931281353299386342411)
              ·
                refine ⟨371896922029949079513617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247931281353299386342411 371896922029949079513617)
                ·
                  refine ⟨278922691522461809635213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371896922029949079513617 278922691522461809635213)
                  ·
                    refine ⟨104596009320923178613205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 278922691522461809635213 104596009320923178613205)
                    ·
                      rfl

theorem cell22_305550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_305550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305550 prefixEnd_305550 := by exact prefixLift 305550
  have htrace : WordTrace (prefixWord ++ tailWord_305550) baseStart_305550 baseEnd_305550 := by
    simpa [prefixWord, tailWord_305550, baseEnd_305550] using wordTrace_append hprefix tailTrace_305550
  have hstable : (prefixWord ++ tailWord_305550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305550).length < 2 ^ (prefixWord ++ tailWord_305550).sum := by decide
  have hdescent : baseEnd_305550 < baseStart_305550 := by decide
  rcases family_descends (prefixWord ++ tailWord_305550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305591 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 5]
def baseStart_305591 : Nat := 118140960795 + 305591 * 2 ^ 59
def prefixEnd_305591 : Nat := 4983230072969 + 3 ^ 40 * 305591 * 2
def baseEnd_305591 : Nat := 34870014819604246112693

theorem tailTrace_305591 : CollatzResearch.WordTrace tailWord_305591 prefixEnd_305591 34870014819604246112693 := by
  unfold tailWord_305591
  simp only [CollatzResearch.WordTrace]
  refine ⟨11145819435903472632788627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7430546290602315088525751 11145819435903472632788627)
  ·
    refine ⟨16718729153855208949182941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11145819435903472632788627 16718729153855208949182941)
    ·
      refine ⟨6269523432695703355943603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16718729153855208949182941 6269523432695703355943603)
      ·
        refine ⟨9404285149043555033915405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6269523432695703355943603 9404285149043555033915405)
        ·
          refine ⟨3526606930891333137718277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9404285149043555033915405 3526606930891333137718277)
          ·
            refine ⟨661238799542124963322177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3526606930891333137718277 661238799542124963322177)
            ·
              refine ⟨495929099656593722491633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661238799542124963322177 495929099656593722491633)
              ·
                refine ⟨371946824742445291868725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495929099656593722491633 371946824742445291868725)
                ·
                  refine ⟨34870014819604246112693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 371946824742445291868725 34870014819604246112693)
                  ·
                    rfl

theorem cell22_305591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 5].length) (baseStart_305591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305591 prefixEnd_305591 := by exact prefixLift 305591
  have htrace : WordTrace (prefixWord ++ tailWord_305591) baseStart_305591 baseEnd_305591 := by
    simpa [prefixWord, tailWord_305591, baseEnd_305591] using wordTrace_append hprefix tailTrace_305591
  have hstable : (prefixWord ++ tailWord_305591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305591).length < 2 ^ (prefixWord ++ tailWord_305591).sum := by decide
  have hdescent : baseEnd_305591 < baseStart_305591 := by decide
  rcases family_descends (prefixWord ++ tailWord_305591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305621 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_305621 : Nat := 118140960795 + 305621 * 2 ^ 59
def prefixEnd_305621 : Nat := 4983230072969 + 3 ^ 40 * 305621 * 2
def baseEnd_305621 : Nat := 104620314071902660087987

theorem tailTrace_305621 : CollatzResearch.WordTrace tailWord_305621 prefixEnd_305621 104620314071902660087987 := by
  unfold tailWord_305621
  simp only [CollatzResearch.WordTrace]
  refine ⟨11146913625794787756380717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7431275750529858504253811 11146913625794787756380717)
  ·
    refine ⟨4180092609673045408642769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11146913625794787756380717 4180092609673045408642769)
    ·
      refine ⟨3135069457254784056482077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4180092609673045408642769 3135069457254784056482077)
      ·
        refine ⟨1175651046470544021180779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3135069457254784056482077 1175651046470544021180779)
        ·
          refine ⟨1763476569705816031771169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175651046470544021180779 1763476569705816031771169)
          ·
            refine ⟨1322607427279362023828377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763476569705816031771169 1322607427279362023828377)
            ·
              refine ⟨991955570459521517871283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322607427279362023828377 991955570459521517871283)
              ·
                refine ⟨1487933355689282276806925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991955570459521517871283 1487933355689282276806925)
                ·
                  refine ⟨557975008383480853802597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1487933355689282276806925 557975008383480853802597)
                  ·
                    refine ⟨104620314071902660087987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 557975008383480853802597 104620314071902660087987)
                    ·
                      rfl

theorem cell22_305621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_305621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305621 prefixEnd_305621 := by exact prefixLift 305621
  have htrace : WordTrace (prefixWord ++ tailWord_305621) baseStart_305621 baseEnd_305621 := by
    simpa [prefixWord, tailWord_305621, baseEnd_305621] using wordTrace_append hprefix tailTrace_305621
  have hstable : (prefixWord ++ tailWord_305621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305621).length < 2 ^ (prefixWord ++ tailWord_305621).sum := by decide
  have hdescent : baseEnd_305621 < baseStart_305621 := by decide
  rcases family_descends (prefixWord ++ tailWord_305621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305651 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 4, 3]
def baseStart_305651 : Nat := 118140960795 + 305651 * 2 ^ 59
def prefixEnd_305651 : Nat := 4983230072969 + 3 ^ 40 * 305651 * 2
def baseEnd_305651 : Nat := 104630583684992581837895

theorem tailTrace_305651 : CollatzResearch.WordTrace tailWord_305651 prefixEnd_305651 104630583684992581837895 := by
  unfold tailWord_305651
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148007815686102879972807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7432005210457401919981871 11148007815686102879972807)
  ·
    refine ⟨16722011723529154319959211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11148007815686102879972807 16722011723529154319959211)
    ·
      refine ⟨25083017585293731479938817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16722011723529154319959211 25083017585293731479938817)
      ·
        refine ⟨18812263188970298609954113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25083017585293731479938817 18812263188970298609954113)
        ·
          refine ⟨14109197391727723957465585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18812263188970298609954113 14109197391727723957465585)
          ·
            refine ⟨10581898043795792968099189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14109197391727723957465585 10581898043795792968099189)
            ·
              refine ⟨992052941605855590759299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10581898043795792968099189 992052941605855590759299)
              ·
                refine ⟨1488079412408783386138949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992052941605855590759299 1488079412408783386138949)
                ·
                  refine ⟨279014889826646884901053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488079412408783386138949 279014889826646884901053)
                  ·
                    refine ⟨104630583684992581837895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279014889826646884901053 104630583684992581837895)
                    ·
                      rfl

theorem cell22_305651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 3].length) (baseStart_305651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305651 prefixEnd_305651 := by exact prefixLift 305651
  have htrace : WordTrace (prefixWord ++ tailWord_305651) baseStart_305651 baseEnd_305651 := by
    simpa [prefixWord, tailWord_305651, baseEnd_305651] using wordTrace_append hprefix tailTrace_305651
  have hstable : (prefixWord ++ tailWord_305651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305651).length < 2 ^ (prefixWord ++ tailWord_305651).sum := by decide
  have hdescent : baseEnd_305651 < baseStart_305651 := by decide
  rcases family_descends (prefixWord ++ tailWord_305651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305668 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_305668 : Nat := 118140960795 + 305668 * 2 ^ 59
def prefixEnd_305668 : Nat := 4983230072969 + 3 ^ 40 * 305668 * 2
def baseEnd_305668 : Nat := 104636403132410204162843

theorem tailTrace_305668 : CollatzResearch.WordTrace tailWord_305668 prefixEnd_305668 104636403132410204162843 := by
  unfold tailWord_305668
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574313928312257391670829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7432418571083009855561105 5574313928312257391670829)
  ·
    refine ⟨2090367723117096521876561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5574313928312257391670829 2090367723117096521876561)
    ·
      refine ⟨1567775792337822391407421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2090367723117096521876561 1567775792337822391407421)
      ·
        refine ⟨587915922126683396777783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1567775792337822391407421 587915922126683396777783)
        ·
          refine ⟨881873883190025095166675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587915922126683396777783 881873883190025095166675)
          ·
            refine ⟨1322810824785037642750013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881873883190025095166675 1322810824785037642750013)
            ·
              refine ⟨496054059294389116031255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1322810824785037642750013 496054059294389116031255)
              ·
                refine ⟨744081088941583674046883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496054059294389116031255 744081088941583674046883)
                ·
                  refine ⟨1116121633412375511070325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 744081088941583674046883 1116121633412375511070325)
                  ·
                    refine ⟨104636403132410204162843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1116121633412375511070325 104636403132410204162843)
                    ·
                      rfl

theorem cell22_305668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_305668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305668 prefixEnd_305668 := by exact prefixLift 305668
  have htrace : WordTrace (prefixWord ++ tailWord_305668) baseStart_305668 baseEnd_305668 := by
    simpa [prefixWord, tailWord_305668, baseEnd_305668] using wordTrace_append hprefix tailTrace_305668
  have hstable : (prefixWord ++ tailWord_305668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305668).length < 2 ^ (prefixWord ++ tailWord_305668).sum := by decide
  have hdescent : baseEnd_305668 < baseStart_305668 := by decide
  rcases family_descends (prefixWord ++ tailWord_305668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305687 : List Nat := [1, 1, 3, 6, 1, 2, 1, 3, 4]
def baseStart_305687 : Nat := 118140960795 + 305687 * 2 ^ 59
def prefixEnd_305687 : Nat := 4983230072969 + 3 ^ 40 * 305687 * 2
def baseEnd_305687 : Nat := 34880969073566829312595

theorem tailTrace_305687 : CollatzResearch.WordTrace tailWord_305687 prefixEnd_305687 34880969073566829312595 := by
  unfold tailWord_305687
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149320843555681028283315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7432880562370454018855543 11149320843555681028283315)
  ·
    refine ⟨16723981265333521542424973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11149320843555681028283315 16723981265333521542424973)
    ·
      refine ⟨6271492974500070578409365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16723981265333521542424973 6271492974500070578409365)
      ·
        refine ⟨293976233179690808362939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6271492974500070578409365 293976233179690808362939)
        ·
          refine ⟨440964349769536212544409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293976233179690808362939 440964349769536212544409)
          ·
            refine ⟨330723262327152159408307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440964349769536212544409 330723262327152159408307)
            ·
              refine ⟨496084893490728239112461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330723262327152159408307 496084893490728239112461)
              ·
                refine ⟨186031835059023089667173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496084893490728239112461 186031835059023089667173)
                ·
                  refine ⟨34880969073566829312595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186031835059023089667173 34880969073566829312595)
                  ·
                    rfl

theorem cell22_305687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 4].length) (baseStart_305687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305687 prefixEnd_305687 := by exact prefixLift 305687
  have htrace : WordTrace (prefixWord ++ tailWord_305687) baseStart_305687 baseEnd_305687 := by
    simpa [prefixWord, tailWord_305687, baseEnd_305687] using wordTrace_append hprefix tailTrace_305687
  have hstable : (prefixWord ++ tailWord_305687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305687).length < 2 ^ (prefixWord ++ tailWord_305687).sum := by decide
  have hdescent : baseEnd_305687 < baseStart_305687 := by decide
  rcases family_descends (prefixWord ++ tailWord_305687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305700 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_305700 : Nat := 118140960795 + 305700 * 2 ^ 59
def prefixEnd_305700 : Nat := 4983230072969 + 3 ^ 40 * 305700 * 2
def baseEnd_305700 : Nat := 104647357386372787362745

theorem tailTrace_305700 : CollatzResearch.WordTrace tailWord_305700 prefixEnd_305700 104647357386372787362745 := by
  unfold tailWord_305700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574897496254292124253277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7433196661672389499004369 5574897496254292124253277)
  ·
    refine ⟨2090586561095359546594979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5574897496254292124253277 2090586561095359546594979)
    ·
      refine ⟨3135879841643039319892469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090586561095359546594979 3135879841643039319892469)
      ·
        refine ⟨293988735154034936239919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3135879841643039319892469 293988735154034936239919)
        ·
          refine ⟨440983102731052404359879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293988735154034936239919 440983102731052404359879)
          ·
            refine ⟨661474654096578606539819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440983102731052404359879 661474654096578606539819)
            ·
              refine ⟨992211981144867909809729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661474654096578606539819 992211981144867909809729)
              ·
                refine ⟨744158985858650932357297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992211981144867909809729 744158985858650932357297)
                ·
                  refine ⟨558119239393988199267973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744158985858650932357297 558119239393988199267973)
                  ·
                    refine ⟨104647357386372787362745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 558119239393988199267973 104647357386372787362745)
                    ·
                      rfl

theorem cell22_305700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_305700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305700 prefixEnd_305700 := by exact prefixLift 305700
  have htrace : WordTrace (prefixWord ++ tailWord_305700) baseStart_305700 baseEnd_305700 := by
    simpa [prefixWord, tailWord_305700, baseEnd_305700] using wordTrace_append hprefix tailTrace_305700
  have hstable : (prefixWord ++ tailWord_305700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305700).length < 2 ^ (prefixWord ++ tailWord_305700).sum := by decide
  have hdescent : baseEnd_305700 < baseStart_305700 := by decide
  rcases family_descends (prefixWord ++ tailWord_305700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305713 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 3, 3]
def baseStart_305713 : Nat := 118140960795 + 305713 * 2 ^ 59
def prefixEnd_305713 : Nat := 4983230072969 + 3 ^ 40 * 305713 * 2
def baseEnd_305713 : Nat := 104651807552045086787705

theorem tailTrace_305713 : CollatzResearch.WordTrace tailWord_305713 prefixEnd_305713 104651807552045086787705 := by
  unfold tailWord_305713
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150269141461487468729793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7433512760974324979153195 11150269141461487468729793)
  ·
    refine ⟨8362701856096115601547345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11150269141461487468729793 8362701856096115601547345)
    ·
      refine ⟨6272026392072086701160509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8362701856096115601547345 6272026392072086701160509)
      ·
        refine ⟨2352009897027032512935191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6272026392072086701160509 2352009897027032512935191)
        ·
          refine ⟨3528014845540548769402787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352009897027032512935191 3528014845540548769402787)
          ·
            refine ⟨5292022268310823154104181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528014845540548769402787 5292022268310823154104181)
            ·
              refine ⟨496127087654139670697267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5292022268310823154104181 496127087654139670697267)
              ·
                refine ⟨744190631481209506045901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496127087654139670697267 744190631481209506045901)
                ·
                  refine ⟨279071486805453564767213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744190631481209506045901 279071486805453564767213)
                  ·
                    refine ⟨104651807552045086787705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279071486805453564767213 104651807552045086787705)
                    ·
                      rfl

theorem cell22_305713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 3, 3].length) (baseStart_305713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305713 prefixEnd_305713 := by exact prefixLift 305713
  have htrace : WordTrace (prefixWord ++ tailWord_305713) baseStart_305713 baseEnd_305713 := by
    simpa [prefixWord, tailWord_305713, baseEnd_305713] using wordTrace_append hprefix tailTrace_305713
  have hstable : (prefixWord ++ tailWord_305713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305713).length < 2 ^ (prefixWord ++ tailWord_305713).sum := by decide
  have hdescent : baseEnd_305713 < baseStart_305713 := by decide
  rcases family_descends (prefixWord ++ tailWord_305713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305773 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_305773 : Nat := 118140960795 + 305773 * 2 ^ 59
def prefixEnd_305773 : Nat := 4983230072969 + 3 ^ 40 * 305773 * 2
def baseEnd_305773 : Nat := 104672346778224930287521

theorem tailTrace_305773 : CollatzResearch.WordTrace tailWord_305773 prefixEnd_305773 104672346778224930287521 := by
  unfold tailWord_305773
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152457521244117715913973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7434971680829411810609315 11152457521244117715913973)
  ·
    refine ⟨1045542892616636035866935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11152457521244117715913973 1045542892616636035866935)
    ·
      refine ⟨1568314338924954053800403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045542892616636035866935 1568314338924954053800403)
      ·
        refine ⟨2352471508387431080700605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568314338924954053800403 2352471508387431080700605)
        ·
          refine ⟨882176815645286655262727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2352471508387431080700605 882176815645286655262727)
          ·
            refine ⟨1323265223467929982894091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882176815645286655262727 1323265223467929982894091)
            ·
              refine ⟨1984897835201894974341137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323265223467929982894091 1984897835201894974341137)
              ·
                refine ⟨1488673376401421230755853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1984897835201894974341137 1488673376401421230755853)
                ·
                  refine ⟨558252516150532961533445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1488673376401421230755853 558252516150532961533445)
                  ·
                    refine ⟨104672346778224930287521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 558252516150532961533445 104672346778224930287521)
                    ·
                      rfl

theorem cell22_305773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_305773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305773 prefixEnd_305773 := by exact prefixLift 305773
  have htrace : WordTrace (prefixWord ++ tailWord_305773) baseStart_305773 baseEnd_305773 := by
    simpa [prefixWord, tailWord_305773, baseEnd_305773] using wordTrace_append hprefix tailTrace_305773
  have hstable : (prefixWord ++ tailWord_305773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305773).length < 2 ^ (prefixWord ++ tailWord_305773).sum := by decide
  have hdescent : baseEnd_305773 < baseStart_305773 := by decide
  rcases family_descends (prefixWord ++ tailWord_305773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305816 : List Nat := [2, 1, 2, 4, 1, 1, 11]
def baseStart_305816 : Nat := 118140960795 + 305816 * 2 ^ 59
def prefixEnd_305816 : Nat := 4983230072969 + 3 ^ 40 * 305816 * 2
def baseEnd_305816 : Nat := 3877298761369894498607

theorem tailTrace_305816 : CollatzResearch.WordTrace tailWord_305816 prefixEnd_305816 3877298761369894498607 := by
  unfold tailWord_305816
  simp only [CollatzResearch.WordTrace]
  refine ⟨5577012930044168029864651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7436017240058890706486201 5577012930044168029864651)
  ·
    refine ⟨8365519395066252044796977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5577012930044168029864651 8365519395066252044796977)
    ·
      refine ⟨6274139546299689033597733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8365519395066252044796977 6274139546299689033597733)
      ·
        refine ⟨1176401164931191693799575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6274139546299689033597733 1176401164931191693799575)
        ·
          refine ⟨1764601747396787540699363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176401164931191693799575 1764601747396787540699363)
          ·
            refine ⟨2646902621095181311049045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764601747396787540699363 2646902621095181311049045)
            ·
              refine ⟨3877298761369894498607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2646902621095181311049045 3877298761369894498607)
              ·
                rfl

theorem cell22_305816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 11].length) (baseStart_305816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305816 prefixEnd_305816 := by exact prefixLift 305816
  have htrace : WordTrace (prefixWord ++ tailWord_305816) baseStart_305816 baseEnd_305816 := by
    simpa [prefixWord, tailWord_305816, baseEnd_305816] using wordTrace_append hprefix tailTrace_305816
  have hstable : (prefixWord ++ tailWord_305816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305816).length < 2 ^ (prefixWord ++ tailWord_305816).sum := by decide
  have hdescent : baseEnd_305816 < baseStart_305816 := by decide
  rcases family_descends (prefixWord ++ tailWord_305816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305820 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_305820 : Nat := 118140960795 + 305820 * 2 ^ 59
def prefixEnd_305820 : Nat := 4983230072969 + 3 ^ 40 * 305820 * 2
def baseEnd_305820 : Nat := 104688435838732474362377

theorem tailTrace_305820 : CollatzResearch.WordTrace tailWord_305820 prefixEnd_305820 104688435838732474362377 := by
  unfold tailWord_305820
  simp only [CollatzResearch.WordTrace]
  refine ⟨5577085876036922371437457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7436114501382563161916609 5577085876036922371437457)
  ·
    refine ⟨4182814407027691778578093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5577085876036922371437457 4182814407027691778578093)
    ·
      refine ⟨1568555402635384416966785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4182814407027691778578093 1568555402635384416966785)
      ·
        refine ⟨1176416551976538312725089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568555402635384416966785 1176416551976538312725089)
        ·
          refine ⟨882312413982403734543817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176416551976538312725089 882312413982403734543817)
          ·
            refine ⟨661734310486802800907863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 882312413982403734543817 661734310486802800907863)
            ·
              refine ⟨992601465730204201361795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661734310486802800907863 992601465730204201361795)
              ·
                refine ⟨1488902198595306302042693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992601465730204201361795 1488902198595306302042693)
                ·
                  refine ⟨279169162236619931633005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488902198595306302042693 279169162236619931633005)
                  ·
                    refine ⟨104688435838732474362377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279169162236619931633005 104688435838732474362377)
                    ·
                      rfl

theorem cell22_305820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_305820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305820 prefixEnd_305820 := by exact prefixLift 305820
  have htrace : WordTrace (prefixWord ++ tailWord_305820) baseStart_305820 baseEnd_305820 := by
    simpa [prefixWord, tailWord_305820, baseEnd_305820] using wordTrace_append hprefix tailTrace_305820
  have hstable : (prefixWord ++ tailWord_305820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305820).length < 2 ^ (prefixWord ++ tailWord_305820).sum := by decide
  have hdescent : baseEnd_305820 < baseStart_305820 := by decide
  rcases family_descends (prefixWord ++ tailWord_305820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305953 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 1, 6]
def baseStart_305953 : Nat := 118140960795 + 305953 * 2 ^ 59
def prefixEnd_305953 : Nat := 4983230072969 + 3 ^ 40 * 305953 * 2
def baseEnd_305953 : Nat := 104733964456764460786969

theorem tailTrace_305953 : CollatzResearch.WordTrace tailWord_305953 prefixEnd_305953 104733964456764460786969 := by
  unfold tailWord_305953
  simp only [CollatzResearch.WordTrace]
  refine ⟨11159022660592008457466513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7439348440394672304977675 11159022660592008457466513)
  ·
    refine ⟨8369266995444006343099885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11159022660592008457466513 8369266995444006343099885)
    ·
      refine ⟨3138475123291502378662457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8369266995444006343099885 3138475123291502378662457)
      ·
        refine ⟨2353856342468626783996843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3138475123291502378662457 2353856342468626783996843)
        ·
          refine ⟨3530784513702940175995265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353856342468626783996843 3530784513702940175995265)
          ·
            refine ⟨2648088385277205131996449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530784513702940175995265 2648088385277205131996449)
            ·
              refine ⟨1986066288957903848997337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648088385277205131996449 1986066288957903848997337)
              ·
                refine ⟨1489549716718427886748003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986066288957903848997337 1489549716718427886748003)
                ·
                  refine ⟨2234324575077641830122005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489549716718427886748003 2234324575077641830122005)
                  ·
                    refine ⟨104733964456764460786969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2234324575077641830122005 104733964456764460786969)
                    ·
                      rfl

theorem cell22_305953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_305953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305953 prefixEnd_305953 := by exact prefixLift 305953
  have htrace : WordTrace (prefixWord ++ tailWord_305953) baseStart_305953 baseEnd_305953 := by
    simpa [prefixWord, tailWord_305953, baseEnd_305953] using wordTrace_append hprefix tailTrace_305953
  have hstable : (prefixWord ++ tailWord_305953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305953).length < 2 ^ (prefixWord ++ tailWord_305953).sum := by decide
  have hdescent : baseEnd_305953 < baseStart_305953 := by decide
  rcases family_descends (prefixWord ++ tailWord_305953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305998 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_305998 : Nat := 118140960795 + 305998 * 2 ^ 59
def prefixEnd_305998 : Nat := 4983230072969 + 3 ^ 40 * 305998 * 2
def baseEnd_305998 : Nat := 104749368876399343411831

theorem tailTrace_305998 : CollatzResearch.WordTrace tailWord_305998 prefixEnd_305998 104749368876399343411831 := by
  unfold tailWord_305998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395082993178622642856831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7440442630285987428569765 1395082993178622642856831)
  ·
    refine ⟨2092624489767933964285247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1395082993178622642856831 2092624489767933964285247)
    ·
      refine ⟨3138936734651900946427871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092624489767933964285247 3138936734651900946427871)
      ·
        refine ⟨4708405101977851419641807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138936734651900946427871 4708405101977851419641807)
        ·
          refine ⟨7062607652966777129462711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708405101977851419641807 7062607652966777129462711)
          ·
            refine ⟨10593911479450165694194067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7062607652966777129462711 10593911479450165694194067)
            ·
              refine ⟨15890867219175248541291101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10593911479450165694194067 15890867219175248541291101)
              ·
                refine ⟨5959075207190718202984163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15890867219175248541291101 5959075207190718202984163)
                ·
                  refine ⟨8938612810786077304476245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5959075207190718202984163 8938612810786077304476245)
                  ·
                    refine ⟨104749368876399343411831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8938612810786077304476245 104749368876399343411831)
                    ·
                      rfl

theorem cell22_305998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_305998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_305998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_305998 prefixEnd_305998 := by exact prefixLift 305998
  have htrace : WordTrace (prefixWord ++ tailWord_305998) baseStart_305998 baseEnd_305998 := by
    simpa [prefixWord, tailWord_305998, baseEnd_305998] using wordTrace_append hprefix tailTrace_305998
  have hstable : (prefixWord ++ tailWord_305998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305998).length < 2 ^ (prefixWord ++ tailWord_305998).sum := by decide
  have hdescent : baseEnd_305998 < baseStart_305998 := by decide
  rcases family_descends (prefixWord ++ tailWord_305998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306000 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 3, 3]
def baseStart_306000 : Nat := 118140960795 + 306000 * 2 ^ 59
def prefixEnd_306000 : Nat := 4983230072969 + 3 ^ 40 * 306000 * 2
def baseEnd_306000 : Nat := 104750053517272004861825

theorem tailTrace_306000 : CollatzResearch.WordTrace tailWord_306000 prefixEnd_306000 104750053517272004861825 := by
  unfold tailWord_306000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580368445710867742213727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7440491260947823656284969 5580368445710867742213727)
  ·
    refine ⟨8370552668566301613320591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5580368445710867742213727 8370552668566301613320591)
    ·
      refine ⟨12555829002849452419980887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8370552668566301613320591 12555829002849452419980887)
      ·
        refine ⟨18833743504274178629971331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12555829002849452419980887 18833743504274178629971331)
        ·
          refine ⟨28250615256411267944956997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18833743504274178629971331 28250615256411267944956997)
          ·
            refine ⟨5296990360577112739679437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28250615256411267944956997 5296990360577112739679437)
            ·
              refine ⟨1986371385216417277379789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5296990360577112739679437 1986371385216417277379789)
              ·
                refine ⟨744889269456156479017421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1986371385216417277379789 744889269456156479017421)
                ·
                  refine ⟨279333476046058679631533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744889269456156479017421 279333476046058679631533)
                  ·
                    refine ⟨104750053517272004861825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279333476046058679631533 104750053517272004861825)
                    ·
                      rfl

theorem cell22_306000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_306000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306000 prefixEnd_306000 := by exact prefixLift 306000
  have htrace : WordTrace (prefixWord ++ tailWord_306000) baseStart_306000 baseEnd_306000 := by
    simpa [prefixWord, tailWord_306000, baseEnd_306000] using wordTrace_append hprefix tailTrace_306000
  have hstable : (prefixWord ++ tailWord_306000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306000).length < 2 ^ (prefixWord ++ tailWord_306000).sum := by decide
  have hdescent : baseEnd_306000 < baseStart_306000 := by decide
  rcases family_descends (prefixWord ++ tailWord_306000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306034 : List Nat := [3, 2, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_306034 : Nat := 118140960795 + 306034 * 2 ^ 59
def prefixEnd_306034 : Nat := 4983230072969 + 3 ^ 40 * 306034 * 2
def baseEnd_306034 : Nat := 104761692412107249511721

theorem tailTrace_306034 : CollatzResearch.WordTrace tailWord_306034 prefixEnd_306034 104761692412107249511721 := by
  unfold tailWord_306034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790494243324639822791289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7441317982199039527443437 2790494243324639822791289)
  ·
    refine ⟨2092870682493479867093467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2790494243324639822791289 2092870682493479867093467)
    ·
      refine ⟨3139306023740219800640201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092870682493479867093467 3139306023740219800640201)
      ·
        refine ⟨2354479517805164850480151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3139306023740219800640201 2354479517805164850480151)
        ·
          refine ⟨3531719276707747275720227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354479517805164850480151 3531719276707747275720227)
          ·
            refine ⟨5297578915061620913580341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3531719276707747275720227 5297578915061620913580341)
            ·
              refine ⟨496648023287026960648157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5297578915061620913580341 496648023287026960648157)
              ·
                refine ⟨186243008732635110243059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496648023287026960648157 186243008732635110243059)
                ·
                  refine ⟨279364513098952665364589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186243008732635110243059 279364513098952665364589)
                  ·
                    refine ⟨104761692412107249511721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279364513098952665364589 104761692412107249511721)
                    ·
                      rfl

theorem cell22_306034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_306034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306034 prefixEnd_306034 := by exact prefixLift 306034
  have htrace : WordTrace (prefixWord ++ tailWord_306034) baseStart_306034 baseEnd_306034 := by
    simpa [prefixWord, tailWord_306034, baseEnd_306034] using wordTrace_append hprefix tailTrace_306034
  have hstable : (prefixWord ++ tailWord_306034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306034).length < 2 ^ (prefixWord ++ tailWord_306034).sum := by decide
  have hdescent : baseEnd_306034 < baseStart_306034 := by decide
  rcases family_descends (prefixWord ++ tailWord_306034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306109 : List Nat := [1, 4, 1, 2, 4, 1, 1, 4, 4]
def baseStart_306109 : Nat := 118140960795 + 306109 * 2 ^ 59
def prefixEnd_306109 : Nat := 4983230072969 + 3 ^ 40 * 306109 * 2
def baseEnd_306109 : Nat := 34929122148277351295497

theorem tailTrace_306109 : CollatzResearch.WordTrace tailWord_306109 prefixEnd_306109 34929122148277351295497 := by
  unfold tailWord_306109
  simp only [CollatzResearch.WordTrace]
  refine ⟨11164712448026847100145381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7443141632017898066763587 11164712448026847100145381)
  ·
    refine ⟨2093383584005033831277259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11164712448026847100145381 2093383584005033831277259)
    ·
      refine ⟨3140075376007550746915889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2093383584005033831277259 3140075376007550746915889)
      ·
        refine ⟨2355056532005663060186917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3140075376007550746915889 2355056532005663060186917)
        ·
          refine ⟨441573099751061823785047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2355056532005663060186917 441573099751061823785047)
          ·
            refine ⟨662359649626592735677571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441573099751061823785047 662359649626592735677571)
            ·
              refine ⟨993539474439889103516357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662359649626592735677571 993539474439889103516357)
              ·
                refine ⟨186288651457479206909317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 993539474439889103516357 186288651457479206909317)
                ·
                  refine ⟨34929122148277351295497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186288651457479206909317 34929122148277351295497)
                  ·
                    rfl

theorem cell22_306109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_306109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306109 prefixEnd_306109 := by exact prefixLift 306109
  have htrace : WordTrace (prefixWord ++ tailWord_306109) baseStart_306109 baseEnd_306109 := by
    simpa [prefixWord, tailWord_306109, baseEnd_306109] using wordTrace_append hprefix tailTrace_306109
  have hstable : (prefixWord ++ tailWord_306109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306109).length < 2 ^ (prefixWord ++ tailWord_306109).sum := by decide
  have hdescent : baseEnd_306109 < baseStart_306109 := by decide
  rcases family_descends (prefixWord ++ tailWord_306109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306137 : List Nat := [1, 2, 1, 2, 5, 2, 3, 6]
def baseStart_306137 : Nat := 118140960795 + 306137 * 2 ^ 59
def prefixEnd_306137 : Nat := 4983230072969 + 3 ^ 40 * 306137 * 2
def baseEnd_306137 : Nat := 11644105713005479354045

theorem tailTrace_306137 : CollatzResearch.WordTrace tailWord_306137 prefixEnd_306137 11644105713005479354045 := by
  unfold tailWord_306137
  simp only [CollatzResearch.WordTrace]
  refine ⟨11165733691925407882164665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7443822461283605254776443 11165733691925407882164665)
  ·
    refine ⟨8374300268944055911623499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11165733691925407882164665 8374300268944055911623499)
    ·
      refine ⟨12561450403416083867435249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8374300268944055911623499 12561450403416083867435249)
      ·
        refine ⟨9421087802562062900576437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12561450403416083867435249 9421087802562062900576437)
        ·
          refine ⟨883226981490193396929041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9421087802562062900576437 883226981490193396929041)
          ·
            refine ⟨662420236117645047696781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883226981490193396929041 662420236117645047696781)
            ·
              refine ⟨248407588544116892886293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662420236117645047696781 248407588544116892886293)
              ·
                refine ⟨11644105713005479354045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 248407588544116892886293 11644105713005479354045)
                ·
                  rfl

theorem cell22_306137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 6].length) (baseStart_306137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306137 prefixEnd_306137 := by exact prefixLift 306137
  have htrace : WordTrace (prefixWord ++ tailWord_306137) baseStart_306137 baseEnd_306137 := by
    simpa [prefixWord, tailWord_306137, baseEnd_306137] using wordTrace_append hprefix tailTrace_306137
  have hstable : (prefixWord ++ tailWord_306137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306137).length < 2 ^ (prefixWord ++ tailWord_306137).sum := by decide
  have hdescent : baseEnd_306137 < baseStart_306137 := by decide
  rcases family_descends (prefixWord ++ tailWord_306137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306158 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_306158 : Nat := 118140960795 + 306158 * 2 ^ 59
def prefixEnd_306158 : Nat := 4983230072969 + 3 ^ 40 * 306158 * 2
def baseEnd_306158 : Nat := 104804140146212259411341

theorem tailTrace_306158 : CollatzResearch.WordTrace tailWord_306158 prefixEnd_306158 104804140146212259411341 := by
  unfold tailWord_306158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395812453106166058584891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7444333083232885645786085 1395812453106166058584891)
  ·
    refine ⟨2093718679659249087877337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1395812453106166058584891 2093718679659249087877337)
    ·
      refine ⟨1570289009744436815908003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2093718679659249087877337 1570289009744436815908003)
      ·
        refine ⟨2355433514616655223862005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570289009744436815908003 2355433514616655223862005)
        ·
          refine ⟨220821891995311427237063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2355433514616655223862005 220821891995311427237063)
          ·
            refine ⟨331232837992967140855595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220821891995311427237063 331232837992967140855595)
            ·
              refine ⟨496849256989450711283393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331232837992967140855595 496849256989450711283393)
              ·
                refine ⟨372636942742088033462545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496849256989450711283393 372636942742088033462545)
                ·
                  refine ⟨279477707056566025096909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372636942742088033462545 279477707056566025096909)
                  ·
                    refine ⟨104804140146212259411341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279477707056566025096909 104804140146212259411341)
                    ·
                      rfl

theorem cell22_306158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_306158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306158 prefixEnd_306158 := by exact prefixLift 306158
  have htrace : WordTrace (prefixWord ++ tailWord_306158) baseStart_306158 baseEnd_306158 := by
    simpa [prefixWord, tailWord_306158, baseEnd_306158] using wordTrace_append hprefix tailTrace_306158
  have hstable : (prefixWord ++ tailWord_306158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306158).length < 2 ^ (prefixWord ++ tailWord_306158).sum := by decide
  have hdescent : baseEnd_306158 < baseStart_306158 := by decide
  rcases family_descends (prefixWord ++ tailWord_306158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306169 : List Nat := [1, 2, 1, 3, 1, 3, 1, 6, 1, 3]
def baseStart_306169 : Nat := 118140960795 + 306169 * 2 ^ 59
def prefixEnd_306169 : Nat := 4983230072969 + 3 ^ 40 * 306169 * 2
def baseEnd_306169 : Nat := 104807905671011897386307

theorem tailTrace_306169 : CollatzResearch.WordTrace tailWord_306169 prefixEnd_306169 104807905671011897386307 := by
  unfold tailWord_306169
  simp only [CollatzResearch.WordTrace]
  refine ⟨11166900827809477347329561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7444600551872984898219707 11166900827809477347329561)
  ·
    refine ⟨8375175620857108010497171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11166900827809477347329561 8375175620857108010497171)
    ·
      refine ⟨12562763431285662015745757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8375175620857108010497171 12562763431285662015745757)
      ·
        refine ⟨4711036286732123255904659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12562763431285662015745757 4711036286732123255904659)
        ·
          refine ⟨7066554430098184883856989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4711036286732123255904659 7066554430098184883856989)
          ·
            refine ⟨2649957911286819331446371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7066554430098184883856989 2649957911286819331446371)
            ·
              refine ⟨3974936866930228997169557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649957911286819331446371 3974936866930228997169557)
              ·
                refine ⟨186325165637354484242323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3974936866930228997169557 186325165637354484242323)
                ·
                  refine ⟨279487748456031726363485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186325165637354484242323 279487748456031726363485)
                  ·
                    refine ⟨104807905671011897386307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279487748456031726363485 104807905671011897386307)
                    ·
                      rfl

theorem cell22_306169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 3].length) (baseStart_306169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306169 prefixEnd_306169 := by exact prefixLift 306169
  have htrace : WordTrace (prefixWord ++ tailWord_306169) baseStart_306169 baseEnd_306169 := by
    simpa [prefixWord, tailWord_306169, baseEnd_306169] using wordTrace_append hprefix tailTrace_306169
  have hstable : (prefixWord ++ tailWord_306169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306169).length < 2 ^ (prefixWord ++ tailWord_306169).sum := by decide
  have hdescent : baseEnd_306169 < baseStart_306169 := by decide
  rcases family_descends (prefixWord ++ tailWord_306169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306246 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_306246 : Nat := 118140960795 + 306246 * 2 ^ 59
def prefixEnd_306246 : Nat := 4983230072969 + 3 ^ 40 * 306246 * 2
def baseEnd_306246 : Nat := 104834264344609363211071

theorem tailTrace_306246 : CollatzResearch.WordTrace tailWord_306246 prefixEnd_306246 104834264344609363211071 := by
  unfold tailWord_306246
  simp only [CollatzResearch.WordTrace]
  refine ⟨349053414016578734308831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7446472832353679665255061 349053414016578734308831)
  ·
    refine ⟨523580121024868101463247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349053414016578734308831 523580121024868101463247)
    ·
      refine ⟨785370181537302152194871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523580121024868101463247 785370181537302152194871)
      ·
        refine ⟨1178055272305953228292307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785370181537302152194871 1178055272305953228292307)
        ·
          refine ⟨1767082908458929842438461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178055272305953228292307 1767082908458929842438461)
          ·
            refine ⟨662656090672098690914423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1767082908458929842438461 662656090672098690914423)
            ·
              refine ⟨993984136008148036371635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 662656090672098690914423 993984136008148036371635)
              ·
                refine ⟨1490976204012222054557453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 993984136008148036371635 1490976204012222054557453)
                ·
                  refine ⟨559116076504583270459045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1490976204012222054557453 559116076504583270459045)
                  ·
                    refine ⟨104834264344609363211071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559116076504583270459045 104834264344609363211071)
                    ·
                      rfl

theorem cell22_306246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_306246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306246 prefixEnd_306246 := by exact prefixLift 306246
  have htrace : WordTrace (prefixWord ++ tailWord_306246) baseStart_306246 baseEnd_306246 := by
    simpa [prefixWord, tailWord_306246, baseEnd_306246] using wordTrace_append hprefix tailTrace_306246
  have hstable : (prefixWord ++ tailWord_306246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306246).length < 2 ^ (prefixWord ++ tailWord_306246).sum := by decide
  have hdescent : baseEnd_306246 < baseStart_306246 := by decide
  rcases family_descends (prefixWord ++ tailWord_306246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306257 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_306257 : Nat := 118140960795 + 306257 * 2 ^ 59
def prefixEnd_306257 : Nat := 4983230072969 + 3 ^ 40 * 306257 * 2
def baseEnd_306257 : Nat := 104838029869409001186037

theorem tailTrace_306257 : CollatzResearch.WordTrace tailWord_306257 prefixEnd_306257 104838029869409001186037 := by
  unfold tailWord_306257
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170110451490668376533025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7446740300993778917688683 11170110451490668376533025)
  ·
    refine ⟨8377582838618001282399769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11170110451490668376533025 8377582838618001282399769)
    ·
      refine ⟨6283187128963500961799827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8377582838618001282399769 6283187128963500961799827)
      ·
        refine ⟨9424780693445251442699741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283187128963500961799827 9424780693445251442699741)
        ·
          refine ⟨3534292760041969291012403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9424780693445251442699741 3534292760041969291012403)
          ·
            refine ⟨5301439140062953936518605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534292760041969291012403 5301439140062953936518605)
            ·
              refine ⟨1988039677523607726194477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5301439140062953936518605 1988039677523607726194477)
              ·
                refine ⟨745514879071352897322929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1988039677523607726194477 745514879071352897322929)
                ·
                  refine ⟨559136159303514672992197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745514879071352897322929 559136159303514672992197)
                  ·
                    refine ⟨104838029869409001186037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559136159303514672992197 104838029869409001186037)
                    ·
                      rfl

theorem cell22_306257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_306257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306257 prefixEnd_306257 := by exact prefixLift 306257
  have htrace : WordTrace (prefixWord ++ tailWord_306257) baseStart_306257 baseEnd_306257 := by
    simpa [prefixWord, tailWord_306257, baseEnd_306257] using wordTrace_append hprefix tailTrace_306257
  have hstable : (prefixWord ++ tailWord_306257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306257).length < 2 ^ (prefixWord ++ tailWord_306257).sum := by decide
  have hdescent : baseEnd_306257 < baseStart_306257 := by decide
  rcases family_descends (prefixWord ++ tailWord_306257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306338 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_306338 : Nat := 118140960795 + 306338 * 2 ^ 59
def prefixEnd_306338 : Nat := 4983230072969 + 3 ^ 40 * 306338 * 2
def baseEnd_306338 : Nat := 104865757824751789910789

theorem tailTrace_306338 : CollatzResearch.WordTrace tailWord_306338 prefixEnd_306338 104865757824751789910789 := by
  unfold tailWord_306338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793266191049304802557917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7448709842798146140154445 2793266191049304802557917)
  ·
    refine ⟨1047474821643489300959219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2793266191049304802557917 1047474821643489300959219)
    ·
      refine ⟨1571212232465233951438829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047474821643489300959219 1571212232465233951438829)
      ·
        refine ⟨589204587174462731789561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1571212232465233951438829 589204587174462731789561)
        ·
          refine ⟨441903440380847048842171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589204587174462731789561 441903440380847048842171)
          ·
            refine ⟨662855160571270573263257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441903440380847048842171 662855160571270573263257)
            ·
              refine ⟨497141370428452929947443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662855160571270573263257 497141370428452929947443)
              ·
                refine ⟨745712055642679394921165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497141370428452929947443 745712055642679394921165)
                ·
                  refine ⟨279642020866004773095437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745712055642679394921165 279642020866004773095437)
                  ·
                    refine ⟨104865757824751789910789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279642020866004773095437 104865757824751789910789)
                    ·
                      rfl

theorem cell22_306338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_306338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306338 prefixEnd_306338 := by exact prefixLift 306338
  have htrace : WordTrace (prefixWord ++ tailWord_306338) baseStart_306338 baseEnd_306338 := by
    simpa [prefixWord, tailWord_306338, baseEnd_306338] using wordTrace_append hprefix tailTrace_306338
  have hstable : (prefixWord ++ tailWord_306338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306338).length < 2 ^ (prefixWord ++ tailWord_306338).sum := by decide
  have hdescent : baseEnd_306338 < baseStart_306338 := by decide
  rcases family_descends (prefixWord ++ tailWord_306338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306372 : List Nat := [2, 3, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_306372 : Nat := 118140960795 + 306372 * 2 ^ 59
def prefixEnd_306372 : Nat := 4983230072969 + 3 ^ 40 * 306372 * 2
def baseEnd_306372 : Nat := 104877396719587034560685

theorem tailTrace_306372 : CollatzResearch.WordTrace tailWord_306372 prefixEnd_306372 104877396719587034560685 := by
  unfold tailWord_306372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587152423037021508484685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7449536564049362011312913 5587152423037021508484685)
  ·
    refine ⟨2095182158638883065681757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5587152423037021508484685 2095182158638883065681757)
    ·
      refine ⟨785693309489581149630659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2095182158638883065681757 785693309489581149630659)
      ·
        refine ⟨1178539964234371724445989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785693309489581149630659 1178539964234371724445989)
        ·
          refine ⟨220976243293944698333623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1178539964234371724445989 220976243293944698333623)
          ·
            refine ⟨331464364940917047500435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220976243293944698333623 331464364940917047500435)
            ·
              refine ⟨497196547411375571250653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331464364940917047500435 497196547411375571250653)
              ·
                refine ⟨186448705279265839218995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497196547411375571250653 186448705279265839218995)
                ·
                  refine ⟨279673057918898758828493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186448705279265839218995 279673057918898758828493)
                  ·
                    refine ⟨104877396719587034560685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279673057918898758828493 104877396719587034560685)
                    ·
                      rfl

theorem cell22_306372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_306372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306372 prefixEnd_306372 := by exact prefixLift 306372
  have htrace : WordTrace (prefixWord ++ tailWord_306372) baseStart_306372 baseEnd_306372 := by
    simpa [prefixWord, tailWord_306372, baseEnd_306372] using wordTrace_append hprefix tailTrace_306372
  have hstable : (prefixWord ++ tailWord_306372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306372).length < 2 ^ (prefixWord ++ tailWord_306372).sum := by decide
  have hdescent : baseEnd_306372 < baseStart_306372 := by decide
  rcases family_descends (prefixWord ++ tailWord_306372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306379 : List Nat := [1, 1, 1, 1, 3, 2, 2, 7, 4]
def baseStart_306379 : Nat := 118140960795 + 306379 * 2 ^ 59
def prefixEnd_306379 : Nat := 4983230072969 + 3 ^ 40 * 306379 * 2
def baseEnd_306379 : Nat := 34959930987547116545221

theorem tailTrace_306379 : CollatzResearch.WordTrace tailWord_306379 prefixEnd_306379 34959930987547116545221 := by
  unfold tailWord_306379
  simp only [CollatzResearch.WordTrace]
  refine ⟨11174560157048683212474191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7449706771365788808316127 11174560157048683212474191)
  ·
    refine ⟨16761840235573024818711287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11174560157048683212474191 16761840235573024818711287)
    ·
      refine ⟨25142760353359537228066931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16761840235573024818711287 25142760353359537228066931)
      ·
        refine ⟨37714140530039305842100397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25142760353359537228066931 37714140530039305842100397)
        ·
          refine ⟨14142802698764739690787649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37714140530039305842100397 14142802698764739690787649)
          ·
            refine ⟨10607102024073554768090737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14142802698764739690787649 10607102024073554768090737)
            ·
              refine ⟨7955326518055166076068053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10607102024073554768090737 7955326518055166076068053)
              ·
                refine ⟨186452965266917954907845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7955326518055166076068053 186452965266917954907845)
                ·
                  refine ⟨34959930987547116545221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186452965266917954907845 34959930987547116545221)
                  ·
                    rfl

theorem cell22_306379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 4].length) (baseStart_306379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306379 prefixEnd_306379 := by exact prefixLift 306379
  have htrace : WordTrace (prefixWord ++ tailWord_306379) baseStart_306379 baseEnd_306379 := by
    simpa [prefixWord, tailWord_306379, baseEnd_306379] using wordTrace_append hprefix tailTrace_306379
  have hstable : (prefixWord ++ tailWord_306379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306379).length < 2 ^ (prefixWord ++ tailWord_306379).sum := by decide
  have hdescent : baseEnd_306379 < baseStart_306379 := by decide
  rcases family_descends (prefixWord ++ tailWord_306379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306411 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 2, 3]
def baseStart_306411 : Nat := 118140960795 + 306411 * 2 ^ 59
def prefixEnd_306411 : Nat := 4983230072969 + 3 ^ 40 * 306411 * 2
def baseEnd_306411 : Nat := 104890747216603932835565

theorem tailTrace_306411 : CollatzResearch.WordTrace tailWord_306411 prefixEnd_306411 104890747216603932835565 := by
  unfold tailWord_306411
  simp only [CollatzResearch.WordTrace]
  refine ⟨11175727292932752677639087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7450484861955168451759391 11175727292932752677639087)
  ·
    refine ⟨16763590939399129016458631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11175727292932752677639087 16763590939399129016458631)
    ·
      refine ⟨25145386409098693524687947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16763590939399129016458631 25145386409098693524687947)
      ·
        refine ⟨37718079613648040287031921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25145386409098693524687947 37718079613648040287031921)
        ·
          refine ⟨28288559710236030215273941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37718079613648040287031921 28288559710236030215273941)
          ·
            refine ⟨663013118208656958170483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28288559710236030215273941 663013118208656958170483)
            ·
              refine ⟨994519677312985437255725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663013118208656958170483 994519677312985437255725)
              ·
                refine ⟨372944878992369538970897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 994519677312985437255725 372944878992369538970897)
                ·
                  refine ⟨279708659244277154228173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372944878992369538970897 279708659244277154228173)
                  ·
                    refine ⟨104890747216603932835565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279708659244277154228173 104890747216603932835565)
                    ·
                      rfl

theorem cell22_306411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 2, 3].length) (baseStart_306411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306411 prefixEnd_306411 := by exact prefixLift 306411
  have htrace : WordTrace (prefixWord ++ tailWord_306411) baseStart_306411 baseEnd_306411 := by
    simpa [prefixWord, tailWord_306411, baseEnd_306411] using wordTrace_append hprefix tailTrace_306411
  have hstable : (prefixWord ++ tailWord_306411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306411).length < 2 ^ (prefixWord ++ tailWord_306411).sum := by decide
  have hdescent : baseEnd_306411 < baseStart_306411 := by decide
  rcases family_descends (prefixWord ++ tailWord_306411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306544 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_306544 : Nat := 118140960795 + 306544 * 2 ^ 59
def prefixEnd_306544 : Nat := 4983230072969 + 3 ^ 40 * 306544 * 2
def baseEnd_306544 : Nat := 104936275834635919260157

theorem tailTrace_306544 : CollatzResearch.WordTrace tailWord_306544 prefixEnd_306544 104936275834635919260157 := by
  unfold tailWord_306544
  simp only [CollatzResearch.WordTrace]
  refine ⟨5590289100725458196115343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7453718800967277594820457 5590289100725458196115343)
  ·
    refine ⟨8385433651088187294173015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5590289100725458196115343 8385433651088187294173015)
    ·
      refine ⟨12578150476632280941259523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8385433651088187294173015 12578150476632280941259523)
      ·
        refine ⟨18867225714948421411889285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12578150476632280941259523 18867225714948421411889285)
        ·
          refine ⟨3537604821552829014729241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18867225714948421411889285 3537604821552829014729241)
          ·
            refine ⟨2653203616164621761046931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3537604821552829014729241 2653203616164621761046931)
            ·
              refine ⟨3979805424246932641570397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653203616164621761046931 3979805424246932641570397)
              ·
                refine ⟨1492427034092599740588899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3979805424246932641570397 1492427034092599740588899)
                ·
                  refine ⟨2238640551138899610883349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492427034092599740588899 2238640551138899610883349)
                  ·
                    refine ⟨104936275834635919260157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2238640551138899610883349 104936275834635919260157)
                    ·
                      rfl

theorem cell22_306544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_306544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306544 prefixEnd_306544 := by exact prefixLift 306544
  have htrace : WordTrace (prefixWord ++ tailWord_306544) baseStart_306544 baseEnd_306544 := by
    simpa [prefixWord, tailWord_306544, baseEnd_306544] using wordTrace_append hprefix tailTrace_306544
  have hstable : (prefixWord ++ tailWord_306544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306544).length < 2 ^ (prefixWord ++ tailWord_306544).sum := by decide
  have hdescent : baseEnd_306544 < baseStart_306544 := by decide
  rcases family_descends (prefixWord ++ tailWord_306544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306546 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_306546 : Nat := 118140960795 + 306546 * 2 ^ 59
def prefixEnd_306546 : Nat := 4983230072969 + 3 ^ 40 * 306546 * 2
def baseEnd_306546 : Nat := 104936960475508580710151

theorem tailTrace_306546 : CollatzResearch.WordTrace tailWord_306546 prefixEnd_306546 104936960475508580710151 := by
  unfold tailWord_306546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2795162786860917683450873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7453767431629113822535661 2795162786860917683450873)
  ·
    refine ⟨2096372090145688262588155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2795162786860917683450873 2096372090145688262588155)
    ·
      refine ⟨3144558135218532393882233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096372090145688262588155 3144558135218532393882233)
      ·
        refine ⟨2358418601413899295411675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3144558135218532393882233 2358418601413899295411675)
        ·
          refine ⟨3537627902120848943117513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358418601413899295411675 3537627902120848943117513)
          ·
            refine ⟨2653220926590636707338135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3537627902120848943117513 2653220926590636707338135)
            ·
              refine ⟨3979831389885955061007203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653220926590636707338135 3979831389885955061007203)
              ·
                refine ⟨5969747084828932591510805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979831389885955061007203 5969747084828932591510805)
                ·
                  refine ⟨279831894601356215227069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5969747084828932591510805 279831894601356215227069)
                  ·
                    refine ⟨104936960475508580710151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279831894601356215227069 104936960475508580710151)
                    ·
                      rfl

theorem cell22_306546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_306546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306546 prefixEnd_306546 := by exact prefixLift 306546
  have htrace : WordTrace (prefixWord ++ tailWord_306546) baseStart_306546 baseEnd_306546 := by
    simpa [prefixWord, tailWord_306546, baseEnd_306546] using wordTrace_append hprefix tailTrace_306546
  have hstable : (prefixWord ++ tailWord_306546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306546).length < 2 ^ (prefixWord ++ tailWord_306546).sum := by decide
  have hdescent : baseEnd_306546 < baseStart_306546 := by decide
  rcases family_descends (prefixWord ++ tailWord_306546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306580 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_306580 : Nat := 118140960795 + 306580 * 2 ^ 59
def prefixEnd_306580 : Nat := 4983230072969 + 3 ^ 40 * 306580 * 2
def baseEnd_306580 : Nat := 104948599370343825360047

theorem tailTrace_306580 : CollatzResearch.WordTrace tailWord_306580 prefixEnd_306580 104948599370343825360047 := by
  unfold tailWord_306580
  simp only [CollatzResearch.WordTrace]
  refine ⟨5590945614660247270270597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7454594152880329693694129 5590945614660247270270597)
  ·
    refine ⟨1048302302748796363175737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5590945614660247270270597 1048302302748796363175737)
    ·
      refine ⟨786226727061597272381803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1048302302748796363175737 786226727061597272381803)
      ·
        refine ⟨1179340090592395908572705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786226727061597272381803 1179340090592395908572705)
        ·
          refine ⟨884505067944296931429529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1179340090592395908572705 884505067944296931429529)
          ·
            refine ⟨663378800958222698572147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884505067944296931429529 663378800958222698572147)
            ·
              refine ⟨995068201437334047858221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663378800958222698572147 995068201437334047858221)
              ·
                refine ⟨373150575539000267946833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 995068201437334047858221 373150575539000267946833)
                ·
                  refine ⟨279862931654250200960125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373150575539000267946833 279862931654250200960125)
                  ·
                    refine ⟨104948599370343825360047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 279862931654250200960125 104948599370343825360047)
                    ·
                      rfl

theorem cell22_306580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_306580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306580 prefixEnd_306580 := by exact prefixLift 306580
  have htrace : WordTrace (prefixWord ++ tailWord_306580) baseStart_306580 baseEnd_306580 := by
    simpa [prefixWord, tailWord_306580, baseEnd_306580] using wordTrace_append hprefix tailTrace_306580
  have hstable : (prefixWord ++ tailWord_306580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306580).length < 2 ^ (prefixWord ++ tailWord_306580).sum := by decide
  have hdescent : baseEnd_306580 < baseStart_306580 := by decide
  rcases family_descends (prefixWord ++ tailWord_306580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306604 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 9]
def baseStart_306604 : Nat := 118140960795 + 306604 * 2 ^ 59
def prefixEnd_306604 : Nat := 4983230072969 + 3 ^ 40 * 306604 * 2
def baseEnd_306604 : Nat := 34985605020271920919991

theorem tailTrace_306604 : CollatzResearch.WordTrace tailWord_306604 prefixEnd_306604 34985605020271920919991 := by
  unfold tailWord_306604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591383290616773319707433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7455177720822364426276577 5591383290616773319707433)
  ·
    refine ⟨4193537467962579989780575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5591383290616773319707433 4193537467962579989780575)
    ·
      refine ⟨6290306201943869984670863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4193537467962579989780575 6290306201943869984670863)
      ·
        refine ⟨9435459302915804977006295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6290306201943869984670863 9435459302915804977006295)
        ·
          refine ⟨14153188954373707465509443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9435459302915804977006295 14153188954373707465509443)
          ·
            refine ⟨21229783431560561198264165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14153188954373707465509443 21229783431560561198264165)
            ·
              refine ⟨3980584393417605224674531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21229783431560561198264165 3980584393417605224674531)
              ·
                refine ⟨5970876590126407837011797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980584393417605224674531 5970876590126407837011797)
                ·
                  refine ⟨34985605020271920919991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5970876590126407837011797 34985605020271920919991)
                  ·
                    rfl

theorem cell22_306604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_306604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306604 prefixEnd_306604 := by exact prefixLift 306604
  have htrace : WordTrace (prefixWord ++ tailWord_306604) baseStart_306604 baseEnd_306604 := by
    simpa [prefixWord, tailWord_306604, baseEnd_306604] using wordTrace_append hprefix tailTrace_306604
  have hstable : (prefixWord ++ tailWord_306604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306604).length < 2 ^ (prefixWord ++ tailWord_306604).sum := by decide
  have hdescent : baseEnd_306604 < baseStart_306604 := by decide
  rcases family_descends (prefixWord ++ tailWord_306604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306636 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_306636 : Nat := 118140960795 + 306636 * 2 ^ 59
def prefixEnd_306636 : Nat := 4983230072969 + 3 ^ 40 * 306636 * 2
def baseEnd_306636 : Nat := 104967769314778345959875

theorem tailTrace_306636 : CollatzResearch.WordTrace tailWord_306636 prefixEnd_306636 104967769314778345959875 := by
  unfold tailWord_306636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591966858558808052289881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7455955811411744069719841 5591966858558808052289881)
  ·
    refine ⟨4193975143919106039217411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5591966858558808052289881 4193975143919106039217411)
    ·
      refine ⟨6290962715878659058826117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4193975143919106039217411 6290962715878659058826117)
      ·
        refine ⟨1179555509227248573529897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6290962715878659058826117 1179555509227248573529897)
        ·
          refine ⟨884666631920436430147423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1179555509227248573529897 884666631920436430147423)
          ·
            refine ⟨1326999947880654645221135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884666631920436430147423 1326999947880654645221135)
            ·
              refine ⟨1990499921820981967831703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326999947880654645221135 1990499921820981967831703)
              ·
                refine ⟨2985749882731472951747555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1990499921820981967831703 2985749882731472951747555)
                ·
                  refine ⟨4478624824097209427621333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985749882731472951747555 4478624824097209427621333)
                  ·
                    refine ⟨104967769314778345959875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4478624824097209427621333 104967769314778345959875)
                    ·
                      rfl

theorem cell22_306636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_306636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306636 prefixEnd_306636 := by exact prefixLift 306636
  have htrace : WordTrace (prefixWord ++ tailWord_306636) baseStart_306636 baseEnd_306636 := by
    simpa [prefixWord, tailWord_306636, baseEnd_306636] using wordTrace_append hprefix tailTrace_306636
  have hstable : (prefixWord ++ tailWord_306636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306636).length < 2 ^ (prefixWord ++ tailWord_306636).sum := by decide
  have hdescent : baseEnd_306636 < baseStart_306636 := by decide
  rcases family_descends (prefixWord ++ tailWord_306636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306696 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_306696 : Nat := 118140960795 + 306696 * 2 ^ 59
def prefixEnd_306696 : Nat := 4983230072969 + 3 ^ 40 * 306696 * 2
def baseEnd_306696 : Nat := 104988308540958189459691

theorem tailTrace_306696 : CollatzResearch.WordTrace tailWord_306696 prefixEnd_306696 104988308540958189459691 := by
  unfold tailWord_306696
  simp only [CollatzResearch.WordTrace]
  refine ⟨5593061048450123175881971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7457414731266830901175961 5593061048450123175881971)
  ·
    refine ⟨8389591572675184763822957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5593061048450123175881971 8389591572675184763822957)
    ·
      refine ⟨3146096839753194286433609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8389591572675184763822957 3146096839753194286433609)
      ·
        refine ⟨2359572629814895714825207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3146096839753194286433609 2359572629814895714825207)
        ·
          refine ⟨3539358944722343572237811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359572629814895714825207 3539358944722343572237811)
          ·
            refine ⟨5309038417083515358356717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539358944722343572237811 5309038417083515358356717)
            ·
              refine ⟨1990889406406318259383769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5309038417083515358356717 1990889406406318259383769)
              ·
                refine ⟨1493167054804738694537827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1990889406406318259383769 1493167054804738694537827)
                ·
                  refine ⟨2239750582207108041806741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1493167054804738694537827 2239750582207108041806741)
                  ·
                    refine ⟨104988308540958189459691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2239750582207108041806741 104988308540958189459691)
                    ·
                      rfl

theorem cell22_306696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_306696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306696 prefixEnd_306696 := by exact prefixLift 306696
  have htrace : WordTrace (prefixWord ++ tailWord_306696) baseStart_306696 baseEnd_306696 := by
    simpa [prefixWord, tailWord_306696, baseEnd_306696] using wordTrace_append hprefix tailTrace_306696
  have hstable : (prefixWord ++ tailWord_306696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306696).length < 2 ^ (prefixWord ++ tailWord_306696).sum := by decide
  have hdescent : baseEnd_306696 < baseStart_306696 := by decide
  rcases family_descends (prefixWord ++ tailWord_306696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306698 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_306698 : Nat := 118140960795 + 306698 * 2 ^ 59
def prefixEnd_306698 : Nat := 4983230072969 + 3 ^ 40 * 306698 * 2
def baseEnd_306698 : Nat := 104988993181830850909685

theorem tailTrace_306698 : CollatzResearch.WordTrace tailWord_306698 prefixEnd_306698 104988993181830850909685 := by
  unfold tailWord_306698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796548760723250173334187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7457463361928667128891165 2796548760723250173334187)
  ·
    refine ⟨4194823141084875260001281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2796548760723250173334187 4194823141084875260001281)
    ·
      refine ⟨3146117355813656445000961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4194823141084875260001281 3146117355813656445000961)
      ·
        refine ⟨2359588016860242333750721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3146117355813656445000961 2359588016860242333750721)
        ·
          refine ⟨1769691012645181750313041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2359588016860242333750721 1769691012645181750313041)
          ·
            refine ⟨1327268259483886312734781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1769691012645181750313041 1327268259483886312734781)
            ·
              refine ⟨497725597306457367275543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1327268259483886312734781 497725597306457367275543)
              ·
                refine ⟨746588395959686050913315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497725597306457367275543 746588395959686050913315)
                ·
                  refine ⟨1119882593939529076369973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746588395959686050913315 1119882593939529076369973)
                  ·
                    refine ⟨104988993181830850909685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1119882593939529076369973 104988993181830850909685)
                    ·
                      rfl

theorem cell22_306698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_306698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306698 prefixEnd_306698 := by exact prefixLift 306698
  have htrace : WordTrace (prefixWord ++ tailWord_306698) baseStart_306698 baseEnd_306698 := by
    simpa [prefixWord, tailWord_306698, baseEnd_306698] using wordTrace_append hprefix tailTrace_306698
  have hstable : (prefixWord ++ tailWord_306698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306698).length < 2 ^ (prefixWord ++ tailWord_306698).sum := by decide
  have hdescent : baseEnd_306698 < baseStart_306698 := by decide
  rcases family_descends (prefixWord ++ tailWord_306698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306749 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_306749 : Nat := 118140960795 + 306749 * 2 ^ 59
def prefixEnd_306749 : Nat := 4983230072969 + 3 ^ 40 * 306749 * 2
def baseEnd_306749 : Nat := 105006451524083717884529

theorem tailTrace_306749 : CollatzResearch.WordTrace tailWord_306749 prefixEnd_306749 105006451524083717884529 := by
  unfold tailWord_306749
  simp only [CollatzResearch.WordTrace]
  refine ⟨11188055165708236403443301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7458703443805490935628867 11188055165708236403443301)
  ·
    refine ⟨2097760343570294325645619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11188055165708236403443301 2097760343570294325645619)
    ·
      refine ⟨3146640515355441488468429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097760343570294325645619 3146640515355441488468429)
      ·
        refine ⟨1179990193258290558175661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3146640515355441488468429 1179990193258290558175661)
        ·
          refine ⟨442496322471858959315873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1179990193258290558175661 442496322471858959315873)
          ·
            refine ⟨331872241853894219486905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442496322471858959315873 331872241853894219486905)
            ·
              refine ⟨248904181390420664615179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331872241853894219486905 248904181390420664615179)
              ·
                refine ⟨373356272085630996922769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248904181390420664615179 373356272085630996922769)
                ·
                  refine ⟨280017204064223247692077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373356272085630996922769 280017204064223247692077)
                  ·
                    refine ⟨105006451524083717884529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280017204064223247692077 105006451524083717884529)
                    ·
                      rfl

theorem cell22_306749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_306749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306749 prefixEnd_306749 := by exact prefixLift 306749
  have htrace : WordTrace (prefixWord ++ tailWord_306749) baseStart_306749 baseEnd_306749 := by
    simpa [prefixWord, tailWord_306749, baseEnd_306749] using wordTrace_append hprefix tailTrace_306749
  have hstable : (prefixWord ++ tailWord_306749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306749).length < 2 ^ (prefixWord ++ tailWord_306749).sum := by decide
  have hdescent : baseEnd_306749 < baseStart_306749 := by decide
  rcases family_descends (prefixWord ++ tailWord_306749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306794 : List Nat := [3, 1, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_306794 : Nat := 118140960795 + 306794 * 2 ^ 59
def prefixEnd_306794 : Nat := 4983230072969 + 3 ^ 40 * 306794 * 2
def baseEnd_306794 : Nat := 105021855943718600509391

theorem tailTrace_306794 : CollatzResearch.WordTrace tailWord_306794 prefixEnd_306794 105021855943718600509391 := by
  unfold tailWord_306794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797424112636302272207859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7459797633696806059220957 2797424112636302272207859)
  ·
    refine ⟨4196136168954453408311789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2797424112636302272207859 4196136168954453408311789)
    ·
      refine ⟨1573551063357920028116921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4196136168954453408311789 1573551063357920028116921)
      ·
        refine ⟨1180163297518440021087691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1573551063357920028116921 1180163297518440021087691)
        ·
          refine ⟨1770244946277660031631537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180163297518440021087691 1770244946277660031631537)
          ·
            refine ⟨1327683709708245023723653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1770244946277660031631537 1327683709708245023723653)
            ·
              refine ⟨248940695570295941948185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1327683709708245023723653 248940695570295941948185)
              ·
                refine ⟨186705521677721956461139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248940695570295941948185 186705521677721956461139)
                ·
                  refine ⟨280058282516582934691709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186705521677721956461139 280058282516582934691709)
                  ·
                    refine ⟨105021855943718600509391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280058282516582934691709 105021855943718600509391)
                    ·
                      rfl

theorem cell22_306794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_306794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306794 prefixEnd_306794 := by exact prefixLift 306794
  have htrace : WordTrace (prefixWord ++ tailWord_306794) baseStart_306794 baseEnd_306794 := by
    simpa [prefixWord, tailWord_306794, baseEnd_306794] using wordTrace_append hprefix tailTrace_306794
  have hstable : (prefixWord ++ tailWord_306794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306794).length < 2 ^ (prefixWord ++ tailWord_306794).sum := by decide
  have hdescent : baseEnd_306794 < baseStart_306794 := by decide
  rcases family_descends (prefixWord ++ tailWord_306794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306801 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 10]
def baseStart_306801 : Nat := 118140960795 + 306801 * 2 ^ 59
def prefixEnd_306801 : Nat := 4983230072969 + 3 ^ 40 * 306801 * 2
def baseEnd_306801 : Nat := 35008084062257638528123

theorem tailTrace_306801 : CollatzResearch.WordTrace tailWord_306801 prefixEnd_306801 35008084062257638528123 := by
  unfold tailWord_306801
  simp only [CollatzResearch.WordTrace]
  refine ⟨11189951761519849284336257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7459967841013232856224171 11189951761519849284336257)
  ·
    refine ⟨8392463821139886963252193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11189951761519849284336257 8392463821139886963252193)
    ·
      refine ⟨6294347865854915222439145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8392463821139886963252193 6294347865854915222439145)
      ·
        refine ⟨4720760899391186416829359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6294347865854915222439145 4720760899391186416829359)
        ·
          refine ⟨7081141349086779625244039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720760899391186416829359 7081141349086779625244039)
          ·
            refine ⟨10621712023630169437866059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7081141349086779625244039 10621712023630169437866059)
            ·
              refine ⟨15932568035445254156799089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10621712023630169437866059 15932568035445254156799089)
              ·
                refine ⟨11949426026583940617599317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15932568035445254156799089 11949426026583940617599317)
                ·
                  refine ⟨35008084062257638528123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 11949426026583940617599317 35008084062257638528123)
                  ·
                    rfl

theorem cell22_306801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_306801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306801 prefixEnd_306801 := by exact prefixLift 306801
  have htrace : WordTrace (prefixWord ++ tailWord_306801) baseStart_306801 baseEnd_306801 := by
    simpa [prefixWord, tailWord_306801, baseEnd_306801] using wordTrace_append hprefix tailTrace_306801
  have hstable : (prefixWord ++ tailWord_306801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306801).length < 2 ^ (prefixWord ++ tailWord_306801).sum := by decide
  have hdescent : baseEnd_306801 < baseStart_306801 := by decide
  rcases family_descends (prefixWord ++ tailWord_306801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306805 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 2, 5]
def baseStart_306805 : Nat := 118140960795 + 306805 * 2 ^ 59
def prefixEnd_306805 : Nat := 4983230072969 + 3 ^ 40 * 306805 * 2
def baseEnd_306805 : Nat := 105025621468518238484357

theorem tailTrace_306805 : CollatzResearch.WordTrace tailWord_306805 prefixEnd_306805 105025621468518238484357 := by
  unfold tailWord_306805
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190097653505357967481869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7460065102336905311654579 11190097653505357967481869)
  ·
    refine ⟨4196286620064509237805701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11190097653505357967481869 4196286620064509237805701)
    ·
      refine ⟨786803741262095482088569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4196286620064509237805701 786803741262095482088569)
      ·
        refine ⟨590102805946571611566427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 786803741262095482088569 590102805946571611566427)
        ·
          refine ⟨885154208919857417349641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590102805946571611566427 885154208919857417349641)
          ·
            refine ⟨663865656689893063012231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885154208919857417349641 663865656689893063012231)
            ·
              refine ⟨995798485034839594518347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663865656689893063012231 995798485034839594518347)
              ·
                refine ⟨1493697727552259391777521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995798485034839594518347 1493697727552259391777521)
                ·
                  refine ⟨1120273295664194543833141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1493697727552259391777521 1120273295664194543833141)
                  ·
                    refine ⟨105025621468518238484357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1120273295664194543833141 105025621468518238484357)
                    ·
                      rfl

theorem cell22_306805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_306805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306805 prefixEnd_306805 := by exact prefixLift 306805
  have htrace : WordTrace (prefixWord ++ tailWord_306805) baseStart_306805 baseEnd_306805 := by
    simpa [prefixWord, tailWord_306805, baseEnd_306805] using wordTrace_append hprefix tailTrace_306805
  have hstable : (prefixWord ++ tailWord_306805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306805).length < 2 ^ (prefixWord ++ tailWord_306805).sum := by decide
  have hdescent : baseEnd_306805 < baseStart_306805 := by decide
  rcases family_descends (prefixWord ++ tailWord_306805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306867 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 2, 3]
def baseStart_306867 : Nat := 118140960795 + 306867 * 2 ^ 59
def prefixEnd_306867 : Nat := 4983230072969 + 3 ^ 40 * 306867 * 2
def baseEnd_306867 : Nat := 105046845335570743434167

theorem tailTrace_306867 : CollatzResearch.WordTrace tailWord_306867 prefixEnd_306867 105046845335570743434167 := by
  unfold tailWord_306867
  simp only [CollatzResearch.WordTrace]
  refine ⟨11192358979280742556238855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7461572652853828370825903 11192358979280742556238855)
  ·
    refine ⟨16788538468921113834358283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11192358979280742556238855 16788538468921113834358283)
    ·
      refine ⟨25182807703381670751537425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16788538468921113834358283 25182807703381670751537425)
      ·
        refine ⟨18887105777536253063653069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25182807703381670751537425 18887105777536253063653069)
        ·
          refine ⟨7082664666576094898869901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18887105777536253063653069 7082664666576094898869901)
          ·
            refine ⟨2655999249966035587076213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7082664666576094898869901 2655999249966035587076213)
            ·
              refine ⟨248999929684315836288395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2655999249966035587076213 248999929684315836288395)
              ·
                refine ⟨373499894526473754432593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248999929684315836288395 373499894526473754432593)
                ·
                  refine ⟨280124920894855315824445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 373499894526473754432593 280124920894855315824445)
                  ·
                    refine ⟨105046845335570743434167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280124920894855315824445 105046845335570743434167)
                    ·
                      rfl

theorem cell22_306867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 3].length) (baseStart_306867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306867 prefixEnd_306867 := by exact prefixLift 306867
  have htrace : WordTrace (prefixWord ++ tailWord_306867) baseStart_306867 baseEnd_306867 := by
    simpa [prefixWord, tailWord_306867, baseEnd_306867] using wordTrace_append hprefix tailTrace_306867
  have hstable : (prefixWord ++ tailWord_306867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306867).length < 2 ^ (prefixWord ++ tailWord_306867).sum := by decide
  have hdescent : baseEnd_306867 < baseStart_306867 := by decide
  rcases family_descends (prefixWord ++ tailWord_306867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306886 : List Nat := [6, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_306886 : Nat := 118140960795 + 306886 * 2 ^ 59
def prefixEnd_306886 : Nat := 4983230072969 + 3 ^ 40 * 306886 * 2
def baseEnd_306886 : Nat := 35017783141287009069703

theorem tailTrace_306886 : CollatzResearch.WordTrace tailWord_306886 prefixEnd_306886 35017783141287009069703 := by
  unfold tailWord_306886
  simp only [CollatzResearch.WordTrace]
  refine ⟨349782873944122150036891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7462034644141272534120341 349782873944122150036891)
  ·
    refine ⟨524674310916183225055337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349782873944122150036891 524674310916183225055337)
    ·
      refine ⟨393505733187137418791503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524674310916183225055337 393505733187137418791503)
      ·
        refine ⟨590258599780706128187255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393505733187137418791503 590258599780706128187255)
        ·
          refine ⟨885387899671059192280883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590258599780706128187255 885387899671059192280883)
          ·
            refine ⟨1328081849506588788421325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885387899671059192280883 1328081849506588788421325)
            ·
              refine ⟨498030693564970795657997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1328081849506588788421325 498030693564970795657997)
              ·
                refine ⟨186761510086864048371749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 498030693564970795657997 186761510086864048371749)
                ·
                  refine ⟨35017783141287009069703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186761510086864048371749 35017783141287009069703)
                  ·
                    rfl

theorem cell22_306886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_306886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306886 prefixEnd_306886 := by exact prefixLift 306886
  have htrace : WordTrace (prefixWord ++ tailWord_306886) baseStart_306886 baseEnd_306886 := by
    simpa [prefixWord, tailWord_306886, baseEnd_306886] using wordTrace_append hprefix tailTrace_306886
  have hstable : (prefixWord ++ tailWord_306886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306886).length < 2 ^ (prefixWord ++ tailWord_306886).sum := by decide
  have hdescent : baseEnd_306886 < baseStart_306886 := by decide
  rcases family_descends (prefixWord ++ tailWord_306886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306912 : List Nat := [2, 1, 1, 3, 1, 2, 2, 6, 1, 3]
def baseStart_306912 : Nat := 118140960795 + 306912 * 2 ^ 59
def prefixEnd_306912 : Nat := 4983230072969 + 3 ^ 40 * 306912 * 2
def baseEnd_306912 : Nat := 105062249755205626059029

theorem tailTrace_306912 : CollatzResearch.WordTrace tailWord_306912 prefixEnd_306912 105062249755205626059029 := by
  unfold tailWord_306912
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597000132058857620813495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7462666842745143494417993 5597000132058857620813495)
  ·
    refine ⟨8395500198088286431220243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5597000132058857620813495 8395500198088286431220243)
    ·
      refine ⟨12593250297132429646830365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8395500198088286431220243 12593250297132429646830365)
      ·
        refine ⟨4722468861424661117561387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12593250297132429646830365 4722468861424661117561387)
        ·
          refine ⟨7083703292136991676342081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4722468861424661117561387 7083703292136991676342081)
          ·
            refine ⟨5312777469102743757256561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7083703292136991676342081 5312777469102743757256561)
            ·
              refine ⟨3984583101827057817942421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312777469102743757256561 3984583101827057817942421)
              ·
                refine ⟨186777332898143335216051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3984583101827057817942421 186777332898143335216051)
                ·
                  refine ⟨280165999347215002824077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186777332898143335216051 280165999347215002824077)
                  ·
                    refine ⟨105062249755205626059029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280165999347215002824077 105062249755205626059029)
                    ·
                      rfl

theorem cell22_306912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 1, 3].length) (baseStart_306912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306912 prefixEnd_306912 := by exact prefixLift 306912
  have htrace : WordTrace (prefixWord ++ tailWord_306912) baseStart_306912 baseEnd_306912 := by
    simpa [prefixWord, tailWord_306912, baseEnd_306912] using wordTrace_append hprefix tailTrace_306912
  have hstable : (prefixWord ++ tailWord_306912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306912).length < 2 ^ (prefixWord ++ tailWord_306912).sum := by decide
  have hdescent : baseEnd_306912 < baseStart_306912 := by decide
  rcases family_descends (prefixWord ++ tailWord_306912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306923 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 2, 5]
def baseStart_306923 : Nat := 118140960795 + 306923 * 2 ^ 59
def prefixEnd_306923 : Nat := 4983230072969 + 3 ^ 40 * 306923 * 2
def baseEnd_306923 : Nat := 105066015280005264033995

theorem tailTrace_306923 : CollatzResearch.WordTrace tailWord_306923 prefixEnd_306923 105066015280005264033995 := by
  unfold tailWord_306923
  simp only [CollatzResearch.WordTrace]
  refine ⟨11194401467077864120277423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7462934311385242746851615 11194401467077864120277423)
  ·
    refine ⟨16791602200616796180416135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11194401467077864120277423 16791602200616796180416135)
    ·
      refine ⟨25187403300925194270624203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16791602200616796180416135 25187403300925194270624203)
      ·
        refine ⟨37781104951387791405936305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25187403300925194270624203 37781104951387791405936305)
        ·
          refine ⟨28335828713540843554452229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37781104951387791405936305 28335828713540843554452229)
          ·
            refine ⟨5312967883788908166459793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28335828713540843554452229 5312967883788908166459793)
            ·
              refine ⟨3984725912841681124844845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5312967883788908166459793 3984725912841681124844845)
              ·
                refine ⟨1494272217315630421816817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3984725912841681124844845 1494272217315630421816817)
                ·
                  refine ⟨1120704162986722816362613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1494272217315630421816817 1120704162986722816362613)
                  ·
                    refine ⟨105066015280005264033995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1120704162986722816362613 105066015280005264033995)
                    ·
                      rfl

theorem cell22_306923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 5].length) (baseStart_306923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306923 prefixEnd_306923 := by exact prefixLift 306923
  have htrace : WordTrace (prefixWord ++ tailWord_306923) baseStart_306923 baseEnd_306923 := by
    simpa [prefixWord, tailWord_306923, baseEnd_306923] using wordTrace_append hprefix tailTrace_306923
  have hstable : (prefixWord ++ tailWord_306923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306923).length < 2 ^ (prefixWord ++ tailWord_306923).sum := by decide
  have hdescent : baseEnd_306923 < baseStart_306923 := by decide
  rcases family_descends (prefixWord ++ tailWord_306923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306955 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 1, 4]
def baseStart_306955 : Nat := 118140960795 + 306955 * 2 ^ 59
def prefixEnd_306955 : Nat := 4983230072969 + 3 ^ 40 * 306955 * 2
def baseEnd_306955 : Nat := 105076969533967847233897

theorem tailTrace_306955 : CollatzResearch.WordTrace tailWord_306955 prefixEnd_306955 105076969533967847233897 := by
  unfold tailWord_306955
  simp only [CollatzResearch.WordTrace]
  refine ⟨11195568602961933585442319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7463712401974622390294879 11195568602961933585442319)
  ·
    refine ⟨16793352904442900378163479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11195568602961933585442319 16793352904442900378163479)
    ·
      refine ⟨25190029356664350567245219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16793352904442900378163479 25190029356664350567245219)
      ·
        refine ⟨37785044034996525850867829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25190029356664350567245219 37785044034996525850867829)
        ·
          refine ⟨3542347878280924298518859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37785044034996525850867829 3542347878280924298518859)
          ·
            refine ⟨5313521817421386447778289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3542347878280924298518859 5313521817421386447778289)
            ·
              refine ⟨3985141363066039835833717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5313521817421386447778289 3985141363066039835833717)
              ·
                refine ⟨373607002787441234609411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3985141363066039835833717 373607002787441234609411)
                ·
                  refine ⟨560410504181161851914117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373607002787441234609411 560410504181161851914117)
                  ·
                    refine ⟨105076969533967847233897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 560410504181161851914117 105076969533967847233897)
                    ·
                      rfl

theorem cell22_306955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 4].length) (baseStart_306955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_306955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_306955 prefixEnd_306955 := by exact prefixLift 306955
  have htrace : WordTrace (prefixWord ++ tailWord_306955) baseStart_306955 baseEnd_306955 := by
    simpa [prefixWord, tailWord_306955, baseEnd_306955] using wordTrace_append hprefix tailTrace_306955
  have hstable : (prefixWord ++ tailWord_306955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306955).length < 2 ^ (prefixWord ++ tailWord_306955).sum := by decide
  have hdescent : baseEnd_306955 < baseStart_306955 := by decide
  rcases family_descends (prefixWord ++ tailWord_306955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307000 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_307000 : Nat := 118140960795 + 307000 * 2 ^ 59
def prefixEnd_307000 : Nat := 4983230072969 + 3 ^ 40 * 307000 * 2
def baseEnd_307000 : Nat := 105092373953602729858759

theorem tailTrace_307000 : CollatzResearch.WordTrace tailWord_307000 prefixEnd_307000 105092373953602729858759 := by
  unfold tailWord_307000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5598604943899453135415227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7464806591865937513886969 5598604943899453135415227)
  ·
    refine ⟨8397907415849179703122841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5598604943899453135415227 8397907415849179703122841)
    ·
      refine ⟨6298430561886884777342131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8397907415849179703122841 6298430561886884777342131)
      ·
        refine ⟨9447645842830327166013197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6298430561886884777342131 9447645842830327166013197)
        ·
          refine ⟨3542867191061372687254949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9447645842830327166013197 3542867191061372687254949)
          ·
            refine ⟨664287598324007378860303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3542867191061372687254949 664287598324007378860303)
            ·
              refine ⟨996431397486011068290455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664287598324007378860303 996431397486011068290455)
              ·
                refine ⟨1494647096229016602435683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996431397486011068290455 1494647096229016602435683)
                ·
                  refine ⟨2241970644343524903653525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1494647096229016602435683 2241970644343524903653525)
                  ·
                    refine ⟨105092373953602729858759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2241970644343524903653525 105092373953602729858759)
                    ·
                      rfl

theorem cell22_307000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_307000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307000 prefixEnd_307000 := by exact prefixLift 307000
  have htrace : WordTrace (prefixWord ++ tailWord_307000) baseStart_307000 baseEnd_307000 := by
    simpa [prefixWord, tailWord_307000, baseEnd_307000] using wordTrace_append hprefix tailTrace_307000
  have hstable : (prefixWord ++ tailWord_307000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307000).length < 2 ^ (prefixWord ++ tailWord_307000).sum := by decide
  have hdescent : baseEnd_307000 < baseStart_307000 := by decide
  rcases family_descends (prefixWord ++ tailWord_307000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307006 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_307006 : Nat := 118140960795 + 307006 * 2 ^ 59
def prefixEnd_307006 : Nat := 4983230072969 + 3 ^ 40 * 307006 * 2
def baseEnd_307006 : Nat := 105094427876220714208741

theorem tailTrace_307006 : CollatzResearch.WordTrace tailWord_307006 prefixEnd_307006 105094427876220714208741 := by
  unfold tailWord_307006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399678590722146161943609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7464952483851446197032581 1399678590722146161943609)
  ·
    refine ⟨1049758943041609621457707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1399678590722146161943609 1049758943041609621457707)
    ·
      refine ⟨1574638414562414432186561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049758943041609621457707 1574638414562414432186561)
      ·
        refine ⟨1180978810921810824139921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1574638414562414432186561 1180978810921810824139921)
        ·
          refine ⟨885734108191358118104941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1180978810921810824139921 885734108191358118104941)
          ·
            refine ⟨332150290571759294289353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 885734108191358118104941 332150290571759294289353)
            ·
              refine ⟨249112717928819470717015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332150290571759294289353 249112717928819470717015)
              ·
                refine ⟨373669076893229206075523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249112717928819470717015 373669076893229206075523)
                ·
                  refine ⟨560503615339843809113285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373669076893229206075523 560503615339843809113285)
                  ·
                    refine ⟨105094427876220714208741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 560503615339843809113285 105094427876220714208741)
                    ·
                      rfl

theorem cell22_307006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_307006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307006 prefixEnd_307006 := by exact prefixLift 307006
  have htrace : WordTrace (prefixWord ++ tailWord_307006) baseStart_307006 baseEnd_307006 := by
    simpa [prefixWord, tailWord_307006, baseEnd_307006] using wordTrace_append hprefix tailTrace_307006
  have hstable : (prefixWord ++ tailWord_307006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307006).length < 2 ^ (prefixWord ++ tailWord_307006).sum := by decide
  have hdescent : baseEnd_307006 < baseStart_307006 := by decide
  rcases family_descends (prefixWord ++ tailWord_307006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307036 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_307036 : Nat := 118140960795 + 307036 * 2 ^ 59
def prefixEnd_307036 : Nat := 4983230072969 + 3 ^ 40 * 307036 * 2
def baseEnd_307036 : Nat := 105104697489310635958649

theorem tailTrace_307036 : CollatzResearch.WordTrace tailWord_307036 prefixEnd_307036 105104697489310635958649 := by
  unfold tailWord_307036
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599261457834242209570481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7465681943778989612760641 5599261457834242209570481)
  ·
    refine ⟨4199446093375681657177861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5599261457834242209570481 4199446093375681657177861)
    ·
      refine ⟨787396142507940310720849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4199446093375681657177861 787396142507940310720849)
      ·
        refine ⟨590547106880955233040637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 787396142507940310720849 590547106880955233040637)
        ·
          refine ⟨221455165080358212390239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 590547106880955233040637 221455165080358212390239)
          ·
            refine ⟨332182747620537318585359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221455165080358212390239 332182747620537318585359)
            ·
              refine ⟨498274121430805977878039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332182747620537318585359 498274121430805977878039)
              ·
                refine ⟨747411182146208966817059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498274121430805977878039 747411182146208966817059)
                ·
                  refine ⟨1121116773219313450225589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747411182146208966817059 1121116773219313450225589)
                  ·
                    refine ⟨105104697489310635958649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1121116773219313450225589 105104697489310635958649)
                    ·
                      rfl

theorem cell22_307036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_307036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307036 prefixEnd_307036 := by exact prefixLift 307036
  have htrace : WordTrace (prefixWord ++ tailWord_307036) baseStart_307036 baseEnd_307036 := by
    simpa [prefixWord, tailWord_307036, baseEnd_307036] using wordTrace_append hprefix tailTrace_307036
  have hstable : (prefixWord ++ tailWord_307036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307036).length < 2 ^ (prefixWord ++ tailWord_307036).sum := by decide
  have hdescent : baseEnd_307036 < baseStart_307036 := by decide
  rcases family_descends (prefixWord ++ tailWord_307036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307047 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 3, 3]
def baseStart_307047 : Nat := 118140960795 + 307047 * 2 ^ 59
def prefixEnd_307047 : Nat := 4983230072969 + 3 ^ 40 * 307047 * 2
def baseEnd_307047 : Nat := 105108463014110273933615

theorem tailTrace_307047 : CollatzResearch.WordTrace tailWord_307047 prefixEnd_307047 105108463014110273933615 := by
  unfold tailWord_307047
  simp only [CollatzResearch.WordTrace]
  refine ⟨11198924118628633297791395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7465949412419088865194263 11198924118628633297791395)
  ·
    refine ⟨16798386177942949946687093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11198924118628633297791395 16798386177942949946687093)
    ·
      refine ⟨1574848704182151557501915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16798386177942949946687093 1574848704182151557501915)
      ·
        refine ⟨2362273056273227336252873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574848704182151557501915 2362273056273227336252873)
        ·
          refine ⟨1771704792204920502189655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2362273056273227336252873 1771704792204920502189655)
          ·
            refine ⟨2657557188307380753284483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771704792204920502189655 2657557188307380753284483)
            ·
              refine ⟨3986335782461071129926725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2657557188307380753284483 3986335782461071129926725)
              ·
                refine ⟨747437959211450836861261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3986335782461071129926725 747437959211450836861261)
                ·
                  refine ⟨280289234704294063822973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 747437959211450836861261 280289234704294063822973)
                  ·
                    refine ⟨105108463014110273933615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280289234704294063822973 105108463014110273933615)
                    ·
                      rfl

theorem cell22_307047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_307047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307047 prefixEnd_307047 := by exact prefixLift 307047
  have htrace : WordTrace (prefixWord ++ tailWord_307047) baseStart_307047 baseEnd_307047 := by
    simpa [prefixWord, tailWord_307047, baseEnd_307047] using wordTrace_append hprefix tailTrace_307047
  have hstable : (prefixWord ++ tailWord_307047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307047).length < 2 ^ (prefixWord ++ tailWord_307047).sum := by decide
  have hdescent : baseEnd_307047 < baseStart_307047 := by decide
  rcases family_descends (prefixWord ++ tailWord_307047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307081 : List Nat := [1, 2, 1, 1, 5, 1, 5, 2, 1, 3]
def baseStart_307081 : Nat := 118140960795 + 307081 * 2 ^ 59
def prefixEnd_307081 : Nat := 4983230072969 + 3 ^ 40 * 307081 * 2
def baseEnd_307081 : Nat := 105120101908945518583511

theorem tailTrace_307081 : CollatzResearch.WordTrace tailWord_307081 prefixEnd_307081 105120101908945518583511 := by
  unfold tailWord_307081
  simp only [CollatzResearch.WordTrace]
  refine ⟨11200164200505457104529097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7466776133670304736352731 11200164200505457104529097)
  ·
    refine ⟨8400123150379092828396823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11200164200505457104529097 8400123150379092828396823)
    ·
      refine ⟨12600184725568639242595235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8400123150379092828396823 12600184725568639242595235)
      ·
        refine ⟨18900277088352958863892853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12600184725568639242595235 18900277088352958863892853)
        ·
          refine ⟨1771900977033089893489955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18900277088352958863892853 1771900977033089893489955)
          ·
            refine ⟨2657851465549634840234933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771900977033089893489955 2657851465549634840234933)
            ·
              refine ⟨249173574895278266272025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2657851465549634840234933 249173574895278266272025)
              ·
                refine ⟨186880181171458699704019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249173574895278266272025 186880181171458699704019)
                ·
                  refine ⟨280320271757188049556029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186880181171458699704019 280320271757188049556029)
                  ·
                    refine ⟨105120101908945518583511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280320271757188049556029 105120101908945518583511)
                    ·
                      rfl

theorem cell22_307081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 3].length) (baseStart_307081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307081 prefixEnd_307081 := by exact prefixLift 307081
  have htrace : WordTrace (prefixWord ++ tailWord_307081) baseStart_307081 baseEnd_307081 := by
    simpa [prefixWord, tailWord_307081, baseEnd_307081] using wordTrace_append hprefix tailTrace_307081
  have hstable : (prefixWord ++ tailWord_307081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307081).length < 2 ^ (prefixWord ++ tailWord_307081).sum := by decide
  have hdescent : baseEnd_307081 < baseStart_307081 := by decide
  rcases family_descends (prefixWord ++ tailWord_307081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307132 : List Nat := [2, 2, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_307132 : Nat := 118140960795 + 307132 * 2 ^ 59
def prefixEnd_307132 : Nat := 4983230072969 + 3 ^ 40 * 307132 * 2
def baseEnd_307132 : Nat := 105137560251198385558355

theorem tailTrace_307132 : CollatzResearch.WordTrace tailWord_307132 prefixEnd_307132 105137560251198385558355 := by
  unfold tailWord_307132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5601012161660346407317825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7468016215547128543090433 5601012161660346407317825)
  ·
    refine ⟨4200759121245259805488369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5601012161660346407317825 4200759121245259805488369)
    ·
      refine ⟨3150569340933944854116277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4200759121245259805488369 3150569340933944854116277)
      ·
        refine ⟨295365875712557330073401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3150569340933944854116277 295365875712557330073401)
        ·
          refine ⟨221524406784417997555051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295365875712557330073401 221524406784417997555051)
          ·
            refine ⟨332286610176626996332577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221524406784417997555051 332286610176626996332577)
            ·
              refine ⟨249214957632470247249433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332286610176626996332577 249214957632470247249433)
              ·
                refine ⟨186911218224352685437075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249214957632470247249433 186911218224352685437075)
                ·
                  refine ⟨280366827336529028155613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186911218224352685437075 280366827336529028155613)
                  ·
                    refine ⟨105137560251198385558355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280366827336529028155613 105137560251198385558355)
                    ·
                      rfl

theorem cell22_307132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_307132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307132 prefixEnd_307132 := by exact prefixLift 307132
  have htrace : WordTrace (prefixWord ++ tailWord_307132) baseStart_307132 baseEnd_307132 := by
    simpa [prefixWord, tailWord_307132, baseEnd_307132] using wordTrace_append hprefix tailTrace_307132
  have hstable : (prefixWord ++ tailWord_307132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307132).length < 2 ^ (prefixWord ++ tailWord_307132).sum := by decide
  have hdescent : baseEnd_307132 < baseStart_307132 := by decide
  rcases family_descends (prefixWord ++ tailWord_307132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307287 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 1, 6]
def baseStart_307287 : Nat := 118140960795 + 307287 * 2 ^ 59
def prefixEnd_307287 : Nat := 4983230072969 + 3 ^ 40 * 307287 * 2
def baseEnd_307287 : Nat := 105190619918829647932879

theorem tailTrace_307287 : CollatzResearch.WordTrace tailWord_307287 prefixEnd_307287 105190619918829647932879 := by
  unfold tailWord_307287
  simp only [CollatzResearch.WordTrace]
  refine ⟨11207677637759154286528115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7471785091839436191018743 11207677637759154286528115)
  ·
    refine ⟨16811516456638731429792173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11207677637759154286528115 16811516456638731429792173)
    ·
      refine ⟨6304318671239524286172065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16811516456638731429792173 6304318671239524286172065)
      ·
        refine ⟨4728239003429643214629049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6304318671239524286172065 4728239003429643214629049)
        ·
          refine ⟨3546179252572232410971787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4728239003429643214629049 3546179252572232410971787)
          ·
            refine ⟨5319268878858348616457681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546179252572232410971787 5319268878858348616457681)
            ·
              refine ⟨3989451659143761462343261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5319268878858348616457681 3989451659143761462343261)
              ·
                refine ⟨1496044372178910548378723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3989451659143761462343261 1496044372178910548378723)
                ·
                  refine ⟨2244066558268365822568085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1496044372178910548378723 2244066558268365822568085)
                  ·
                    refine ⟨105190619918829647932879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2244066558268365822568085 105190619918829647932879)
                    ·
                      rfl

theorem cell22_307287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_307287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307287 prefixEnd_307287 := by exact prefixLift 307287
  have htrace : WordTrace (prefixWord ++ tailWord_307287) baseStart_307287 baseEnd_307287 := by
    simpa [prefixWord, tailWord_307287, baseEnd_307287] using wordTrace_append hprefix tailTrace_307287
  have hstable : (prefixWord ++ tailWord_307287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307287).length < 2 ^ (prefixWord ++ tailWord_307287).sum := by decide
  have hdescent : baseEnd_307287 < baseStart_307287 := by decide
  rcases family_descends (prefixWord ++ tailWord_307287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307308 : List Nat := [2, 2, 1, 1, 3, 5, 2, 2, 4]
def baseStart_307308 : Nat := 118140960795 + 307308 * 2 ^ 59
def prefixEnd_307308 : Nat := 4983230072969 + 3 ^ 40 * 307308 * 2
def baseEnd_307308 : Nat := 35065936215997531052605

theorem tailTrace_307308 : CollatzResearch.WordTrace tailWord_307308 prefixEnd_307308 35065936215997531052605 := by
  unfold tailWord_307308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604221785341537436521289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7472295713788716582028385 5604221785341537436521289)
  ·
    refine ⟨4203166339006153077390967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5604221785341537436521289 4203166339006153077390967)
    ·
      refine ⟨6304749508509229616086451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4203166339006153077390967 6304749508509229616086451)
      ·
        refine ⟨9457124262763844424129677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304749508509229616086451 9457124262763844424129677)
        ·
          refine ⟨3546421598536441659048629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9457124262763844424129677 3546421598536441659048629)
          ·
            refine ⟨332477024862791405535809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3546421598536441659048629 332477024862791405535809)
            ·
              refine ⟨249357768647093554151857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332477024862791405535809 249357768647093554151857)
              ·
                refine ⟨187018326485320165613893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249357768647093554151857 187018326485320165613893)
                ·
                  refine ⟨35065936215997531052605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187018326485320165613893 35065936215997531052605)
                  ·
                    rfl

theorem cell22_307308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_307308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307308 prefixEnd_307308 := by exact prefixLift 307308
  have htrace : WordTrace (prefixWord ++ tailWord_307308) baseStart_307308 baseEnd_307308 := by
    simpa [prefixWord, tailWord_307308, baseEnd_307308] using wordTrace_append hprefix tailTrace_307308
  have hstable : (prefixWord ++ tailWord_307308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307308).length < 2 ^ (prefixWord ++ tailWord_307308).sum := by decide
  have hdescent : baseEnd_307308 < baseStart_307308 := by decide
  rcases family_descends (prefixWord ++ tailWord_307308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307319 : List Nat := [1, 1, 3, 1, 1, 7, 1, 7]
def baseStart_307319 : Nat := 118140960795 + 307319 * 2 ^ 59
def prefixEnd_307319 : Nat := 4983230072969 + 3 ^ 40 * 307319 * 2
def baseEnd_307319 : Nat := 11689063796976914570309

theorem tailTrace_307319 : CollatzResearch.WordTrace tailWord_307319 prefixEnd_307319 11689063796976914570309 := by
  unfold tailWord_307319
  simp only [CollatzResearch.WordTrace]
  refine ⟨11208844773643223751693011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7472563182428815834462007 11208844773643223751693011)
  ·
    refine ⟨16813267160464835627539517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11208844773643223751693011 16813267160464835627539517)
    ·
      refine ⟨6304975185174313360327319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16813267160464835627539517 6304975185174313360327319)
      ·
        refine ⟨9457462777761470040490979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6304975185174313360327319 9457462777761470040490979)
        ·
          refine ⟨14186194166642205060736469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9457462777761470040490979 14186194166642205060736469)
          ·
            refine ⟨332488925780676681111011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14186194166642205060736469 332488925780676681111011)
            ·
              refine ⟨498733388671015021666517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332488925780676681111011 498733388671015021666517)
              ·
                refine ⟨11689063796976914570309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 498733388671015021666517 11689063796976914570309)
                ·
                  rfl

theorem cell22_307319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 7].length) (baseStart_307319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307319 prefixEnd_307319 := by exact prefixLift 307319
  have htrace : WordTrace (prefixWord ++ tailWord_307319) baseStart_307319 baseEnd_307319 := by
    simpa [prefixWord, tailWord_307319, baseEnd_307319] using wordTrace_append hprefix tailTrace_307319
  have hstable : (prefixWord ++ tailWord_307319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307319).length < 2 ^ (prefixWord ++ tailWord_307319).sum := by decide
  have hdescent : baseEnd_307319 < baseStart_307319 := by decide
  rcases family_descends (prefixWord ++ tailWord_307319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307336 : List Nat := [2, 1, 3, 4, 1, 2, 3, 6]
def baseStart_307336 : Nat := 118140960795 + 307336 * 2 ^ 59
def prefixEnd_307336 : Nat := 4983230072969 + 3 ^ 40 * 307336 * 2
def baseEnd_307336 : Nat := 11689710402245539273081

theorem tailTrace_307336 : CollatzResearch.WordTrace tailWord_307336 prefixEnd_307336 11689710402245539273081 := by
  unfold tailWord_307336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604732407290817827530931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7472976543054423770041241 5604732407290817827530931)
  ·
    refine ⟨8407098610936226741296397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5604732407290817827530931 8407098610936226741296397)
    ·
      refine ⟨3152661979101085027986149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8407098610936226741296397 3152661979101085027986149)
      ·
        refine ⟨591124121081453442747403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3152661979101085027986149 591124121081453442747403)
        ·
          refine ⟨886686181622180164121105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591124121081453442747403 886686181622180164121105)
          ·
            refine ⟨665014636216635123090829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886686181622180164121105 665014636216635123090829)
            ·
              refine ⟨249380488581238171159061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665014636216635123090829 249380488581238171159061)
              ·
                refine ⟨11689710402245539273081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 249380488581238171159061 11689710402245539273081)
                ·
                  rfl

theorem cell22_307336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 6].length) (baseStart_307336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307336 prefixEnd_307336 := by exact prefixLift 307336
  have htrace : WordTrace (prefixWord ++ tailWord_307336) baseStart_307336 baseEnd_307336 := by
    simpa [prefixWord, tailWord_307336, baseEnd_307336] using wordTrace_append hprefix tailTrace_307336
  have hstable : (prefixWord ++ tailWord_307336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307336).length < 2 ^ (prefixWord ++ tailWord_307336).sum := by decide
  have hdescent : baseEnd_307336 < baseStart_307336 := by decide
  rcases family_descends (prefixWord ++ tailWord_307336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307347 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 7]
def baseStart_307347 : Nat := 118140960795 + 307347 * 2 ^ 59
def prefixEnd_307347 : Nat := 4983230072969 + 3 ^ 40 * 307347 * 2
def baseEnd_307347 : Nat := 35070386381669830477565

theorem tailTrace_307347 : CollatzResearch.WordTrace tailWord_307347 prefixEnd_307347 35070386381669830477565 := by
  unfold tailWord_307347
  simp only [CollatzResearch.WordTrace]
  refine ⟨11209866017541784533712295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7473244011694523022474863 11209866017541784533712295)
  ·
    refine ⟨16814799026312676800568443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11209866017541784533712295 16814799026312676800568443)
    ·
      refine ⟨25222198539469015200852665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16814799026312676800568443 25222198539469015200852665)
      ·
        refine ⟨18916648904601761400639499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25222198539469015200852665 18916648904601761400639499)
        ·
          refine ⟨28374973356902642100959249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18916648904601761400639499 28374973356902642100959249)
          ·
            refine ⟨21281230017676981575719437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28374973356902642100959249 21281230017676981575719437)
            ·
              refine ⟨7980461256628868090894789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21281230017676981575719437 7980461256628868090894789)
              ·
                refine ⟨1496336485617912767042773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7980461256628868090894789 1496336485617912767042773)
                ·
                  refine ⟨35070386381669830477565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1496336485617912767042773 35070386381669830477565)
                  ·
                    rfl

theorem cell22_307347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 7].length) (baseStart_307347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307347 prefixEnd_307347 := by exact prefixLift 307347
  have htrace : WordTrace (prefixWord ++ tailWord_307347) baseStart_307347 baseEnd_307347 := by
    simpa [prefixWord, tailWord_307347, baseEnd_307347] using wordTrace_append hprefix tailTrace_307347
  have hstable : (prefixWord ++ tailWord_307347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307347).length < 2 ^ (prefixWord ++ tailWord_307347).sum := by decide
  have hdescent : baseEnd_307347 < baseStart_307347 := by decide
  rcases family_descends (prefixWord ++ tailWord_307347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307458 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_307458 : Nat := 118140960795 + 307458 * 2 ^ 59
def prefixEnd_307458 : Nat := 4983230072969 + 3 ^ 40 * 307458 * 2
def baseEnd_307458 : Nat := 105249156713442201907355

theorem tailTrace_307458 : CollatzResearch.WordTrace tailWord_307458 prefixEnd_307458 105249156713442201907355 := by
  unfold tailWord_307458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803478630034912622750757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7475943013426433660668685 2803478630034912622750757)
  ·
    refine ⟨525652243131546116765767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2803478630034912622750757 525652243131546116765767)
    ·
      refine ⟨788478364697319175148651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525652243131546116765767 788478364697319175148651)
      ·
        refine ⟨1182717547045978762722977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788478364697319175148651 1182717547045978762722977)
        ·
          refine ⟨887038160284484072042233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1182717547045978762722977 887038160284484072042233)
          ·
            refine ⟨665278620213363054031675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887038160284484072042233 665278620213363054031675)
            ·
              refine ⟨997917930320044581047513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665278620213363054031675 997917930320044581047513)
              ·
                refine ⟨748438447740033435785635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 997917930320044581047513 748438447740033435785635)
                ·
                  refine ⟨1122657671610050153678453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 748438447740033435785635 1122657671610050153678453)
                  ·
                    refine ⟨105249156713442201907355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1122657671610050153678453 105249156713442201907355)
                    ·
                      rfl

theorem cell22_307458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_307458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307458 prefixEnd_307458 := by exact prefixLift 307458
  have htrace : WordTrace (prefixWord ++ tailWord_307458) baseStart_307458 baseEnd_307458 := by
    simpa [prefixWord, tailWord_307458, baseEnd_307458] using wordTrace_append hprefix tailTrace_307458
  have hstable : (prefixWord ++ tailWord_307458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307458).length < 2 ^ (prefixWord ++ tailWord_307458).sum := by decide
  have hdescent : baseEnd_307458 < baseStart_307458 := by decide
  rcases family_descends (prefixWord ++ tailWord_307458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307593 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 4, 3]
def baseStart_307593 : Nat := 118140960795 + 307593 * 2 ^ 59
def prefixEnd_307593 : Nat := 4983230072969 + 3 ^ 40 * 307593 * 2
def baseEnd_307593 : Nat := 105295369972346849781941

theorem tailTrace_307593 : CollatzResearch.WordTrace tailWord_307593 prefixEnd_307593 105295369972346849781941 := by
  unfold tailWord_307593
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218838374650568547167433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7479225583100379031444955 11218838374650568547167433)
  ·
    refine ⟨8414128780987926410375575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11218838374650568547167433 8414128780987926410375575)
    ·
      refine ⟨12621193171481889615563363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8414128780987926410375575 12621193171481889615563363)
      ·
        refine ⟨18931789757222834423345045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12621193171481889615563363 18931789757222834423345045)
        ·
          refine ⟨887427644869820363594299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18931789757222834423345045 887427644869820363594299)
          ·
            refine ⟨1331141467304730545391449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887427644869820363594299 1331141467304730545391449)
            ·
              refine ⟨998356100478547909043587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1331141467304730545391449 998356100478547909043587)
              ·
                refine ⟨1497534150717821863565381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998356100478547909043587 1497534150717821863565381)
                ·
                  refine ⟨280787653259591599418509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1497534150717821863565381 280787653259591599418509)
                  ·
                    refine ⟨105295369972346849781941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280787653259591599418509 105295369972346849781941)
                    ·
                      rfl

theorem cell22_307593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 4, 3].length) (baseStart_307593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307593 prefixEnd_307593 := by exact prefixLift 307593
  have htrace : WordTrace (prefixWord ++ tailWord_307593) baseStart_307593 baseEnd_307593 := by
    simpa [prefixWord, tailWord_307593, baseEnd_307593] using wordTrace_append hprefix tailTrace_307593
  have hstable : (prefixWord ++ tailWord_307593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307593).length < 2 ^ (prefixWord ++ tailWord_307593).sum := by decide
  have hdescent : baseEnd_307593 < baseStart_307593 := by decide
  rcases family_descends (prefixWord ++ tailWord_307593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307595 : List Nat := [1, 1, 1, 1, 4, 5, 3, 2, 4]
def baseStart_307595 : Nat := 118140960795 + 307595 * 2 ^ 59
def prefixEnd_307595 : Nat := 4983230072969 + 3 ^ 40 * 307595 * 2
def baseEnd_307595 : Nat := 35098684871073170410645

theorem tailTrace_307595 : CollatzResearch.WordTrace tailWord_307595 prefixEnd_307595 35098684871073170410645 := by
  unfold tailWord_307595
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218911320643322888740239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7479274213762215259160159 11218911320643322888740239)
  ·
    refine ⟨16828366980964984333110359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11218911320643322888740239 16828366980964984333110359)
    ·
      refine ⟨25242550471447476499665539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16828366980964984333110359 25242550471447476499665539)
      ·
        refine ⟨37863825707171214749498309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25242550471447476499665539 37863825707171214749498309)
        ·
          refine ⟨7099467320094602765530933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37863825707171214749498309 7099467320094602765530933)
          ·
            refine ⟨665575061258869009268525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7099467320094602765530933 665575061258869009268525)
            ·
              refine ⟨249590647972075878475697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665575061258869009268525 249590647972075878475697)
              ·
                refine ⟨187192985979056908856773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249590647972075878475697 187192985979056908856773)
                ·
                  refine ⟨35098684871073170410645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187192985979056908856773 35098684871073170410645)
                  ·
                    rfl

theorem cell22_307595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 4].length) (baseStart_307595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307595 prefixEnd_307595 := by exact prefixLift 307595
  have htrace : WordTrace (prefixWord ++ tailWord_307595) baseStart_307595 baseEnd_307595 := by
    simpa [prefixWord, tailWord_307595, baseEnd_307595] using wordTrace_append hprefix tailTrace_307595
  have hstable : (prefixWord ++ tailWord_307595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307595).length < 2 ^ (prefixWord ++ tailWord_307595).sum := by decide
  have hdescent : baseEnd_307595 < baseStart_307595 := by decide
  rcases family_descends (prefixWord ++ tailWord_307595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307610 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_307610 : Nat := 118140960795 + 307610 * 2 ^ 59
def prefixEnd_307610 : Nat := 4983230072969 + 3 ^ 40 * 307610 * 2
def baseEnd_307610 : Nat := 105301189419764472106889

theorem tailTrace_307610 : CollatzResearch.WordTrace tailWord_307610 prefixEnd_307610 105301189419764472106889 := by
  unfold tailWord_307610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804864603897245112634071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7479638943725986967024189 2804864603897245112634071)
  ·
    refine ⟨4207296905845867668951107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2804864603897245112634071 4207296905845867668951107)
    ·
      refine ⟨6310945358768801503426661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4207296905845867668951107 6310945358768801503426661)
      ·
        refine ⟨1183302254769150281892499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6310945358768801503426661 1183302254769150281892499)
        ·
          refine ⟨1774953382153725422838749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183302254769150281892499 1774953382153725422838749)
          ·
            refine ⟨665607518307647033564531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1774953382153725422838749 665607518307647033564531)
            ·
              refine ⟨998411277461470550346797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665607518307647033564531 998411277461470550346797)
              ·
                refine ⟨374404229048051456380049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998411277461470550346797 374404229048051456380049)
                ·
                  refine ⟨280803171786038592285037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 374404229048051456380049 280803171786038592285037)
                  ·
                    refine ⟨105301189419764472106889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280803171786038592285037 105301189419764472106889)
                    ·
                      rfl

theorem cell22_307610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_307610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307610 prefixEnd_307610 := by exact prefixLift 307610
  have htrace : WordTrace (prefixWord ++ tailWord_307610) baseStart_307610 baseEnd_307610 := by
    simpa [prefixWord, tailWord_307610, baseEnd_307610] using wordTrace_append hprefix tailTrace_307610
  have hstable : (prefixWord ++ tailWord_307610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307610).length < 2 ^ (prefixWord ++ tailWord_307610).sum := by decide
  have hdescent : baseEnd_307610 < baseStart_307610 := by decide
  rcases family_descends (prefixWord ++ tailWord_307610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307696 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 8]
def baseStart_307696 : Nat := 118140960795 + 307696 * 2 ^ 59
def prefixEnd_307696 : Nat := 4983230072969 + 3 ^ 40 * 307696 * 2
def baseEnd_307696 : Nat := 35110209659096304818875

theorem tailTrace_307696 : CollatzResearch.WordTrace tailWord_307696 prefixEnd_307696 35110209659096304818875 := by
  unfold tailWord_307696
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611297546638708569083471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7481730062184944758777961 5611297546638708569083471)
  ·
    refine ⟨8416946319958062853625207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5611297546638708569083471 8416946319958062853625207)
    ·
      refine ⟨12625419479937094280437811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8416946319958062853625207 12625419479937094280437811)
      ·
        refine ⟨18938129219905641420656717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12625419479937094280437811 18938129219905641420656717)
        ·
          refine ⟨7101798457464615532746269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18938129219905641420656717 7101798457464615532746269)
          ·
            refine ⟨2663174421549230824779851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7101798457464615532746269 2663174421549230824779851)
            ·
              refine ⟨3994761632323846237169777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2663174421549230824779851 3994761632323846237169777)
              ·
                refine ⟨2996071224242884677877333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3994761632323846237169777 2996071224242884677877333)
                ·
                  refine ⟨35110209659096304818875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2996071224242884677877333 35110209659096304818875)
                  ·
                    rfl

theorem cell22_307696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_307696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307696 prefixEnd_307696 := by exact prefixLift 307696
  have htrace : WordTrace (prefixWord ++ tailWord_307696) baseStart_307696 baseEnd_307696 := by
    simpa [prefixWord, tailWord_307696, baseEnd_307696] using wordTrace_append hprefix tailTrace_307696
  have hstable : (prefixWord ++ tailWord_307696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307696).length < 2 ^ (prefixWord ++ tailWord_307696).sum := by decide
  have hdescent : baseEnd_307696 < baseStart_307696 := by decide
  rcases family_descends (prefixWord ++ tailWord_307696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307713 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 6]
def baseStart_307713 : Nat := 118140960795 + 307713 * 2 ^ 59
def prefixEnd_307713 : Nat := 4983230072969 + 3 ^ 40 * 307713 * 2
def baseEnd_307713 : Nat := 35112149474902178927191

theorem tailTrace_307713 : CollatzResearch.WordTrace tailWord_307713 prefixEnd_307713 35112149474902178927191 := by
  unfold tailWord_307713
  simp only [CollatzResearch.WordTrace]
  refine ⟨11223215134215829041535793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7482143422810552694357195 11223215134215829041535793)
  ·
    refine ⟨8417411350661871781151845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11223215134215829041535793 8417411350661871781151845)
    ·
      refine ⟨1578264628249100958965971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8417411350661871781151845 1578264628249100958965971)
      ·
        refine ⟨2367396942373651438448957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578264628249100958965971 2367396942373651438448957)
        ·
          refine ⟨887773853390119289418359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2367396942373651438448957 887773853390119289418359)
          ·
            refine ⟨1331660780085178934127539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887773853390119289418359 1331660780085178934127539)
            ·
              refine ⟨1997491170127768401191309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331660780085178934127539 1997491170127768401191309)
              ·
                refine ⟨749059188797913150446741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1997491170127768401191309 749059188797913150446741)
                ·
                  refine ⟨35112149474902178927191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 749059188797913150446741 35112149474902178927191)
                  ·
                    rfl

theorem cell22_307713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_307713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307713 prefixEnd_307713 := by exact prefixLift 307713
  have htrace : WordTrace (prefixWord ++ tailWord_307713) baseStart_307713 baseEnd_307713 := by
    simpa [prefixWord, tailWord_307713, baseEnd_307713] using wordTrace_append hprefix tailTrace_307713
  have hstable : (prefixWord ++ tailWord_307713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307713).length < 2 ^ (prefixWord ++ tailWord_307713).sum := by decide
  have hdescent : baseEnd_307713 < baseStart_307713 := by decide
  rcases family_descends (prefixWord ++ tailWord_307713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307732 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_307732 : Nat := 118140960795 + 307732 * 2 ^ 59
def prefixEnd_307732 : Nat := 4983230072969 + 3 ^ 40 * 307732 * 2
def baseEnd_307732 : Nat := 105342952512996820556515

theorem tailTrace_307732 : CollatzResearch.WordTrace tailWord_307732 prefixEnd_307732 105342952512996820556515 := by
  unfold tailWord_307732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611954060573497643238725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7482605414097996857651633 5611954060573497643238725)
  ·
    refine ⟨1052241386357530808107261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5611954060573497643238725 1052241386357530808107261)
    ·
      refine ⟨394590519884074053040223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1052241386357530808107261 394590519884074053040223)
      ·
        refine ⟨591885779826111079560335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394590519884074053040223 591885779826111079560335)
        ·
          refine ⟨887828669739166619340503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591885779826111079560335 887828669739166619340503)
          ·
            refine ⟨1331743004608749929010755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887828669739166619340503 1331743004608749929010755)
            ·
              refine ⟨1997614506913124893516133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331743004608749929010755 1997614506913124893516133)
              ·
                refine ⟨374552720046210917534275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1997614506913124893516133 374552720046210917534275)
                ·
                  refine ⟨561829080069316376301413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374552720046210917534275 561829080069316376301413)
                  ·
                    refine ⟨105342952512996820556515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 561829080069316376301413 105342952512996820556515)
                    ·
                      rfl

theorem cell22_307732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_307732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307732 prefixEnd_307732 := by exact prefixLift 307732
  have htrace : WordTrace (prefixWord ++ tailWord_307732) baseStart_307732 baseEnd_307732 := by
    simpa [prefixWord, tailWord_307732, baseEnd_307732] using wordTrace_append hprefix tailTrace_307732
  have hstable : (prefixWord ++ tailWord_307732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307732).length < 2 ^ (prefixWord ++ tailWord_307732).sum := by decide
  have hdescent : baseEnd_307732 < baseStart_307732 := by decide
  rcases family_descends (prefixWord ++ tailWord_307732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307743 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 2, 4]
def baseStart_307743 : Nat := 118140960795 + 307743 * 2 ^ 59
def prefixEnd_307743 : Nat := 4983230072969 + 3 ^ 40 * 307743 * 2
def baseEnd_307743 : Nat := 105346718037796458531481

theorem tailTrace_307743 : CollatzResearch.WordTrace tailWord_307743 prefixEnd_307743 105346718037796458531481 := by
  unfold tailWord_307743
  simp only [CollatzResearch.WordTrace]
  refine ⟨11224309324107144165127883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7482872882738096110085255 11224309324107144165127883)
  ·
    refine ⟨16836463986160716247691825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11224309324107144165127883 16836463986160716247691825)
    ·
      refine ⟨12627347989620537185768869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16836463986160716247691825 12627347989620537185768869)
      ·
        refine ⟨2367627748053850722331663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12627347989620537185768869 2367627748053850722331663)
        ·
          refine ⟨3551441622080776083497495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2367627748053850722331663 3551441622080776083497495)
          ·
            refine ⟨5327162433121164125246243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551441622080776083497495 5327162433121164125246243)
            ·
              refine ⟨7990743649681746187869365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5327162433121164125246243 7990743649681746187869365)
              ·
                refine ⟨749132217157663705112753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7990743649681746187869365 749132217157663705112753)
                ·
                  refine ⟨561849162868247778834565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 749132217157663705112753 561849162868247778834565)
                  ·
                    refine ⟨105346718037796458531481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 561849162868247778834565 105346718037796458531481)
                    ·
                      rfl

theorem cell22_307743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_307743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307743 prefixEnd_307743 := by exact prefixLift 307743
  have htrace : WordTrace (prefixWord ++ tailWord_307743) baseStart_307743 baseEnd_307743 := by
    simpa [prefixWord, tailWord_307743, baseEnd_307743] using wordTrace_append hprefix tailTrace_307743
  have hstable : (prefixWord ++ tailWord_307743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307743).length < 2 ^ (prefixWord ++ tailWord_307743).sum := by decide
  have hdescent : baseEnd_307743 < baseStart_307743 := by decide
  rcases family_descends (prefixWord ++ tailWord_307743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307747 : List Nat := [1, 1, 1, 4, 4, 3, 1, 3, 4]
def baseStart_307747 : Nat := 118140960795 + 307747 * 2 ^ 59
def prefixEnd_307747 : Nat := 4983230072969 + 3 ^ 40 * 307747 * 2
def baseEnd_307747 : Nat := 35116029106513927143823

theorem tailTrace_307747 : CollatzResearch.WordTrace tailWord_307747 prefixEnd_307747 35116029106513927143823 := by
  unfold tailWord_307747
  simp only [CollatzResearch.WordTrace]
  refine ⟨11224455216092652848273495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7482970144061768565515663 11224455216092652848273495)
  ·
    refine ⟨16836682824138979272410243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11224455216092652848273495 16836682824138979272410243)
    ·
      refine ⟨25255024236208468908615365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16836682824138979272410243 25255024236208468908615365)
      ·
        refine ⟨4735317044289087920365381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25255024236208468908615365 4735317044289087920365381)
        ·
          refine ⟨887871945804203985068509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4735317044289087920365381 887871945804203985068509)
          ·
            refine ⟨332951979676576494400691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 887871945804203985068509 332951979676576494400691)
            ·
              refine ⟨499427969514864741601037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332951979676576494400691 499427969514864741601037)
              ·
                refine ⟨187285488568074278100389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499427969514864741601037 187285488568074278100389)
                ·
                  refine ⟨35116029106513927143823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187285488568074278100389 35116029106513927143823)
                  ·
                    rfl

theorem cell22_307747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 4].length) (baseStart_307747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307747 prefixEnd_307747 := by exact prefixLift 307747
  have htrace : WordTrace (prefixWord ++ tailWord_307747) baseStart_307747 baseEnd_307747 := by
    simpa [prefixWord, tailWord_307747, baseEnd_307747] using wordTrace_append hprefix tailTrace_307747
  have hstable : (prefixWord ++ tailWord_307747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307747).length < 2 ^ (prefixWord ++ tailWord_307747).sum := by decide
  have hdescent : baseEnd_307747 < baseStart_307747 := by decide
  rcases family_descends (prefixWord ++ tailWord_307747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307764 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 6]
def baseStart_307764 : Nat := 118140960795 + 307764 * 2 ^ 59
def prefixEnd_307764 : Nat := 4983230072969 + 3 ^ 40 * 307764 * 2
def baseEnd_307764 : Nat := 35117968922319801252139

theorem tailTrace_307764 : CollatzResearch.WordTrace tailWord_307764 prefixEnd_307764 35117968922319801252139 := by
  unfold tailWord_307764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612537628515532375821173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7483383504687376501094897 5612537628515532375821173)
  ·
    refine ⟨526175402673331160233235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5612537628515532375821173 526175402673331160233235)
    ·
      refine ⟨789263104009996740349853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526175402673331160233235 789263104009996740349853)
      ·
        refine ⟨295973664003748777631195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 789263104009996740349853 295973664003748777631195)
        ·
          refine ⟨443960496005623166446793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295973664003748777631195 443960496005623166446793)
          ·
            refine ⟨332970372004217374835095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443960496005623166446793 332970372004217374835095)
            ·
              refine ⟨499455558006326062252643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332970372004217374835095 499455558006326062252643)
              ·
                refine ⟨749183337009489093378965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499455558006326062252643 749183337009489093378965)
                ·
                  refine ⟨35117968922319801252139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 749183337009489093378965 35117968922319801252139)
                  ·
                    rfl

theorem cell22_307764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_307764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307764 prefixEnd_307764 := by exact prefixLift 307764
  have htrace : WordTrace (prefixWord ++ tailWord_307764) baseStart_307764 baseEnd_307764 := by
    simpa [prefixWord, tailWord_307764, baseEnd_307764] using wordTrace_append hprefix tailTrace_307764
  have hstable : (prefixWord ++ tailWord_307764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307764).length < 2 ^ (prefixWord ++ tailWord_307764).sum := by decide
  have hdescent : baseEnd_307764 < baseStart_307764 := by decide
  rcases family_descends (prefixWord ++ tailWord_307764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307790 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_307790 : Nat := 118140960795 + 307790 * 2 ^ 59
def prefixEnd_307790 : Nat := 4983230072969 + 3 ^ 40 * 307790 * 2
def baseEnd_307790 : Nat := 105362807098304002606337

theorem tailTrace_307790 : CollatzResearch.WordTrace tailWord_307790 prefixEnd_307790 105362807098304002606337 := by
  unfold tailWord_307790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403252944367108899011103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7484015703291247461392549 1403252944367108899011103)
  ·
    refine ⟨2104879416550663348516655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1403252944367108899011103 2104879416550663348516655)
    ·
      refine ⟨3157319124825995022774983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2104879416550663348516655 3157319124825995022774983)
      ·
        refine ⟨4735978687238992534162475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3157319124825995022774983 4735978687238992534162475)
        ·
          refine ⟨7103968030858488801243713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4735978687238992534162475 7103968030858488801243713)
          ·
            refine ⟨5327976023143866600932785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7103968030858488801243713 5327976023143866600932785)
            ·
              refine ⟨3995982017357899950699589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5327976023143866600932785 3995982017357899950699589)
              ·
                refine ⟨749246628254606240756173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3995982017357899950699589 749246628254606240756173)
                ·
                  refine ⟨280967485595477340283565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 749246628254606240756173 280967485595477340283565)
                  ·
                    refine ⟨105362807098304002606337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280967485595477340283565 105362807098304002606337)
                    ·
                      rfl

theorem cell22_307790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_307790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307790 prefixEnd_307790 := by exact prefixLift 307790
  have htrace : WordTrace (prefixWord ++ tailWord_307790) baseStart_307790 baseEnd_307790 := by
    simpa [prefixWord, tailWord_307790, baseEnd_307790] using wordTrace_append hprefix tailTrace_307790
  have hstable : (prefixWord ++ tailWord_307790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307790).length < 2 ^ (prefixWord ++ tailWord_307790).sum := by decide
  have hdescent : baseEnd_307790 < baseStart_307790 := by decide
  rcases family_descends (prefixWord ++ tailWord_307790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307824 : List Nat := [2, 1, 1, 1, 7, 1, 1, 4, 1, 3]
def baseStart_307824 : Nat := 118140960795 + 307824 * 2 ^ 59
def prefixEnd_307824 : Nat := 4983230072969 + 3 ^ 40 * 307824 * 2
def baseEnd_307824 : Nat := 105374445993139247256233

theorem tailTrace_307824 : CollatzResearch.WordTrace tailWord_307824 prefixEnd_307824 105374445993139247256233 := by
  unfold tailWord_307824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613631818406847499413263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7484842424542463332551017 5613631818406847499413263)
  ·
    refine ⟨8420447727610271249119895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613631818406847499413263 8420447727610271249119895)
    ·
      refine ⟨12630671591415406873679843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8420447727610271249119895 12630671591415406873679843)
      ·
        refine ⟨18946007387123110310519765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12630671591415406873679843 18946007387123110310519765)
        ·
          refine ⟨444047048135697897902807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18946007387123110310519765 444047048135697897902807)
          ·
            refine ⟨666070572203546846854211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444047048135697897902807 666070572203546846854211)
            ·
              refine ⟨999105858305320270281317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666070572203546846854211 999105858305320270281317)
              ·
                refine ⟨187332348432247550677747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 999105858305320270281317 187332348432247550677747)
                ·
                  refine ⟨280998522648371326016621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187332348432247550677747 280998522648371326016621)
                  ·
                    refine ⟨105374445993139247256233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 280998522648371326016621 105374445993139247256233)
                    ·
                      rfl

theorem cell22_307824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 1, 3].length) (baseStart_307824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_307824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_307824 prefixEnd_307824 := by exact prefixLift 307824
  have htrace : WordTrace (prefixWord ++ tailWord_307824) baseStart_307824 baseEnd_307824 := by
    simpa [prefixWord, tailWord_307824, baseEnd_307824] using wordTrace_append hprefix tailTrace_307824
  have hstable : (prefixWord ++ tailWord_307824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307824).length < 2 ^ (prefixWord ++ tailWord_307824).sum := by decide
  have hdescent : baseEnd_307824 < baseStart_307824 := by decide
  rcases family_descends (prefixWord ++ tailWord_307824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308002 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_308002 : Nat := 118140960795 + 308002 * 2 ^ 59
def prefixEnd_308002 : Nat := 4983230072969 + 3 ^ 40 * 308002 * 2
def baseEnd_308002 : Nat := 105435379030806116305687

theorem tailTrace_308002 : CollatzResearch.WordTrace tailWord_308002 prefixEnd_308002 105435379030806116305687 := by
  unfold tailWord_308002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808438957542207849701565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7489170553445887599204173 2808438957542207849701565)
  ·
    refine ⟨1053164609078327943638087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2808438957542207849701565 1053164609078327943638087)
    ·
      refine ⟨1579746913617491915457131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1053164609078327943638087 1579746913617491915457131)
      ·
        refine ⟨2369620370426237873185697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579746913617491915457131 2369620370426237873185697)
        ·
          refine ⟨1777215277819678404889273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2369620370426237873185697 1777215277819678404889273)
          ·
            refine ⟨1332911458364758803666955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1777215277819678404889273 1332911458364758803666955)
            ·
              refine ⟨1999367187547138205500433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332911458364758803666955 1999367187547138205500433)
              ·
                refine ⟨1499525390660353654125325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999367187547138205500433 1499525390660353654125325)
                ·
                  refine ⟨562322021497632620296997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1499525390660353654125325 562322021497632620296997)
                  ·
                    refine ⟨105435379030806116305687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 562322021497632620296997 105435379030806116305687)
                    ·
                      rfl

theorem cell22_308002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_308002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308002 prefixEnd_308002 := by exact prefixLift 308002
  have htrace : WordTrace (prefixWord ++ tailWord_308002) baseStart_308002 baseEnd_308002 := by
    simpa [prefixWord, tailWord_308002, baseEnd_308002] using wordTrace_append hprefix tailTrace_308002
  have hstable : (prefixWord ++ tailWord_308002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308002).length < 2 ^ (prefixWord ++ tailWord_308002).sum := by decide
  have hdescent : baseEnd_308002 < baseStart_308002 := by decide
  rcases family_descends (prefixWord ++ tailWord_308002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308049 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 4, 3]
def baseStart_308049 : Nat := 118140960795 + 308049 * 2 ^ 59
def prefixEnd_308049 : Nat := 4983230072969 + 3 ^ 40 * 308049 * 2
def baseEnd_308049 : Nat := 105451468091313660380543

theorem tailTrace_308049 : CollatzResearch.WordTrace tailWord_308049 prefixEnd_308049 105451468091313660380543 := by
  unfold tailWord_308049
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235470060998558425767201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7490313373999038950511467 11235470060998558425767201)
  ·
    refine ⟨8426602545748918819325401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11235470060998558425767201 8426602545748918819325401)
    ·
      refine ⟨6319951909311689114494051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8426602545748918819325401 6319951909311689114494051)
      ·
        refine ⟨9479927863967533671741077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319951909311689114494051 9479927863967533671741077)
        ·
          refine ⟨444371618623478140862863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9479927863967533671741077 444371618623478140862863)
          ·
            refine ⟨666557427935217211294295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444371618623478140862863 666557427935217211294295)
            ·
              refine ⟨999836141902825816941443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666557427935217211294295 999836141902825816941443)
              ·
                refine ⟨1499754212854238725412165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999836141902825816941443 1499754212854238725412165)
                ·
                  refine ⟨281203914910169761014781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499754212854238725412165 281203914910169761014781)
                  ·
                    refine ⟨105451468091313660380543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281203914910169761014781 105451468091313660380543)
                    ·
                      rfl

theorem cell22_308049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 3].length) (baseStart_308049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308049 prefixEnd_308049 := by exact prefixLift 308049
  have htrace : WordTrace (prefixWord ++ tailWord_308049) baseStart_308049 baseEnd_308049 := by
    simpa [prefixWord, tailWord_308049, baseEnd_308049] using wordTrace_append hprefix tailTrace_308049
  have hstable : (prefixWord ++ tailWord_308049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308049).length < 2 ^ (prefixWord ++ tailWord_308049).sum := by decide
  have hdescent : baseEnd_308049 < baseStart_308049 := by decide
  rcases family_descends (prefixWord ++ tailWord_308049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308066 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_308066 : Nat := 118140960795 + 308066 * 2 ^ 59
def prefixEnd_308066 : Nat := 4983230072969 + 3 ^ 40 * 308066 * 2
def baseEnd_308066 : Nat := 105457287538731282705491

theorem tailTrace_308066 : CollatzResearch.WordTrace tailWord_308066 prefixEnd_308066 105457287538731282705491 := by
  unfold tailWord_308066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809022525484242582284013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7490726734624646886090701 2809022525484242582284013)
  ·
    refine ⟨1053383447056590968356505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2809022525484242582284013 1053383447056590968356505)
    ·
      refine ⟨790037585292443226267379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1053383447056590968356505 790037585292443226267379)
      ·
        refine ⟨1185056377938664839401069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790037585292443226267379 1185056377938664839401069)
        ·
          refine ⟨444396141726999314775401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1185056377938664839401069 444396141726999314775401)
          ·
            refine ⟨333297106295249486081551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444396141726999314775401 333297106295249486081551)
            ·
              refine ⟨499945659442874229122327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333297106295249486081551 499945659442874229122327)
              ·
                refine ⟨749918489164311343683491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499945659442874229122327 749918489164311343683491)
                ·
                  refine ⟨1124877733746467015525237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 749918489164311343683491 1124877733746467015525237)
                  ·
                    refine ⟨105457287538731282705491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1124877733746467015525237 105457287538731282705491)
                    ·
                      rfl

theorem cell22_308066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_308066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308066 prefixEnd_308066 := by exact prefixLift 308066
  have htrace : WordTrace (prefixWord ++ tailWord_308066) baseStart_308066 baseEnd_308066 := by
    simpa [prefixWord, tailWord_308066, baseEnd_308066] using wordTrace_append hprefix tailTrace_308066
  have hstable : (prefixWord ++ tailWord_308066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308066).length < 2 ^ (prefixWord ++ tailWord_308066).sum := by decide
  have hdescent : baseEnd_308066 < baseStart_308066 := by decide
  rcases family_descends (prefixWord ++ tailWord_308066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308075 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 2, 6]
def baseStart_308075 : Nat := 118140960795 + 308075 * 2 ^ 59
def prefixEnd_308075 : Nat := 4983230072969 + 3 ^ 40 * 308075 * 2
def baseEnd_308075 : Nat := 105460368422658259230463

theorem tailTrace_308075 : CollatzResearch.WordTrace tailWord_308075 prefixEnd_308075 105460368422658259230463 := by
  unfold tailWord_308075
  simp only [CollatzResearch.WordTrace]
  refine ⟨11236418358904364866213679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7490945572602909910809119 11236418358904364866213679)
  ·
    refine ⟨16854627538356547299320519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11236418358904364866213679 16854627538356547299320519)
    ·
      refine ⟨25281941307534820948980779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16854627538356547299320519 25281941307534820948980779)
      ·
        refine ⟨37922911961302231423471169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25281941307534820948980779 37922911961302231423471169)
        ·
          refine ⟨28442183970976673567603377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37922911961302231423471169 28442183970976673567603377)
          ·
            refine ⟨21331637978232505175702533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28442183970976673567603377 21331637978232505175702533)
            ·
              refine ⟨3999682120918594720444225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21331637978232505175702533 3999682120918594720444225)
              ·
                refine ⟨2999761590688946040333169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3999682120918594720444225 2999761590688946040333169)
                ·
                  refine ⟨2249821193016709530249877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2999761590688946040333169 2249821193016709530249877)
                  ·
                    refine ⟨105460368422658259230463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2249821193016709530249877 105460368422658259230463)
                    ·
                      rfl

theorem cell22_308075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 6].length) (baseStart_308075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308075 prefixEnd_308075 := by exact prefixLift 308075
  have htrace : WordTrace (prefixWord ++ tailWord_308075) baseStart_308075 baseEnd_308075 := by
    simpa [prefixWord, tailWord_308075, baseEnd_308075] using wordTrace_append hprefix tailTrace_308075
  have hstable : (prefixWord ++ tailWord_308075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308075).length < 2 ^ (prefixWord ++ tailWord_308075).sum := by decide
  have hdescent : baseEnd_308075 < baseStart_308075 := by decide
  rcases family_descends (prefixWord ++ tailWord_308075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308098 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_308098 : Nat := 118140960795 + 308098 * 2 ^ 59
def prefixEnd_308098 : Nat := 4983230072969 + 3 ^ 40 * 308098 * 2
def baseEnd_308098 : Nat := 105468241792693865905393

theorem tailTrace_308098 : CollatzResearch.WordTrace tailWord_308098 prefixEnd_308098 105468241792693865905393 := by
  unfold tailWord_308098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2809314309455259948575237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7491504825214026529533965 2809314309455259948575237)
  ·
    refine ⟨526746433022861240357857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2809314309455259948575237 526746433022861240357857)
    ·
      refine ⟨395059824767145930268393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 526746433022861240357857 395059824767145930268393)
      ·
        refine ⟨296294868575359447701295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395059824767145930268393 296294868575359447701295)
        ·
          refine ⟨444442302863039171551943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296294868575359447701295 444442302863039171551943)
          ·
            refine ⟨666663454294558757327915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444442302863039171551943 666663454294558757327915)
            ·
              refine ⟨999995181441838135991873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666663454294558757327915 999995181441838135991873)
              ·
                refine ⟨749996386081378601993905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 999995181441838135991873 749996386081378601993905)
                ·
                  refine ⟨562497289561033951495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 749996386081378601993905 562497289561033951495429)
                  ·
                    refine ⟨105468241792693865905393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 562497289561033951495429 105468241792693865905393)
                    ·
                      rfl

theorem cell22_308098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_308098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308098 prefixEnd_308098 := by exact prefixLift 308098
  have htrace : WordTrace (prefixWord ++ tailWord_308098) baseStart_308098 baseEnd_308098 := by
    simpa [prefixWord, tailWord_308098, baseEnd_308098] using wordTrace_append hprefix tailTrace_308098
  have hstable : (prefixWord ++ tailWord_308098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308098).length < 2 ^ (prefixWord ++ tailWord_308098).sum := by decide
  have hdescent : baseEnd_308098 < baseStart_308098 := by decide
  rcases family_descends (prefixWord ++ tailWord_308098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308137 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 3, 4]
def baseStart_308137 : Nat := 118140960795 + 308137 * 2 ^ 59
def prefixEnd_308137 : Nat := 4983230072969 + 3 ^ 40 * 308137 * 2
def baseEnd_308137 : Nat := 105481592289710764180273

theorem tailTrace_308137 : CollatzResearch.WordTrace tailWord_308137 prefixEnd_308137 105481592289710764180273 := by
  unfold tailWord_308137
  simp only [CollatzResearch.WordTrace]
  refine ⟨11238679684679749454970665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7492453123119832969980443 11238679684679749454970665)
  ·
    refine ⟨8429009763509812091227999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11238679684679749454970665 8429009763509812091227999)
    ·
      refine ⟨12643514645264718136841999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8429009763509812091227999 12643514645264718136841999)
      ·
        refine ⟨18965271967897077205262999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12643514645264718136841999 18965271967897077205262999)
        ·
          refine ⟨28447907951845615807894499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18965271967897077205262999 28447907951845615807894499)
          ·
            refine ⟨42671861927768423711841749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28447907951845615807894499 42671861927768423711841749)
            ·
              refine ⟨1000121763932072430746291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42671861927768423711841749 1000121763932072430746291)
              ·
                refine ⟨1500182645898108646119437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000121763932072430746291 1500182645898108646119437)
                ·
                  refine ⟨562568492211790742294789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1500182645898108646119437 562568492211790742294789)
                  ·
                    refine ⟨105481592289710764180273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 562568492211790742294789 105481592289710764180273)
                    ·
                      rfl

theorem cell22_308137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_308137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308137 prefixEnd_308137 := by exact prefixLift 308137
  have htrace : WordTrace (prefixWord ++ tailWord_308137) baseStart_308137 baseEnd_308137 := by
    simpa [prefixWord, tailWord_308137, baseEnd_308137] using wordTrace_append hprefix tailTrace_308137
  have hstable : (prefixWord ++ tailWord_308137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308137).length < 2 ^ (prefixWord ++ tailWord_308137).sum := by decide
  have hdescent : baseEnd_308137 < baseStart_308137 := by decide
  rcases family_descends (prefixWord ++ tailWord_308137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308184 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_308184 : Nat := 118140960795 + 308184 * 2 ^ 59
def prefixEnd_308184 : Nat := 4983230072969 + 3 ^ 40 * 308184 * 2
def baseEnd_308184 : Nat := 105497681350218308255129

theorem tailTrace_308184 : CollatzResearch.WordTrace tailWord_308184 prefixEnd_308184 105497681350218308255129 := by
  unfold tailWord_308184
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620196957754738240965803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7493595943672984321287737 5620196957754738240965803)
  ·
    refine ⟨8430295436632107361448705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5620196957754738240965803 8430295436632107361448705)
    ·
      refine ⟨6322721577474080521086529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8430295436632107361448705 6322721577474080521086529)
      ·
        refine ⟨4742041183105560390814897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6322721577474080521086529 4742041183105560390814897)
        ·
          refine ⟨3556530887329170293111173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4742041183105560390814897 3556530887329170293111173)
          ·
            refine ⟨666849541374219429958345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3556530887329170293111173 666849541374219429958345)
            ·
              refine ⟨500137156030664572468759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 666849541374219429958345 500137156030664572468759)
              ·
                refine ⟨750205734045996858703139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500137156030664572468759 750205734045996858703139)
                ·
                  refine ⟨1125308601068995288054709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750205734045996858703139 1125308601068995288054709)
                  ·
                    refine ⟨105497681350218308255129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1125308601068995288054709 105497681350218308255129)
                    ·
                      rfl

theorem cell22_308184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_308184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308184 prefixEnd_308184 := by exact prefixLift 308184
  have htrace : WordTrace (prefixWord ++ tailWord_308184) baseStart_308184 baseEnd_308184 := by
    simpa [prefixWord, tailWord_308184, baseEnd_308184] using wordTrace_append hprefix tailTrace_308184
  have hstable : (prefixWord ++ tailWord_308184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308184).length < 2 ^ (prefixWord ++ tailWord_308184).sum := by decide
  have hdescent : baseEnd_308184 < baseStart_308184 := by decide
  rcases family_descends (prefixWord ++ tailWord_308184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308199 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 1, 6]
def baseStart_308199 : Nat := 118140960795 + 308199 * 2 ^ 59
def prefixEnd_308199 : Nat := 4983230072969 + 3 ^ 40 * 308199 * 2
def baseEnd_308199 : Nat := 105502816156763269130083

theorem tailTrace_308199 : CollatzResearch.WordTrace tailWord_308199 prefixEnd_308199 105502816156763269130083 := by
  unfold tailWord_308199
  simp only [CollatzResearch.WordTrace]
  refine ⟨11240941010455134043727651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7493960673636756029151767 11240941010455134043727651)
  ·
    refine ⟨16861411515682701065591477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11240941010455134043727651 16861411515682701065591477)
    ·
      refine ⟨1580757329595253224899201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16861411515682701065591477 1580757329595253224899201)
      ·
        refine ⟨1185567997196439918674401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1580757329595253224899201 1185567997196439918674401)
        ·
          refine ⟨889175997897329939005801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185567997196439918674401 889175997897329939005801)
          ·
            refine ⟨666881998422997454254351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889175997897329939005801 666881998422997454254351)
            ·
              refine ⟨1000322997634496181381527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666881998422997454254351 1000322997634496181381527)
              ·
                refine ⟨1500484496451744272072291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000322997634496181381527 1500484496451744272072291)
                ·
                  refine ⟨2250726744677616408108437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1500484496451744272072291 2250726744677616408108437)
                  ·
                    refine ⟨105502816156763269130083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2250726744677616408108437 105502816156763269130083)
                    ·
                      rfl

theorem cell22_308199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_308199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308199 prefixEnd_308199 := by exact prefixLift 308199
  have htrace : WordTrace (prefixWord ++ tailWord_308199) baseStart_308199 baseEnd_308199 := by
    simpa [prefixWord, tailWord_308199, baseEnd_308199] using wordTrace_append hprefix tailTrace_308199
  have hstable : (prefixWord ++ tailWord_308199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308199).length < 2 ^ (prefixWord ++ tailWord_308199).sum := by decide
  have hdescent : baseEnd_308199 < baseStart_308199 := by decide
  rcases family_descends (prefixWord ++ tailWord_308199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308214 : List Nat := [5, 1, 1, 1, 3, 2, 9]
def baseStart_308214 : Nat := 118140960795 + 308214 * 2 ^ 59
def prefixEnd_308214 : Nat := 4983230072969 + 3 ^ 40 * 308214 * 2
def baseEnd_308214 : Nat := 3907701887529934444631

theorem tailTrace_308214 : CollatzResearch.WordTrace tailWord_308214 prefixEnd_308214 3907701887529934444631 := by
  unfold tailWord_308214
  simp only [CollatzResearch.WordTrace]
  refine ⟨702593006587549475345231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7494325403600527737015797 702593006587549475345231)
  ·
    refine ⟨1053889509881324213017847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702593006587549475345231 1053889509881324213017847)
    ·
      refine ⟨1580834264821986319526771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1053889509881324213017847 1580834264821986319526771)
      ·
        refine ⟨2371251397232979479290157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1580834264821986319526771 2371251397232979479290157)
        ·
          refine ⟨889219273962367304733809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2371251397232979479290157 889219273962367304733809)
          ·
            refine ⟨666914455471775478550357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889219273962367304733809 666914455471775478550357)
            ·
              refine ⟨3907701887529934444631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 666914455471775478550357 3907701887529934444631)
              ·
                rfl

theorem cell22_308214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 9].length) (baseStart_308214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308214 prefixEnd_308214 := by exact prefixLift 308214
  have htrace : WordTrace (prefixWord ++ tailWord_308214) baseStart_308214 baseEnd_308214 := by
    simpa [prefixWord, tailWord_308214, baseEnd_308214] using wordTrace_append hprefix tailTrace_308214
  have hstable : (prefixWord ++ tailWord_308214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308214).length < 2 ^ (prefixWord ++ tailWord_308214).sum := by decide
  have hdescent : baseEnd_308214 < baseStart_308214 := by decide
  rcases family_descends (prefixWord ++ tailWord_308214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308276 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 7]
def baseStart_308276 : Nat := 118140960795 + 308276 * 2 ^ 59
def prefixEnd_308276 : Nat := 4983230072969 + 3 ^ 40 * 308276 * 2
def baseEnd_308276 : Nat := 35176391610120244984949

theorem tailTrace_308276 : CollatzResearch.WordTrace tailWord_308276 prefixEnd_308276 35176391610120244984949 := by
  unfold tailWord_308276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621874715588088097140341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7495832954117450796187121 5621874715588088097140341)
  ·
    refine ⟨527050754586383259106907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5621874715588088097140341 527050754586383259106907)
    ·
      refine ⟨790576131879574888660361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527050754586383259106907 790576131879574888660361)
      ·
        refine ⟨592932098909681166495271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 790576131879574888660361 592932098909681166495271)
        ·
          refine ⟨889398148364521749742907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592932098909681166495271 889398148364521749742907)
          ·
            refine ⟨1334097222546782624614361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889398148364521749742907 1334097222546782624614361)
            ·
              refine ⟨1000572916910086968460771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334097222546782624614361 1000572916910086968460771)
              ·
                refine ⟨1500859375365130452691157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000572916910086968460771 1500859375365130452691157)
                ·
                  refine ⟨35176391610120244984949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1500859375365130452691157 35176391610120244984949)
                  ·
                    rfl

theorem cell22_308276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_308276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308276 prefixEnd_308276 := by exact prefixLift 308276
  have htrace : WordTrace (prefixWord ++ tailWord_308276) baseStart_308276 baseEnd_308276 := by
    simpa [prefixWord, tailWord_308276, baseEnd_308276] using wordTrace_append hprefix tailTrace_308276
  have hstable : (prefixWord ++ tailWord_308276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308276).length < 2 ^ (prefixWord ++ tailWord_308276).sum := by decide
  have hdescent : baseEnd_308276 < baseStart_308276 := by decide
  rcases family_descends (prefixWord ++ tailWord_308276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308280 : List Nat := [2, 1, 2, 1, 5, 2, 3, 2, 1, 3]
def baseStart_308280 : Nat := 118140960795 + 308280 * 2 ^ 59
def prefixEnd_308280 : Nat := 4983230072969 + 3 ^ 40 * 308280 * 2
def baseEnd_308280 : Nat := 105530544112106057854835

theorem tailTrace_308280 : CollatzResearch.WordTrace tailWord_308280 prefixEnd_308280 105530544112106057854835 := by
  unfold tailWord_308280
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621947661580842438713147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7495930215441123251617529 5621947661580842438713147)
  ·
    refine ⟨8432921492371263658069721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5621947661580842438713147 8432921492371263658069721)
    ·
      refine ⟨6324691119278447743552291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8432921492371263658069721 6324691119278447743552291)
      ·
        refine ⟨9487036678917671615328437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6324691119278447743552291 9487036678917671615328437)
        ·
          refine ⟨889409688648531713937041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9487036678917671615328437 889409688648531713937041)
          ·
            refine ⟨667057266486398785452781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889409688648531713937041 667057266486398785452781)
            ·
              refine ⟨250146474932399544544793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 667057266486398785452781 250146474932399544544793)
              ·
                refine ⟨187609856199299658408595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250146474932399544544793 187609856199299658408595)
                ·
                  refine ⟨281414784298949487612893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187609856199299658408595 281414784298949487612893)
                  ·
                    refine ⟨105530544112106057854835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281414784298949487612893 105530544112106057854835)
                    ·
                      rfl

theorem cell22_308280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_308280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308280 prefixEnd_308280 := by exact prefixLift 308280
  have htrace : WordTrace (prefixWord ++ tailWord_308280) baseStart_308280 baseEnd_308280 := by
    simpa [prefixWord, tailWord_308280, baseEnd_308280] using wordTrace_append hprefix tailTrace_308280
  have hstable : (prefixWord ++ tailWord_308280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308280).length < 2 ^ (prefixWord ++ tailWord_308280).sum := by decide
  have hdescent : baseEnd_308280 < baseStart_308280 := by decide
  rcases family_descends (prefixWord ++ tailWord_308280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308306 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_308306 : Nat := 118140960795 + 308306 * 2 ^ 59
def prefixEnd_308306 : Nat := 4983230072969 + 3 ^ 40 * 308306 * 2
def baseEnd_308306 : Nat := 105539444443450656704755

theorem tailTrace_308306 : CollatzResearch.WordTrace tailWord_308306 prefixEnd_308306 105539444443450656704755 := by
  unfold tailWord_308306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811210905266872829468193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7496562414044994211915181 2811210905266872829468193)
  ·
    refine ⟨2108408178950154622101145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2811210905266872829468193 2108408178950154622101145)
    ·
      refine ⟨1581306134212615966575859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2108408178950154622101145 1581306134212615966575859)
      ·
        refine ⟨2371959201318923949863789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581306134212615966575859 2371959201318923949863789)
        ·
          refine ⟨889484700494596481198921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2371959201318923949863789 889484700494596481198921)
          ·
            refine ⟨667113525370947360899191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889484700494596481198921 667113525370947360899191)
            ·
              refine ⟨1000670288056421041348787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667113525370947360899191 1000670288056421041348787)
              ·
                refine ⟨1501005432084631562023181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1000670288056421041348787 1501005432084631562023181)
                ·
                  refine ⟨562877037031736835758693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1501005432084631562023181 562877037031736835758693)
                  ·
                    refine ⟨105539444443450656704755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 562877037031736835758693 105539444443450656704755)
                    ·
                      rfl

theorem cell22_308306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_308306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308306 prefixEnd_308306 := by exact prefixLift 308306
  have htrace : WordTrace (prefixWord ++ tailWord_308306) baseStart_308306 baseEnd_308306 := by
    simpa [prefixWord, tailWord_308306, baseEnd_308306] using wordTrace_append hprefix tailTrace_308306
  have hstable : (prefixWord ++ tailWord_308306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308306).length < 2 ^ (prefixWord ++ tailWord_308306).sum := by decide
  have hdescent : baseEnd_308306 < baseStart_308306 := by decide
  rcases family_descends (prefixWord ++ tailWord_308306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308319 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 1, 5]
def baseStart_308319 : Nat := 118140960795 + 308319 * 2 ^ 59
def prefixEnd_308319 : Nat := 4983230072969 + 3 ^ 40 * 308319 * 2
def baseEnd_308319 : Nat := 105543894609122956129715

theorem tailTrace_308319 : CollatzResearch.WordTrace tailWord_308319 prefixEnd_308319 105543894609122956129715 := by
  unfold tailWord_308319
  simp only [CollatzResearch.WordTrace]
  refine ⟨11245317770020394538096011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7496878513346929692064007 11245317770020394538096011)
  ·
    refine ⟨16867976655030591807144017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11245317770020394538096011 16867976655030591807144017)
    ·
      refine ⟨12650982491272943855358013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16867976655030591807144017 12650982491272943855358013)
      ·
        refine ⟨4744118434227353945759255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12650982491272943855358013 4744118434227353945759255)
        ·
          refine ⟨7116177651341030918638883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4744118434227353945759255 7116177651341030918638883)
          ·
            refine ⟨10674266477011546377958325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7116177651341030918638883 10674266477011546377958325)
            ·
              refine ⟨1000712482219832472933593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10674266477011546377958325 1000712482219832472933593)
              ·
                refine ⟨750534361664874354700195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000712482219832472933593 750534361664874354700195)
                ·
                  refine ⟨1125801542497311532050293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750534361664874354700195 1125801542497311532050293)
                  ·
                    refine ⟨105543894609122956129715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1125801542497311532050293 105543894609122956129715)
                    ·
                      rfl

theorem cell22_308319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_308319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308319 prefixEnd_308319 := by exact prefixLift 308319
  have htrace : WordTrace (prefixWord ++ tailWord_308319) baseStart_308319 baseEnd_308319 := by
    simpa [prefixWord, tailWord_308319, baseEnd_308319] using wordTrace_append hprefix tailTrace_308319
  have hstable : (prefixWord ++ tailWord_308319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308319).length < 2 ^ (prefixWord ++ tailWord_308319).sum := by decide
  have hdescent : baseEnd_308319 < baseStart_308319 := by decide
  rcases family_descends (prefixWord ++ tailWord_308319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308353 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 2, 3]
def baseStart_308353 : Nat := 118140960795 + 308353 * 2 ^ 59
def prefixEnd_308353 : Nat := 4983230072969 + 3 ^ 40 * 308353 * 2
def baseEnd_308353 : Nat := 105555533503958200779611

theorem tailTrace_308353 : CollatzResearch.WordTrace tailWord_308353 prefixEnd_308353 105555533503958200779611 := by
  unfold tailWord_308353
  simp only [CollatzResearch.WordTrace]
  refine ⟨11246557851897218344833713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7497705234598145563222475 11246557851897218344833713)
  ·
    refine ⟨8434918388922913758625285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11246557851897218344833713 8434918388922913758625285)
    ·
      refine ⟨1581547197923046329742241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8434918388922913758625285 1581547197923046329742241)
      ·
        refine ⟨1186160398442284747306681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1581547197923046329742241 1186160398442284747306681)
        ·
          refine ⟨889620298831713560480011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186160398442284747306681 889620298831713560480011)
          ·
            refine ⟨1334430448247570340720017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 889620298831713560480011 1334430448247570340720017)
            ·
              refine ⟨1000822836185677755540013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334430448247570340720017 1000822836185677755540013)
              ·
                refine ⟨375308563569629158327505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1000822836185677755540013 375308563569629158327505)
                ·
                  refine ⟨281481422677221868745629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375308563569629158327505 281481422677221868745629)
                  ·
                    refine ⟨105555533503958200779611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281481422677221868745629 105555533503958200779611)
                    ·
                      rfl

theorem cell22_308353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_308353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308353 prefixEnd_308353 := by exact prefixLift 308353
  have htrace : WordTrace (prefixWord ++ tailWord_308353) baseStart_308353 baseEnd_308353 := by
    simpa [prefixWord, tailWord_308353, baseEnd_308353] using wordTrace_append hprefix tailTrace_308353
  have hstable : (prefixWord ++ tailWord_308353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308353).length < 2 ^ (prefixWord ++ tailWord_308353).sum := by decide
  have hdescent : baseEnd_308353 < baseStart_308353 := by decide
  rcases family_descends (prefixWord ++ tailWord_308353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308381 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_308381 : Nat := 118140960795 + 308381 * 2 ^ 59
def prefixEnd_308381 : Nat := 4983230072969 + 3 ^ 40 * 308381 * 2
def baseEnd_308381 : Nat := 105565118476175461079525

theorem tailTrace_308381 : CollatzResearch.WordTrace tailWord_308381 prefixEnd_308381 105565118476175461079525 := by
  unfold tailWord_308381
  simp only [CollatzResearch.WordTrace]
  refine ⟨11247579095795779126852997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7498386063863852751235331 11247579095795779126852997)
  ·
    refine ⟨2108921080461708586284937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11247579095795779126852997 2108921080461708586284937)
    ·
      refine ⟨1581690810346281439713703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2108921080461708586284937 1581690810346281439713703)
      ·
        refine ⟨2372536215519422159570555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581690810346281439713703 2372536215519422159570555)
        ·
          refine ⟨3558804323279133239355833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372536215519422159570555 3558804323279133239355833)
          ·
            refine ⟨2669103242459349929516875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3558804323279133239355833 2669103242459349929516875)
            ·
              refine ⟨4003654863689024894275313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2669103242459349929516875 4003654863689024894275313)
              ·
                refine ⟨3002741147766768670706485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4003654863689024894275313 3002741147766768670706485)
                ·
                  refine ⟨281506982603134562878733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3002741147766768670706485 281506982603134562878733)
                  ·
                    refine ⟨105565118476175461079525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281506982603134562878733 105565118476175461079525)
                    ·
                      rfl

theorem cell22_308381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_308381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308381 prefixEnd_308381 := by exact prefixLift 308381
  have htrace : WordTrace (prefixWord ++ tailWord_308381) baseStart_308381 baseEnd_308381 := by
    simpa [prefixWord, tailWord_308381, baseEnd_308381] using wordTrace_append hprefix tailTrace_308381
  have hstable : (prefixWord ++ tailWord_308381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308381).length < 2 ^ (prefixWord ++ tailWord_308381).sum := by decide
  have hdescent : baseEnd_308381 < baseStart_308381 := by decide
  rcases family_descends (prefixWord ++ tailWord_308381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308439 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 8]
def baseStart_308439 : Nat := 118140960795 + 308439 * 2 ^ 59
def prefixEnd_308439 : Nat := 4983230072969 + 3 ^ 40 * 308439 * 2
def baseEnd_308439 : Nat := 35194991020494214376449

theorem tailTrace_308439 : CollatzResearch.WordTrace tailWord_308439 prefixEnd_308439 35194991020494214376449 := by
  unfold tailWord_308439
  simp only [CollatzResearch.WordTrace]
  refine ⟨11249694529585655032464371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7499796353057103354976247 11249694529585655032464371)
  ·
    refine ⟨16874541794378482548696557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11249694529585655032464371 16874541794378482548696557)
    ·
      refine ⟨6327953172891930955761209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16874541794378482548696557 6327953172891930955761209)
      ·
        refine ⟨4745964879668948216820907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6327953172891930955761209 4745964879668948216820907)
        ·
          refine ⟨7118947319503422325231361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4745964879668948216820907 7118947319503422325231361)
          ·
            refine ⟨5339210489627566743923521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7118947319503422325231361 5339210489627566743923521)
            ·
              refine ⟨4004407867220675057942641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5339210489627566743923521 4004407867220675057942641)
              ·
                refine ⟨3003305900415506293456981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4004407867220675057942641 3003305900415506293456981)
                ·
                  refine ⟨35194991020494214376449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3003305900415506293456981 35194991020494214376449)
                  ·
                    rfl

theorem cell22_308439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 8].length) (baseStart_308439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308439 prefixEnd_308439 := by exact prefixLift 308439
  have htrace : WordTrace (prefixWord ++ tailWord_308439) baseStart_308439 baseEnd_308439 := by
    simpa [prefixWord, tailWord_308439, baseEnd_308439] using wordTrace_append hprefix tailTrace_308439
  have hstable : (prefixWord ++ tailWord_308439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308439).length < 2 ^ (prefixWord ++ tailWord_308439).sum := by decide
  have hdescent : baseEnd_308439 < baseStart_308439 := by decide
  rcases family_descends (prefixWord ++ tailWord_308439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308488 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_308488 : Nat := 118140960795 + 308488 * 2 ^ 59
def prefixEnd_308488 : Nat := 4983230072969 + 3 ^ 40 * 308488 * 2
def baseEnd_308488 : Nat := 105601746762862848654197

theorem tailTrace_308488 : CollatzResearch.WordTrace tailWord_308488 prefixEnd_308488 105601746762862848654197 := by
  unfold tailWord_308488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5625740853204068200499059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7500987804272090933998745 5625740853204068200499059)
  ·
    refine ⟨8438611279806102300748589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5625740853204068200499059 8438611279806102300748589)
    ·
      refine ⟨3164479229927288362780721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8438611279806102300748589 3164479229927288362780721)
      ·
        refine ⟨2373359422445466272085541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3164479229927288362780721 2373359422445466272085541)
        ·
          refine ⟨445004891708524926016039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2373359422445466272085541 445004891708524926016039)
          ·
            refine ⟨667507337562787389024059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445004891708524926016039 667507337562787389024059)
            ·
              refine ⟨1001261006344181083536089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667507337562787389024059 1001261006344181083536089)
              ·
                refine ⟨750945754758135812652067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001261006344181083536089 750945754758135812652067)
                ·
                  refine ⟨1126418632137203718978101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 750945754758135812652067 1126418632137203718978101)
                  ·
                    refine ⟨105601746762862848654197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1126418632137203718978101 105601746762862848654197)
                    ·
                      rfl

theorem cell22_308488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_308488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308488 prefixEnd_308488 := by exact prefixLift 308488
  have htrace : WordTrace (prefixWord ++ tailWord_308488) baseStart_308488 baseEnd_308488 := by
    simpa [prefixWord, tailWord_308488, baseEnd_308488] using wordTrace_append hprefix tailTrace_308488
  have hstable : (prefixWord ++ tailWord_308488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308488).length < 2 ^ (prefixWord ++ tailWord_308488).sum := by decide
  have hdescent : baseEnd_308488 < baseStart_308488 := by decide
  rcases family_descends (prefixWord ++ tailWord_308488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308533 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 5, 3]
def baseStart_308533 : Nat := 118140960795 + 308533 * 2 ^ 59
def prefixEnd_308533 : Nat := 4983230072969 + 3 ^ 40 * 308533 * 2
def baseEnd_308533 : Nat := 105617151182497731279059

theorem tailTrace_308533 : CollatzResearch.WordTrace tailWord_308533 prefixEnd_308533 105617151182497731279059 := by
  unfold tailWord_308533
  simp only [CollatzResearch.WordTrace]
  refine ⟨11253122991245109086386253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7502081994163406057590835 11253122991245109086386253)
  ·
    refine ⟨4219921121716915907394845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11253122991245109086386253 4219921121716915907394845)
    ·
      refine ⟨1582470420643843465273067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4219921121716915907394845 1582470420643843465273067)
      ·
        refine ⟨2373705630965765197909601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582470420643843465273067 2373705630965765197909601)
        ·
          refine ⟨1780279223224323898432201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2373705630965765197909601 1780279223224323898432201)
          ·
            refine ⟨1335209417418242923824151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1780279223224323898432201 1335209417418242923824151)
            ·
              refine ⟨2002814126127364385736227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335209417418242923824151 2002814126127364385736227)
              ·
                refine ⟨3004221189191046578604341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2002814126127364385736227 3004221189191046578604341)
                ·
                  refine ⟨281645736486660616744157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3004221189191046578604341 281645736486660616744157)
                  ·
                    refine ⟨105617151182497731279059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281645736486660616744157 105617151182497731279059)
                    ·
                      rfl

theorem cell22_308533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_308533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308533 prefixEnd_308533 := by exact prefixLift 308533
  have htrace : WordTrace (prefixWord ++ tailWord_308533) baseStart_308533 baseEnd_308533 := by
    simpa [prefixWord, tailWord_308533, baseEnd_308533] using wordTrace_append hprefix tailTrace_308533
  have hstable : (prefixWord ++ tailWord_308533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308533).length < 2 ^ (prefixWord ++ tailWord_308533).sum := by decide
  have hdescent : baseEnd_308533 < baseStart_308533 := by decide
  rcases family_descends (prefixWord ++ tailWord_308533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308537 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 2, 4]
def baseStart_308537 : Nat := 118140960795 + 308537 * 2 ^ 59
def prefixEnd_308537 : Nat := 4983230072969 + 3 ^ 40 * 308537 * 2
def baseEnd_308537 : Nat := 105618520464243054179047

theorem tailTrace_308537 : CollatzResearch.WordTrace tailWord_308537 prefixEnd_308537 105618520464243054179047 := by
  unfold tailWord_308537
  simp only [CollatzResearch.WordTrace]
  refine ⟨11253268883230617769531865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7502179255487078513021243 11253268883230617769531865)
  ·
    refine ⟨8439951662422963327148899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11253268883230617769531865 8439951662422963327148899)
    ·
      refine ⟨12659927493634444990723349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8439951662422963327148899 12659927493634444990723349)
      ·
        refine ⟨593434101264114608940157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12659927493634444990723349 593434101264114608940157)
        ·
          refine ⟨222537787974042978352559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 593434101264114608940157 222537787974042978352559)
          ·
            refine ⟨333806681961064467528839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222537787974042978352559 333806681961064467528839)
            ·
              refine ⟨500710022941596701293259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333806681961064467528839 500710022941596701293259)
              ·
                refine ⟨751065034412395051939889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500710022941596701293259 751065034412395051939889)
                ·
                  refine ⟨563298775809296288954917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 751065034412395051939889 563298775809296288954917)
                  ·
                    refine ⟨105618520464243054179047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 563298775809296288954917 105618520464243054179047)
                    ·
                      rfl

theorem cell22_308537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_308537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308537 prefixEnd_308537 := by exact prefixLift 308537
  have htrace : WordTrace (prefixWord ++ tailWord_308537) baseStart_308537 baseEnd_308537 := by
    simpa [prefixWord, tailWord_308537, baseEnd_308537] using wordTrace_append hprefix tailTrace_308537
  have hstable : (prefixWord ++ tailWord_308537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308537).length < 2 ^ (prefixWord ++ tailWord_308537).sum := by decide
  have hdescent : baseEnd_308537 < baseStart_308537 := by decide
  rcases family_descends (prefixWord ++ tailWord_308537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308561 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 4, 5]
def baseStart_308561 : Nat := 118140960795 + 308561 * 2 ^ 59
def prefixEnd_308561 : Nat := 4983230072969 + 3 ^ 40 * 308561 * 2
def baseEnd_308561 : Nat := 105626736154714991578973

theorem tailTrace_308561 : CollatzResearch.WordTrace tailWord_308561 prefixEnd_308561 105626736154714991578973 := by
  unfold tailWord_308561
  simp only [CollatzResearch.WordTrace]
  refine ⟨11254144235143669868405537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7502762823429113245603691 11254144235143669868405537)
  ·
    refine ⟨8440608176357752401304153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11254144235143669868405537 8440608176357752401304153)
    ·
      refine ⟨6330456132268314300978115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8440608176357752401304153 6330456132268314300978115)
      ·
        refine ⟨9495684198402471451467173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6330456132268314300978115 9495684198402471451467173)
        ·
          refine ⟨1780440787200463397150095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9495684198402471451467173 1780440787200463397150095)
          ·
            refine ⟨2670661180800695095725143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780440787200463397150095 2670661180800695095725143)
            ·
              refine ⟨4005991771201042643587715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670661180800695095725143 4005991771201042643587715)
              ·
                refine ⟨6008987656801563965381573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4005991771201042643587715 6008987656801563965381573)
                ·
                  refine ⟨1126685185650293243509045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6008987656801563965381573 1126685185650293243509045)
                  ·
                    refine ⟨105626736154714991578973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1126685185650293243509045 105626736154714991578973)
                    ·
                      rfl

theorem cell22_308561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_308561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308561 prefixEnd_308561 := by exact prefixLift 308561
  have htrace : WordTrace (prefixWord ++ tailWord_308561) baseStart_308561 baseEnd_308561 := by
    simpa [prefixWord, tailWord_308561, baseEnd_308561] using wordTrace_append hprefix tailTrace_308561
  have hstable : (prefixWord ++ tailWord_308561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308561).length < 2 ^ (prefixWord ++ tailWord_308561).sum := by decide
  have hdescent : baseEnd_308561 < baseStart_308561 := by decide
  rcases family_descends (prefixWord ++ tailWord_308561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308578 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_308578 : Nat := 118140960795 + 308578 * 2 ^ 59
def prefixEnd_308578 : Nat := 4983230072969 + 3 ^ 40 * 308578 * 2
def baseEnd_308578 : Nat := 105632555602132613903921

theorem tailTrace_308578 : CollatzResearch.WordTrace tailWord_308578 prefixEnd_308578 105632555602132613903921 := by
  unfold tailWord_308578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813691069020520442943597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7503176184054721181182925 2813691069020520442943597)
  ·
    refine ⟨1055134150882695166103849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2813691069020520442943597 1055134150882695166103849)
    ·
      refine ⟨791350613162021374577887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1055134150882695166103849 791350613162021374577887)
      ·
        refine ⟨1187025919743032061866831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791350613162021374577887 1187025919743032061866831)
        ·
          refine ⟨1780538879614548092800247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187025919743032061866831 1780538879614548092800247)
          ·
            refine ⟨2670808319421822139200371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780538879614548092800247 2670808319421822139200371)
            ·
              refine ⟨4006212479132733208800557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2670808319421822139200371 4006212479132733208800557)
              ·
                refine ⟨1502329679674774953300209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4006212479132733208800557 1502329679674774953300209)
                ·
                  refine ⟨1126747259756081214975157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1502329679674774953300209 1126747259756081214975157)
                  ·
                    refine ⟨105632555602132613903921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1126747259756081214975157 105632555602132613903921)
                    ·
                      rfl

theorem cell22_308578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_308578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308578 prefixEnd_308578 := by exact prefixLift 308578
  have htrace : WordTrace (prefixWord ++ tailWord_308578) baseStart_308578 baseEnd_308578 := by
    simpa [prefixWord, tailWord_308578, baseEnd_308578] using wordTrace_append hprefix tailTrace_308578
  have hstable : (prefixWord ++ tailWord_308578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308578).length < 2 ^ (prefixWord ++ tailWord_308578).sum := by decide
  have hdescent : baseEnd_308578 < baseStart_308578 := by decide
  rcases family_descends (prefixWord ++ tailWord_308578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308580 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 5]
def baseStart_308580 : Nat := 118140960795 + 308580 * 2 ^ 59
def prefixEnd_308580 : Nat := 4983230072969 + 3 ^ 40 * 308580 * 2
def baseEnd_308580 : Nat := 35211080081001758451305

theorem tailTrace_308580 : CollatzResearch.WordTrace tailWord_308580 prefixEnd_308580 35211080081001758451305 := by
  unfold tailWord_308580
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627418611037418056673597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7503224814716557408898129 5627418611037418056673597)
  ·
    refine ⟨2110281979139031771252599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5627418611037418056673597 2110281979139031771252599)
    ·
      refine ⟨3165422968708547656878899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2110281979139031771252599 3165422968708547656878899)
      ·
        refine ⟨4748134453062821485318349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3165422968708547656878899 4748134453062821485318349)
        ·
          refine ⟨1780550419898558056994381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4748134453062821485318349 1780550419898558056994381)
          ·
            refine ⟨667706407461959271372893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1780550419898558056994381 667706407461959271372893)
            ·
              refine ⟨250389902798234726764835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 667706407461959271372893 250389902798234726764835)
              ·
                refine ⟨375584854197352090147253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250389902798234726764835 375584854197352090147253)
                ·
                  refine ⟨35211080081001758451305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375584854197352090147253 35211080081001758451305)
                  ·
                    rfl

theorem cell22_308580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_308580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308580 prefixEnd_308580 := by exact prefixLift 308580
  have htrace : WordTrace (prefixWord ++ tailWord_308580) baseStart_308580 baseEnd_308580 := by
    simpa [prefixWord, tailWord_308580, baseEnd_308580] using wordTrace_append hprefix tailTrace_308580
  have hstable : (prefixWord ++ tailWord_308580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308580).length < 2 ^ (prefixWord ++ tailWord_308580).sum := by decide
  have hdescent : baseEnd_308580 < baseStart_308580 := by decide
  rcases family_descends (prefixWord ++ tailWord_308580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308591 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 6]
def baseStart_308591 : Nat := 118140960795 + 308591 * 2 ^ 59
def prefixEnd_308591 : Nat := 4983230072969 + 3 ^ 40 * 308591 * 2
def baseEnd_308591 : Nat := 35212335255934971109627

theorem tailTrace_308591 : CollatzResearch.WordTrace tailWord_308591 prefixEnd_308591 35212335255934971109627 := by
  unfold tailWord_308591
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255238425034984991997627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7503492283356656661331751 11255238425034984991997627)
  ·
    refine ⟨16882857637552477487996441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11255238425034984991997627 16882857637552477487996441)
    ·
      refine ⟨12662143228164358115997331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16882857637552477487996441 12662143228164358115997331)
      ·
        refine ⟨18993214842246537173995997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12662143228164358115997331 18993214842246537173995997)
        ·
          refine ⟨7122455565842451440248499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18993214842246537173995997 7122455565842451440248499)
          ·
            refine ⟨10683683348763677160372749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7122455565842451440248499 10683683348763677160372749)
            ·
              refine ⟨4006381255786378935139781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10683683348763677160372749 4006381255786378935139781)
              ·
                refine ⟨751196485459946050338709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4006381255786378935139781 751196485459946050338709)
                ·
                  refine ⟨35212335255934971109627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 751196485459946050338709 35212335255934971109627)
                  ·
                    rfl

theorem cell22_308591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 6].length) (baseStart_308591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308591 prefixEnd_308591 := by exact prefixLift 308591
  have htrace : WordTrace (prefixWord ++ tailWord_308591) baseStart_308591 baseEnd_308591 := by
    simpa [prefixWord, tailWord_308591, baseEnd_308591] using wordTrace_append hprefix tailTrace_308591
  have hstable : (prefixWord ++ tailWord_308591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308591).length < 2 ^ (prefixWord ++ tailWord_308591).sum := by decide
  have hdescent : baseEnd_308591 < baseStart_308591 := by decide
  rcases family_descends (prefixWord ++ tailWord_308591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308593 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 1, 4]
def baseStart_308593 : Nat := 118140960795 + 308593 * 2 ^ 59
def prefixEnd_308593 : Nat := 4983230072969 + 3 ^ 40 * 308593 * 2
def baseEnd_308593 : Nat := 105637690408677574778875

theorem tailTrace_308593 : CollatzResearch.WordTrace tailWord_308593 prefixEnd_308593 105637690408677574778875 := by
  unfold tailWord_308593
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255311371027739333570433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7503540914018492889046955 11255311371027739333570433)
  ·
    refine ⟨8441483528270804500177825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11255311371027739333570433 8441483528270804500177825)
    ·
      refine ⟨6331112646203103375133369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8441483528270804500177825 6331112646203103375133369)
      ·
        refine ⟨4748334484652327531350027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6331112646203103375133369 4748334484652327531350027)
        ·
          refine ⟨7122501726978491297025041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4748334484652327531350027 7122501726978491297025041)
          ·
            refine ⟨5341876295233868472768781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7122501726978491297025041 5341876295233868472768781)
            ·
              refine ⟨2003203610712700677288293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5341876295233868472768781 2003203610712700677288293)
              ·
                refine ⟨375600677008631376991555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2003203610712700677288293 375600677008631376991555)
                ·
                  refine ⟨563401015512947065487333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375600677008631376991555 563401015512947065487333)
                  ·
                    refine ⟨105637690408677574778875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 563401015512947065487333 105637690408677574778875)
                    ·
                      rfl

theorem cell22_308593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_308593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308593 prefixEnd_308593 := by exact prefixLift 308593
  have htrace : WordTrace (prefixWord ++ tailWord_308593) baseStart_308593 baseEnd_308593 := by
    simpa [prefixWord, tailWord_308593, baseEnd_308593] using wordTrace_append hprefix tailTrace_308593
  have hstable : (prefixWord ++ tailWord_308593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308593).length < 2 ^ (prefixWord ++ tailWord_308593).sum := by decide
  have hdescent : baseEnd_308593 < baseStart_308593 := by decide
  rcases family_descends (prefixWord ++ tailWord_308593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308640 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 2, 3]
def baseStart_308640 : Nat := 118140960795 + 308640 * 2 ^ 59
def prefixEnd_308640 : Nat := 4983230072969 + 3 ^ 40 * 308640 * 2
def baseEnd_308640 : Nat := 105653779469185118853731

theorem tailTrace_308640 : CollatzResearch.WordTrace tailWord_308640 prefixEnd_308640 105653779469185118853731 := by
  unfold tailWord_308640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628512800928733180265687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7504683734571644240354249 5628512800928733180265687)
  ·
    refine ⟨8442769201393099770398531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5628512800928733180265687 8442769201393099770398531)
    ·
      refine ⟨12664153802089649655597797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8442769201393099770398531 12664153802089649655597797)
      ·
        refine ⟨2374528837891809310424587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12664153802089649655597797 2374528837891809310424587)
        ·
          refine ⟨3561793256837713965636881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374528837891809310424587 3561793256837713965636881)
          ·
            refine ⟨2671344942628285474227661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3561793256837713965636881 2671344942628285474227661)
            ·
              refine ⟨1001754353485607052835373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2671344942628285474227661 1001754353485607052835373)
              ·
                refine ⟨375657882557102644813265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001754353485607052835373 375657882557102644813265)
                ·
                  refine ⟨281743411917826983609949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 375657882557102644813265 281743411917826983609949)
                  ·
                    refine ⟨105653779469185118853731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281743411917826983609949 105653779469185118853731)
                    ·
                      rfl

theorem cell22_308640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_308640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308640 prefixEnd_308640 := by exact prefixLift 308640
  have htrace : WordTrace (prefixWord ++ tailWord_308640) baseStart_308640 baseEnd_308640 := by
    simpa [prefixWord, tailWord_308640, baseEnd_308640] using wordTrace_append hprefix tailTrace_308640
  have hstable : (prefixWord ++ tailWord_308640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308640).length < 2 ^ (prefixWord ++ tailWord_308640).sum := by decide
  have hdescent : baseEnd_308640 < baseStart_308640 := by decide
  rcases family_descends (prefixWord ++ tailWord_308640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308865 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 1, 7]
def baseStart_308865 : Nat := 118140960795 + 308865 * 2 ^ 59
def prefixEnd_308865 : Nat := 4983230072969 + 3 ^ 40 * 308865 * 2
def baseEnd_308865 : Nat := 105730801567359531978041

theorem tailTrace_308865 : CollatzResearch.WordTrace tailWord_308865 prefixEnd_308865 105730801567359531978041 := by
  unfold tailWord_308865
  simp only [CollatzResearch.WordTrace]
  refine ⟨11265232026042329787472049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7510154684028219858314699 11265232026042329787472049)
  ·
    refine ⟨8448924019531747340604037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11265232026042329787472049 8448924019531747340604037)
    ·
      refine ⟨1584173253662202626363257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8448924019531747340604037 1584173253662202626363257)
      ·
        refine ⟨1188129940246651969772443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584173253662202626363257 1188129940246651969772443)
        ·
          refine ⟨1782194910369977954658665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188129940246651969772443 1782194910369977954658665)
          ·
            refine ⟨1336646182777483465993999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1782194910369977954658665 1336646182777483465993999)
            ·
              refine ⟨2004969274166225198990999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336646182777483465993999 2004969274166225198990999)
              ·
                refine ⟨3007453911249337798486499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2004969274166225198990999 3007453911249337798486499)
                ·
                  refine ⟨4511180866874006697729749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3007453911249337798486499 4511180866874006697729749)
                  ·
                    refine ⟨105730801567359531978041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4511180866874006697729749 105730801567359531978041)
                    ·
                      rfl

theorem cell22_308865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_308865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308865 prefixEnd_308865 := by exact prefixLift 308865
  have htrace : WordTrace (prefixWord ++ tailWord_308865) baseStart_308865 baseEnd_308865 := by
    simpa [prefixWord, tailWord_308865, baseEnd_308865] using wordTrace_append hprefix tailTrace_308865
  have hstable : (prefixWord ++ tailWord_308865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308865).length < 2 ^ (prefixWord ++ tailWord_308865).sum := by decide
  have hdescent : baseEnd_308865 < baseStart_308865 := by decide
  rcases family_descends (prefixWord ++ tailWord_308865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308912 : List Nat := [2, 1, 1, 1, 2, 1, 6, 4, 4]
def baseStart_308912 : Nat := 118140960795 + 308912 * 2 ^ 59
def prefixEnd_308912 : Nat := 4983230072969 + 3 ^ 40 * 308912 * 2
def baseEnd_308912 : Nat := 35248963542622358684299

theorem tailTrace_308912 : CollatzResearch.WordTrace tailWord_308912 prefixEnd_308912 35248963542622358684299 := by
  unfold tailWord_308912
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633473128436028407216495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7511297504581371209621993 5633473128436028407216495)
  ·
    refine ⟨8450209692654042610824743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5633473128436028407216495 8450209692654042610824743)
    ·
      refine ⟨12675314538981063916237115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8450209692654042610824743 12675314538981063916237115)
      ·
        refine ⟨19012971808471595874355673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12675314538981063916237115 19012971808471595874355673)
        ·
          refine ⟨14259728856353696905766755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19012971808471595874355673 14259728856353696905766755)
          ·
            refine ⟨21389593284530545358650133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14259728856353696905766755 21389593284530545358650133)
            ·
              refine ⟨1002637185212369313686725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21389593284530545358650133 1002637185212369313686725)
              ·
                refine ⟨187994472227319246316261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1002637185212369313686725 187994472227319246316261)
                ·
                  refine ⟨35248963542622358684299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187994472227319246316261 35248963542622358684299)
                  ·
                    rfl

theorem cell22_308912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_308912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308912 prefixEnd_308912 := by exact prefixLift 308912
  have htrace : WordTrace (prefixWord ++ tailWord_308912) baseStart_308912 baseEnd_308912 := by
    simpa [prefixWord, tailWord_308912, baseEnd_308912] using wordTrace_append hprefix tailTrace_308912
  have hstable : (prefixWord ++ tailWord_308912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308912).length < 2 ^ (prefixWord ++ tailWord_308912).sum := by decide
  have hdescent : baseEnd_308912 < baseStart_308912 := by decide
  rcases family_descends (prefixWord ++ tailWord_308912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308925 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_308925 : Nat := 118140960795 + 308925 * 2 ^ 59
def prefixEnd_308925 : Nat := 4983230072969 + 3 ^ 40 * 308925 * 2
def baseEnd_308925 : Nat := 105751340793539375477857

theorem tailTrace_308925 : CollatzResearch.WordTrace tailWord_308925 prefixEnd_308925 105751340793539375477857 := by
  unfold tailWord_308925
  simp only [CollatzResearch.WordTrace]
  refine ⟨11267420405824960034656229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7511613603883306689770819 11267420405824960034656229)
  ·
    refine ⟨2112641326092180006498043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11267420405824960034656229 2112641326092180006498043)
    ·
      refine ⟨3168961989138270009747065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112641326092180006498043 3168961989138270009747065)
      ·
        refine ⟨2376721491853702507310299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3168961989138270009747065 2376721491853702507310299)
        ·
          refine ⟨3565082237780553760965449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2376721491853702507310299 3565082237780553760965449)
          ·
            refine ⟨2673811678335415320724087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3565082237780553760965449 2673811678335415320724087)
            ·
              refine ⟨4010717517503122981086131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673811678335415320724087 4010717517503122981086131)
              ·
                refine ⟨6016076276254684471629197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4010717517503122981086131 6016076276254684471629197)
                ·
                  refine ⟨2256028603595506676860949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6016076276254684471629197 2256028603595506676860949)
                  ·
                    refine ⟨105751340793539375477857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2256028603595506676860949 105751340793539375477857)
                    ·
                      rfl

theorem cell22_308925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_308925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308925 prefixEnd_308925 := by exact prefixLift 308925
  have htrace : WordTrace (prefixWord ++ tailWord_308925) baseStart_308925 baseEnd_308925 := by
    simpa [prefixWord, tailWord_308925, baseEnd_308925] using wordTrace_append hprefix tailTrace_308925
  have hstable : (prefixWord ++ tailWord_308925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308925).length < 2 ^ (prefixWord ++ tailWord_308925).sum := by decide
  have hdescent : baseEnd_308925 < baseStart_308925 := by decide
  rcases family_descends (prefixWord ++ tailWord_308925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308942 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_308942 : Nat := 118140960795 + 308942 * 2 ^ 59
def prefixEnd_308942 : Nat := 4983230072969 + 3 ^ 40 * 308942 * 2
def baseEnd_308942 : Nat := 105757160240956997802805

theorem tailTrace_308942 : CollatzResearch.WordTrace tailWord_308942 prefixEnd_308942 105757160240956997802805 := by
  unfold tailWord_308942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1408505055845421492253135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7512026964508914625350053 1408505055845421492253135)
  ·
    refine ⟨2112757583768132238379703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1408505055845421492253135 2112757583768132238379703)
    ·
      refine ⟨3169136375652198357569555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112757583768132238379703 3169136375652198357569555)
      ·
        refine ⟨4753704563478297536354333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169136375652198357569555 4753704563478297536354333)
        ·
          refine ⟨1782639211304361576132875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4753704563478297536354333 1782639211304361576132875)
          ·
            refine ⟨2673958816956542364199313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782639211304361576132875 2673958816956542364199313)
            ·
              refine ⟨2005469112717406773149485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2673958816956542364199313 2005469112717406773149485)
              ·
                refine ⟨752050917269027539931057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2005469112717406773149485 752050917269027539931057)
                ·
                  refine ⟨564038187951770654948293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 752050917269027539931057 564038187951770654948293)
                  ·
                    refine ⟨105757160240956997802805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 564038187951770654948293 105757160240956997802805)
                    ·
                      rfl

theorem cell22_308942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_308942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308942 prefixEnd_308942 := by exact prefixLift 308942
  have htrace : WordTrace (prefixWord ++ tailWord_308942) baseStart_308942 baseEnd_308942 := by
    simpa [prefixWord, tailWord_308942, baseEnd_308942] using wordTrace_append hprefix tailTrace_308942
  have hstable : (prefixWord ++ tailWord_308942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308942).length < 2 ^ (prefixWord ++ tailWord_308942).sum := by decide
  have hdescent : baseEnd_308942 < baseStart_308942 := by decide
  rcases family_descends (prefixWord ++ tailWord_308942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308946 : List Nat := [3, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_308946 : Nat := 118140960795 + 308946 * 2 ^ 59
def prefixEnd_308946 : Nat := 4983230072969 + 3 ^ 40 * 308946 * 2
def baseEnd_308946 : Nat := 35252843174234106900931

theorem tailTrace_308946 : CollatzResearch.WordTrace tailWord_308946 prefixEnd_308946 35252843174234106900931 := by
  unfold tailWord_308946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2817046584687220155292673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7512124225832587080780461 2817046584687220155292673)
  ·
    refine ⟨2112784938515415116469505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2817046584687220155292673 2112784938515415116469505)
    ·
      refine ⟨1584588703886561337352129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2112784938515415116469505 1584588703886561337352129)
      ·
        refine ⟨1188441527914921003014097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1584588703886561337352129 1188441527914921003014097)
        ·
          refine ⟨891331145936190752260573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1188441527914921003014097 891331145936190752260573)
          ·
            refine ⟨334249179726071532097715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 891331145936190752260573 334249179726071532097715)
            ·
              refine ⟨501373769589107298146573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334249179726071532097715 501373769589107298146573)
              ·
                refine ⟨188015163595915236804965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501373769589107298146573 188015163595915236804965)
                ·
                  refine ⟨35252843174234106900931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188015163595915236804965 35252843174234106900931)
                  ·
                    rfl

theorem cell22_308946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_308946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_308946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_308946 prefixEnd_308946 := by exact prefixLift 308946
  have htrace : WordTrace (prefixWord ++ tailWord_308946) baseStart_308946 baseEnd_308946 := by
    simpa [prefixWord, tailWord_308946, baseEnd_308946] using wordTrace_append hprefix tailTrace_308946
  have hstable : (prefixWord ++ tailWord_308946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308946).length < 2 ^ (prefixWord ++ tailWord_308946).sum := by decide
  have hdescent : baseEnd_308946 < baseStart_308946 := by decide
  rcases family_descends (prefixWord ++ tailWord_308946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309064 : List Nat := [2, 1, 3, 1, 1, 4, 1, 5, 4]
def baseStart_309064 : Nat := 118140960795 + 309064 * 2 ^ 59
def prefixEnd_309064 : Nat := 4983230072969 + 3 ^ 40 * 309064 * 2
def baseEnd_309064 : Nat := 35266307778063115417477

theorem tailTrace_309064 : CollatzResearch.WordTrace tailWord_309064 prefixEnd_309064 35266307778063115417477 := by
  unfold tailWord_309064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5636245076160693386983123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7514993434880924515977497 5636245076160693386983123)
  ·
    refine ⟨8454367614241040080474685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5636245076160693386983123 8454367614241040080474685)
    ·
      refine ⟨3170387855340390030178007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8454367614241040080474685 3170387855340390030178007)
      ·
        refine ⟨4755581783010585045267011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3170387855340390030178007 4755581783010585045267011)
        ·
          refine ⟨7133372674515877567900517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4755581783010585045267011 7133372674515877567900517)
          ·
            refine ⟨1337507376471727043981347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7133372674515877567900517 1337507376471727043981347)
            ·
              refine ⟨2006261064707590565972021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337507376471727043981347 2006261064707590565972021)
              ·
                refine ⟨188086974816336615559877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2006261064707590565972021 188086974816336615559877)
                ·
                  refine ⟨35266307778063115417477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188086974816336615559877 35266307778063115417477)
                  ·
                    rfl

theorem cell22_309064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_309064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309064 prefixEnd_309064 := by exact prefixLift 309064
  have htrace : WordTrace (prefixWord ++ tailWord_309064) baseStart_309064 baseEnd_309064 := by
    simpa [prefixWord, tailWord_309064, baseEnd_309064] using wordTrace_append hprefix tailTrace_309064
  have hstable : (prefixWord ++ tailWord_309064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309064).length < 2 ^ (prefixWord ++ tailWord_309064).sum := by decide
  have hdescent : baseEnd_309064 < baseStart_309064 := by decide
  rcases family_descends (prefixWord ++ tailWord_309064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309124 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_309124 : Nat := 118140960795 + 309124 * 2 ^ 59
def prefixEnd_309124 : Nat := 4983230072969 + 3 ^ 40 * 309124 * 2
def baseEnd_309124 : Nat := 105819462560369189752247

theorem tailTrace_309124 : CollatzResearch.WordTrace tailWord_309124 prefixEnd_309124 105819462560369189752247 := by
  unfold tailWord_309124
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637339266052008510575213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7516452354736011347433617 5637339266052008510575213)
  ·
    refine ⟨2114002224769503191465705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5637339266052008510575213 2114002224769503191465705)
    ·
      refine ⟨1585501668577127393599279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2114002224769503191465705 1585501668577127393599279)
      ·
        refine ⟨2378252502865691090398919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585501668577127393599279 2378252502865691090398919)
        ·
          refine ⟨3567378754298536635598379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378252502865691090398919 3567378754298536635598379)
          ·
            refine ⟨5351068131447804953397569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567378754298536635598379 5351068131447804953397569)
            ·
              refine ⟨4013301098585853715048177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5351068131447804953397569 4013301098585853715048177)
              ·
                refine ⟨3009975823939390286286133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4013301098585853715048177 3009975823939390286286133)
                ·
                  refine ⟨282185233494317839339325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3009975823939390286286133 282185233494317839339325)
                  ·
                    refine ⟨105819462560369189752247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282185233494317839339325 105819462560369189752247)
                    ·
                      rfl

theorem cell22_309124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_309124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309124 prefixEnd_309124 := by exact prefixLift 309124
  have htrace : WordTrace (prefixWord ++ tailWord_309124) baseStart_309124 baseEnd_309124 := by
    simpa [prefixWord, tailWord_309124, baseEnd_309124] using wordTrace_append hprefix tailTrace_309124
  have hstable : (prefixWord ++ tailWord_309124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309124).length < 2 ^ (prefixWord ++ tailWord_309124).sum := by decide
  have hdescent : baseEnd_309124 < baseStart_309124 := by decide
  rcases family_descends (prefixWord ++ tailWord_309124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309137 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 7]
def baseStart_309137 : Nat := 118140960795 + 309137 * 2 ^ 59
def prefixEnd_309137 : Nat := 4983230072969 + 3 ^ 40 * 309137 * 2
def baseEnd_309137 : Nat := 35274637575347163059069

theorem tailTrace_309137 : CollatzResearch.WordTrace tailWord_309137 prefixEnd_309137 35274637575347163059069 := by
  unfold tailWord_309137
  simp only [CollatzResearch.WordTrace]
  refine ⟨11275152681056920241373665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7516768454037946827582443 11275152681056920241373665)
  ·
    refine ⟨8456364510792690181030249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11275152681056920241373665 8456364510792690181030249)
    ·
      refine ⟨6342273383094517635772687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8456364510792690181030249 6342273383094517635772687)
      ·
        refine ⟨9513410074641776453659031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6342273383094517635772687 9513410074641776453659031)
        ·
          refine ⟨14270115111962664680488547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9513410074641776453659031 14270115111962664680488547)
          ·
            refine ⟨21405172667943997020732821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14270115111962664680488547 21405172667943997020732821)
            ·
              refine ⟨1003367468809874860346851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21405172667943997020732821 1003367468809874860346851)
              ·
                refine ⟨1505051203214812290520277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1003367468809874860346851 1505051203214812290520277)
                ·
                  refine ⟨35274637575347163059069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1505051203214812290520277 35274637575347163059069)
                  ·
                    rfl

theorem cell22_309137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_309137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309137 prefixEnd_309137 := by exact prefixLift 309137
  have htrace : WordTrace (prefixWord ++ tailWord_309137) baseStart_309137 baseEnd_309137 := by
    simpa [prefixWord, tailWord_309137, baseEnd_309137] using wordTrace_append hprefix tailTrace_309137
  have hstable : (prefixWord ++ tailWord_309137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309137).length < 2 ^ (prefixWord ++ tailWord_309137).sum := by decide
  have hdescent : baseEnd_309137 < baseStart_309137 := by decide
  rcases family_descends (prefixWord ++ tailWord_309137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309152 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_309152 : Nat := 118140960795 + 309152 * 2 ^ 59
def prefixEnd_309152 : Nat := 4983230072969 + 3 ^ 40 * 309152 * 2
def baseEnd_309152 : Nat := 105829047532586450052161

theorem tailTrace_309152 : CollatzResearch.WordTrace tailWord_309152 prefixEnd_309152 105829047532586450052161 := by
  unfold tailWord_309152
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637849888001288901584855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7517133184001718535446473 5637849888001288901584855)
  ·
    refine ⟨8456774832001933352377283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5637849888001288901584855 8456774832001933352377283)
    ·
      refine ⟨12685162248002900028565925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8456774832001933352377283 12685162248002900028565925)
      ·
        refine ⟨2378467921500543755356111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12685162248002900028565925 2378467921500543755356111)
        ·
          refine ⟨3567701882250815633034167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378467921500543755356111 3567701882250815633034167)
          ·
            refine ⟨5351552823376223449551251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567701882250815633034167 5351552823376223449551251)
            ·
              refine ⟨8027329235064335174326877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5351552823376223449551251 8027329235064335174326877)
              ·
                refine ⟨3010248463149125690372579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8027329235064335174326877 3010248463149125690372579)
                ·
                  refine ⟨4515372694723688535558869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3010248463149125690372579 4515372694723688535558869)
                  ·
                    refine ⟨105829047532586450052161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4515372694723688535558869 105829047532586450052161)
                    ·
                      rfl

theorem cell22_309152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_309152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309152 prefixEnd_309152 := by exact prefixLift 309152
  have htrace : WordTrace (prefixWord ++ tailWord_309152) baseStart_309152 baseEnd_309152 := by
    simpa [prefixWord, tailWord_309152, baseEnd_309152] using wordTrace_append hprefix tailTrace_309152
  have hstable : (prefixWord ++ tailWord_309152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309152).length < 2 ^ (prefixWord ++ tailWord_309152).sum := by decide
  have hdescent : baseEnd_309152 < baseStart_309152 := by decide
  rcases family_descends (prefixWord ++ tailWord_309152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309227 : List Nat := [1, 1, 1, 1, 2, 3, 1, 12]
def baseStart_309227 : Nat := 118140960795 + 309227 * 2 ^ 59
def prefixEnd_309227 : Nat := 4983230072969 + 3 ^ 40 * 309227 * 2
def baseEnd_309227 : Nat := 11761635729479028269659

theorem tailTrace_309227 : CollatzResearch.WordTrace tailWord_309227 prefixEnd_309227 11761635729479028269659 := by
  unfold tailWord_309227
  simp only [CollatzResearch.WordTrace]
  refine ⟨11278435250730865612149935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7518956833820577074766623 11278435250730865612149935)
  ·
    refine ⟨16917652876096298418224903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11278435250730865612149935 16917652876096298418224903)
    ·
      refine ⟨25376479314144447627337355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16917652876096298418224903 25376479314144447627337355)
      ·
        refine ⟨38064718971216671441006033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25376479314144447627337355 38064718971216671441006033)
        ·
          refine ⟨28548539228412503580754525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38064718971216671441006033 28548539228412503580754525)
          ·
            refine ⟨10705702210654688842782947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28548539228412503580754525 10705702210654688842782947)
            ·
              refine ⟨16058553315982033264174421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10705702210654688842782947 16058553315982033264174421)
              ·
                refine ⟨11761635729479028269659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 16058553315982033264174421 11761635729479028269659)
                ·
                  rfl

theorem cell22_309227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 12].length) (baseStart_309227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309227 prefixEnd_309227 := by exact prefixLift 309227
  have htrace : WordTrace (prefixWord ++ tailWord_309227) baseStart_309227 baseEnd_309227 := by
    simpa [prefixWord, tailWord_309227, baseEnd_309227] using wordTrace_append hprefix tailTrace_309227
  have hstable : (prefixWord ++ tailWord_309227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309227).length < 2 ^ (prefixWord ++ tailWord_309227).sum := by decide
  have hdescent : baseEnd_309227 < baseStart_309227 := by decide
  rcases family_descends (prefixWord ++ tailWord_309227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309233 : List Nat := [1, 2, 2, 2, 5, 1, 2, 3, 4]
def baseStart_309233 : Nat := 118140960795 + 309233 * 2 ^ 59
def prefixEnd_309233 : Nat := 4983230072969 + 3 ^ 40 * 309233 * 2
def baseEnd_309233 : Nat := 35285591829309746258971

theorem tailTrace_309233 : CollatzResearch.WordTrace tailWord_309233 prefixEnd_309233 35285591829309746258971 := by
  unfold tailWord_309233
  simp only [CollatzResearch.WordTrace]
  refine ⟨11278654088709128636868353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7519102725806085757912235 11278654088709128636868353)
  ·
    refine ⟨8458990566531846477651265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11278654088709128636868353 8458990566531846477651265)
    ·
      refine ⟨6344242924898884858238449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8458990566531846477651265 6344242924898884858238449)
      ·
        refine ⟨4758182193674163643678837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6344242924898884858238449 4758182193674163643678837)
        ·
          refine ⟨446079580656952841594891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4758182193674163643678837 446079580656952841594891)
          ·
            refine ⟨669119370985429262392337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446079580656952841594891 669119370985429262392337)
            ·
              refine ⟨501839528239071946794253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669119370985429262392337 501839528239071946794253)
              ·
                refine ⟨188189823089651980047845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501839528239071946794253 188189823089651980047845)
                ·
                  refine ⟨35285591829309746258971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188189823089651980047845 35285591829309746258971)
                  ·
                    rfl

theorem cell22_309233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_309233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309233 prefixEnd_309233 := by exact prefixLift 309233
  have htrace : WordTrace (prefixWord ++ tailWord_309233) baseStart_309233 baseEnd_309233 := by
    simpa [prefixWord, tailWord_309233, baseEnd_309233] using wordTrace_append hprefix tailTrace_309233
  have hstable : (prefixWord ++ tailWord_309233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309233).length < 2 ^ (prefixWord ++ tailWord_309233).sum := by decide
  have hdescent : baseEnd_309233 < baseStart_309233 := by decide
  rcases family_descends (prefixWord ++ tailWord_309233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309336 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_309336 : Nat := 118140960795 + 309336 * 2 ^ 59
def prefixEnd_309336 : Nat := 4983230072969 + 3 ^ 40 * 309336 * 2
def baseEnd_309336 : Nat := 105892034492871303451597

theorem tailTrace_309336 : CollatzResearch.WordTrace tailWord_309336 prefixEnd_309336 105892034492871303451597 := by
  unfold tailWord_309336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641205403667988613933931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7521607204890651485245241 5641205403667988613933931)
  ·
    refine ⟨8461808105501982920900897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5641205403667988613933931 8461808105501982920900897)
    ·
      refine ⟨6346356079126487190675673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8461808105501982920900897 6346356079126487190675673)
      ·
        refine ⟨4759767059344865393006755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6346356079126487190675673 4759767059344865393006755)
        ·
          refine ⟨7139650589017298089510133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4759767059344865393006755 7139650589017298089510133)
          ·
            refine ⟨669342242720371695891575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7139650589017298089510133 669342242720371695891575)
            ·
              refine ⟨1004013364080557543837363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669342242720371695891575 1004013364080557543837363)
              ·
                refine ⟨1506020046120836315756045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004013364080557543837363 1506020046120836315756045)
                ·
                  refine ⟨564757517295313618408517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1506020046120836315756045 564757517295313618408517)
                  ·
                    refine ⟨105892034492871303451597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 564757517295313618408517 105892034492871303451597)
                    ·
                      rfl

theorem cell22_309336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_309336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309336 prefixEnd_309336 := by exact prefixLift 309336
  have htrace : WordTrace (prefixWord ++ tailWord_309336) baseStart_309336 baseEnd_309336 := by
    simpa [prefixWord, tailWord_309336, baseEnd_309336] using wordTrace_append hprefix tailTrace_309336
  have hstable : (prefixWord ++ tailWord_309336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309336).length < 2 ^ (prefixWord ++ tailWord_309336).sum := by decide
  have hdescent : baseEnd_309336 < baseStart_309336 := by decide
  rcases family_descends (prefixWord ++ tailWord_309336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309353 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 1, 4]
def baseStart_309353 : Nat := 118140960795 + 309353 * 2 ^ 59
def prefixEnd_309353 : Nat := 4983230072969 + 3 ^ 40 * 309353 * 2
def baseEnd_309353 : Nat := 105897853940288925776545

theorem tailTrace_309353 : CollatzResearch.WordTrace tailWord_309353 prefixEnd_309353 105897853940288925776545 := by
  unfold tailWord_309353
  simp only [CollatzResearch.WordTrace]
  refine ⟨11283030848274389131236713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7522020565516259420824475 11283030848274389131236713)
  ·
    refine ⟨8462273136205791848427535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11283030848274389131236713 8462273136205791848427535)
    ·
      refine ⟨12693409704308687772641303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8462273136205791848427535 12693409704308687772641303)
      ·
        refine ⟨19040114556463031658961955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12693409704308687772641303 19040114556463031658961955)
        ·
          refine ⟨28560171834694547488442933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19040114556463031658961955 28560171834694547488442933)
          ·
            refine ⟨2677516109502613827041525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28560171834694547488442933 2677516109502613827041525)
            ·
              refine ⟨251017135265870046285143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2677516109502613827041525 251017135265870046285143)
              ·
                refine ⟨376525702898805069427715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251017135265870046285143 376525702898805069427715)
                ·
                  refine ⟨564788554348207604141573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376525702898805069427715 564788554348207604141573)
                  ·
                    refine ⟨105897853940288925776545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 564788554348207604141573 105897853940288925776545)
                    ·
                      rfl

theorem cell22_309353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 1, 4].length) (baseStart_309353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309353 prefixEnd_309353 := by exact prefixLift 309353
  have htrace : WordTrace (prefixWord ++ tailWord_309353) baseStart_309353 baseEnd_309353 := by
    simpa [prefixWord, tailWord_309353, baseEnd_309353] using wordTrace_append hprefix tailTrace_309353
  have hstable : (prefixWord ++ tailWord_309353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309353).length < 2 ^ (prefixWord ++ tailWord_309353).sum := by decide
  have hdescent : baseEnd_309353 < baseStart_309353 := by decide
  rcases family_descends (prefixWord ++ tailWord_309353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309383 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 2, 3]
def baseStart_309383 : Nat := 118140960795 + 309383 * 2 ^ 59
def prefixEnd_309383 : Nat := 4983230072969 + 3 ^ 40 * 309383 * 2
def baseEnd_309383 : Nat := 105908123553378847526453

theorem tailTrace_309383 : CollatzResearch.WordTrace tailWord_309383 prefixEnd_309383 105908123553378847526453 := by
  unfold tailWord_309383
  simp only [CollatzResearch.WordTrace]
  refine ⟨11284125038165704254828803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7522750025443802836552535 11284125038165704254828803)
  ·
    refine ⟨16926187557248556382243205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11284125038165704254828803 16926187557248556382243205)
    ·
      refine ⟨3173660166984104321670601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16926187557248556382243205 3173660166984104321670601)
      ·
        refine ⟨2380245125238078241252951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3173660166984104321670601 2380245125238078241252951)
        ·
          refine ⟨3570367687857117361879427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2380245125238078241252951 3570367687857117361879427)
          ·
            refine ⟨5355551531785676042819141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3570367687857117361879427 5355551531785676042819141)
            ·
              refine ⟨1004165912209814258028589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5355551531785676042819141 1004165912209814258028589)
              ·
                refine ⟨376562217078680346760721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1004165912209814258028589 376562217078680346760721)
                ·
                  refine ⟨282421662809010260070541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376562217078680346760721 282421662809010260070541)
                  ·
                    refine ⟨105908123553378847526453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282421662809010260070541 105908123553378847526453)
                    ·
                      rfl

theorem cell22_309383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_309383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309383 prefixEnd_309383 := by exact prefixLift 309383
  have htrace : WordTrace (prefixWord ++ tailWord_309383) baseStart_309383 baseEnd_309383 := by
    simpa [prefixWord, tailWord_309383, baseEnd_309383] using wordTrace_append hprefix tailTrace_309383
  have hstable : (prefixWord ++ tailWord_309383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309383).length < 2 ^ (prefixWord ++ tailWord_309383).sum := by decide
  have hdescent : baseEnd_309383 < baseStart_309383 := by decide
  rcases family_descends (prefixWord ++ tailWord_309383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309471 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 5, 4]
def baseStart_309471 : Nat := 118140960795 + 309471 * 2 ^ 59
def prefixEnd_309471 : Nat := 4983230072969 + 3 ^ 40 * 309471 * 2
def baseEnd_309471 : Nat := 105938247751775951326183

theorem tailTrace_309471 : CollatzResearch.WordTrace tailWord_309471 prefixEnd_309471 105938247751775951326183 := by
  unfold tailWord_309471
  simp only [CollatzResearch.WordTrace]
  refine ⟨11287334661846895284032267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7524889774564596856021511 11287334661846895284032267)
  ·
    refine ⟨16931001992770342926048401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11287334661846895284032267 16931001992770342926048401)
    ·
      refine ⟨12698251494577757194536301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16931001992770342926048401 12698251494577757194536301)
      ·
        refine ⟨4761844310466658947951113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12698251494577757194536301 4761844310466658947951113)
        ·
          refine ⟨3571383232849994210963335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4761844310466658947951113 3571383232849994210963335)
          ·
            refine ⟨5357074849274991316445003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571383232849994210963335 5357074849274991316445003)
            ·
              refine ⟨8035612273912486974667505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5357074849274991316445003 8035612273912486974667505)
              ·
                refine ⟨6026709205434365231000629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8035612273912486974667505 6026709205434365231000629)
                ·
                  refine ⟨565003988009471740406309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6026709205434365231000629 565003988009471740406309)
                  ·
                    refine ⟨105938247751775951326183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 565003988009471740406309 105938247751775951326183)
                    ·
                      rfl

theorem cell22_309471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_309471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309471 prefixEnd_309471 := by exact prefixLift 309471
  have htrace : WordTrace (prefixWord ++ tailWord_309471) baseStart_309471 baseEnd_309471 := by
    simpa [prefixWord, tailWord_309471, baseEnd_309471] using wordTrace_append hprefix tailTrace_309471
  have hstable : (prefixWord ++ tailWord_309471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309471).length < 2 ^ (prefixWord ++ tailWord_309471).sum := by decide
  have hdescent : baseEnd_309471 < baseStart_309471 := by decide
  rcases family_descends (prefixWord ++ tailWord_309471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309479 : List Nat := [1, 1, 5, 3, 1, 2, 3, 2, 1, 3]
def baseStart_309479 : Nat := 118140960795 + 309479 * 2 ^ 59
def prefixEnd_309479 : Nat := 4983230072969 + 3 ^ 40 * 309479 * 2
def baseEnd_309479 : Nat := 105940986315266597126159

theorem tailTrace_309479 : CollatzResearch.WordTrace tailWord_309479 prefixEnd_309479 105940986315266597126159 := by
  unfold tailWord_309479
  simp only [CollatzResearch.WordTrace]
  refine ⟨11287626445817912650323491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7525084297211941766882327 11287626445817912650323491)
  ·
    refine ⟨16931439668726868975485237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11287626445817912650323491 16931439668726868975485237)
    ·
      refine ⟨1587322468943143966451741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16931439668726868975485237 1587322468943143966451741)
      ·
        refine ⟨595245925853678987419403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1587322468943143966451741 595245925853678987419403)
        ·
          refine ⟨892868888780518481129105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595245925853678987419403 892868888780518481129105)
          ·
            refine ⟨669651666585388860846829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892868888780518481129105 669651666585388860846829)
            ·
              refine ⟨251119374969520822817561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 669651666585388860846829 251119374969520822817561)
              ·
                refine ⟨188339531227140617113171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251119374969520822817561 188339531227140617113171)
                ·
                  refine ⟨282509296840710925669757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188339531227140617113171 282509296840710925669757)
                  ·
                    refine ⟨105940986315266597126159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282509296840710925669757 105940986315266597126159)
                    ·
                      rfl

theorem cell22_309479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_309479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309479 prefixEnd_309479 := by exact prefixLift 309479
  have htrace : WordTrace (prefixWord ++ tailWord_309479) baseStart_309479 baseEnd_309479 := by
    simpa [prefixWord, tailWord_309479, baseEnd_309479] using wordTrace_append hprefix tailTrace_309479
  have hstable : (prefixWord ++ tailWord_309479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309479).length < 2 ^ (prefixWord ++ tailWord_309479).sum := by decide
  have hdescent : baseEnd_309479 < baseStart_309479 := by decide
  rcases family_descends (prefixWord ++ tailWord_309479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309501 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_309501 : Nat := 118140960795 + 309501 * 2 ^ 59
def prefixEnd_309501 : Nat := 4983230072969 + 3 ^ 40 * 309501 * 2
def baseEnd_309501 : Nat := 105948517364865873076091

theorem tailTrace_309501 : CollatzResearch.WordTrace tailWord_309501 prefixEnd_309501 105948517364865873076091 := by
  unfold tailWord_309501
  simp only [CollatzResearch.WordTrace]
  refine ⟨11288428851738210407624357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7525619234492140271749571 11288428851738210407624357)
  ·
    refine ⟨2116580409700914451429567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11288428851738210407624357 2116580409700914451429567)
    ·
      refine ⟨3174870614551371677144351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2116580409700914451429567 3174870614551371677144351)
      ·
        refine ⟨4762305921827057515716527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3174870614551371677144351 4762305921827057515716527)
        ·
          refine ⟨7143458882740586273574791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4762305921827057515716527 7143458882740586273574791)
          ·
            refine ⟨10715188324110879410362187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7143458882740586273574791 10715188324110879410362187)
            ·
              refine ⟨16072782486166319115543281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10715188324110879410362187 16072782486166319115543281)
              ·
                refine ⟨12054586864624739336657461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16072782486166319115543281 12054586864624739336657461)
                ·
                  refine ⟨1130117518558569312811637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12054586864624739336657461 1130117518558569312811637)
                  ·
                    refine ⟨105948517364865873076091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1130117518558569312811637 105948517364865873076091)
                    ·
                      rfl

theorem cell22_309501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_309501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309501 prefixEnd_309501 := by exact prefixLift 309501
  have htrace : WordTrace (prefixWord ++ tailWord_309501) baseStart_309501 baseEnd_309501 := by
    simpa [prefixWord, tailWord_309501, baseEnd_309501] using wordTrace_append hprefix tailTrace_309501
  have hstable : (prefixWord ++ tailWord_309501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309501).length < 2 ^ (prefixWord ++ tailWord_309501).sum := by decide
  have hdescent : baseEnd_309501 < baseStart_309501 := by decide
  rcases family_descends (prefixWord ++ tailWord_309501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309518 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_309518 : Nat := 118140960795 + 309518 * 2 ^ 59
def prefixEnd_309518 : Nat := 4983230072969 + 3 ^ 40 * 309518 * 2
def baseEnd_309518 : Nat := 105954336812283495401039

theorem tailTrace_309518 : CollatzResearch.WordTrace tailWord_309518 prefixEnd_309518 105954336812283495401039 := by
  unfold tailWord_309518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411131111584577788874151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7526032595117748207328805 1411131111584577788874151)
  ·
    refine ⟨2116696667376866683311227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1411131111584577788874151 2116696667376866683311227)
    ·
      refine ⟨3175045001065300024966841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2116696667376866683311227 3175045001065300024966841)
      ·
        refine ⟨2381283750798975018725131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3175045001065300024966841 2381283750798975018725131)
        ·
          refine ⟨3571925626198462528087697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381283750798975018725131 3571925626198462528087697)
          ·
            refine ⟨2678944219648846896065773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3571925626198462528087697 2678944219648846896065773)
            ·
              refine ⟨1004604082368317586024665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2678944219648846896065773 1004604082368317586024665)
              ·
                refine ⟨753453061776238189518499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004604082368317586024665 753453061776238189518499)
                ·
                  refine ⟨1130179592664357284277749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 753453061776238189518499 1130179592664357284277749)
                  ·
                    refine ⟨105954336812283495401039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1130179592664357284277749 105954336812283495401039)
                    ·
                      rfl

theorem cell22_309518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_309518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309518 prefixEnd_309518 := by exact prefixLift 309518
  have htrace : WordTrace (prefixWord ++ tailWord_309518) baseStart_309518 baseEnd_309518 := by
    simpa [prefixWord, tailWord_309518, baseEnd_309518] using wordTrace_append hprefix tailTrace_309518
  have hstable : (prefixWord ++ tailWord_309518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309518).length < 2 ^ (prefixWord ++ tailWord_309518).sum := by decide
  have hdescent : baseEnd_309518 < baseStart_309518 := by decide
  rcases family_descends (prefixWord ++ tailWord_309518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309535 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 2, 3]
def baseStart_309535 : Nat := 118140960795 + 309535 * 2 ^ 59
def prefixEnd_309535 : Nat := 4983230072969 + 3 ^ 40 * 309535 * 2
def baseEnd_309535 : Nat := 105960156259701117725987

theorem tailTrace_309535 : CollatzResearch.WordTrace tailWord_309535 prefixEnd_309535 105960156259701117725987 := by
  unfold tailWord_309535
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289668933615034214362059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7526445955743356142908039 11289668933615034214362059)
  ·
    refine ⟨16934503400422551321543089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11289668933615034214362059 16934503400422551321543089)
    ·
      refine ⟨12700877550316913491157317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16934503400422551321543089 12700877550316913491157317)
      ·
        refine ⟨2381414540684421279591997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12700877550316913491157317 2381414540684421279591997)
        ·
          refine ⟨893030452756657979846999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2381414540684421279591997 893030452756657979846999)
          ·
            refine ⟨1339545679134986969770499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893030452756657979846999 1339545679134986969770499)
            ·
              refine ⟨2009318518702480454655749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1339545679134986969770499 2009318518702480454655749)
              ·
                refine ⟨376747222256715085247953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2009318518702480454655749 376747222256715085247953)
                ·
                  refine ⟨282560416692536313935965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376747222256715085247953 282560416692536313935965)
                  ·
                    refine ⟨105960156259701117725987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282560416692536313935965 105960156259701117725987)
                    ·
                      rfl

theorem cell22_309535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_309535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309535 prefixEnd_309535 := by exact prefixLift 309535
  have htrace : WordTrace (prefixWord ++ tailWord_309535) baseStart_309535 baseEnd_309535 := by
    simpa [prefixWord, tailWord_309535, baseEnd_309535] using wordTrace_append hprefix tailTrace_309535
  have hstable : (prefixWord ++ tailWord_309535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309535).length < 2 ^ (prefixWord ++ tailWord_309535).sum := by decide
  have hdescent : baseEnd_309535 < baseStart_309535 := by decide
  rcases family_descends (prefixWord ++ tailWord_309535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309640 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_309640 : Nat := 118140960795 + 309640 * 2 ^ 59
def prefixEnd_309640 : Nat := 4983230072969 + 3 ^ 40 * 309640 * 2
def baseEnd_309640 : Nat := 105996099905515843850665

theorem tailTrace_309640 : CollatzResearch.WordTrace tailWord_309640 prefixEnd_309640 105996099905515843850665 := by
  unfold tailWord_309640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646749299117318573467187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7528999065489758097956249 5646749299117318573467187)
  ·
    refine ⟨8470123948675977860200781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5646749299117318573467187 8470123948675977860200781)
    ·
      refine ⟨3176296480753491697575293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8470123948675977860200781 3176296480753491697575293)
      ·
        refine ⟨1191111180282559386590735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3176296480753491697575293 1191111180282559386590735)
        ·
          refine ⟨1786666770423839079886103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191111180282559386590735 1786666770423839079886103)
          ·
            refine ⟨2680000155635758619829155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786666770423839079886103 2680000155635758619829155)
            ·
              refine ⟨4020000233453637929743733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680000155635758619829155 4020000233453637929743733)
              ·
                refine ⟨376875021886278555913475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4020000233453637929743733 376875021886278555913475)
                ·
                  refine ⟨565312532829417833870213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 376875021886278555913475 565312532829417833870213)
                  ·
                    refine ⟨105996099905515843850665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 565312532829417833870213 105996099905515843850665)
                    ·
                      rfl

theorem cell22_309640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_309640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309640 prefixEnd_309640 := by exact prefixLift 309640
  have htrace : WordTrace (prefixWord ++ tailWord_309640) baseStart_309640 baseEnd_309640 := by
    simpa [prefixWord, tailWord_309640, baseEnd_309640] using wordTrace_append hprefix tailTrace_309640
  have hstable : (prefixWord ++ tailWord_309640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309640).length < 2 ^ (prefixWord ++ tailWord_309640).sum := by decide
  have hdescent : baseEnd_309640 < baseStart_309640 := by decide
  rcases family_descends (prefixWord ++ tailWord_309640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309655 : List Nat := [1, 1, 3, 3, 1, 1, 2, 6, 4]
def baseStart_309655 : Nat := 118140960795 + 309655 * 2 ^ 59
def prefixEnd_309655 : Nat := 4983230072969 + 3 ^ 40 * 309655 * 2
def baseEnd_309655 : Nat := 35333744904020268241873

theorem tailTrace_309655 : CollatzResearch.WordTrace tailWord_309655 prefixEnd_309655 35333744904020268241873 := by
  unfold tailWord_309655
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294045693180294708730419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7529363795453529805820279 11294045693180294708730419)
  ·
    refine ⟨16941068539770442063095629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11294045693180294708730419 16941068539770442063095629)
    ·
      refine ⟨6352900702413915773660861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16941068539770442063095629 6352900702413915773660861)
      ·
        refine ⟨2382337763405218415122823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6352900702413915773660861 2382337763405218415122823)
        ·
          refine ⟨3573506645107827622684235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382337763405218415122823 3573506645107827622684235)
          ·
            refine ⟨5360259967661741434026353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573506645107827622684235 5360259967661741434026353)
            ·
              refine ⟨4020194975746306075519765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5360259967661741434026353 4020194975746306075519765)
              ·
                refine ⟨188446639488108097289989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4020194975746306075519765 188446639488108097289989)
                ·
                  refine ⟨35333744904020268241873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188446639488108097289989 35333744904020268241873)
                  ·
                    rfl

theorem cell22_309655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 4].length) (baseStart_309655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309655 prefixEnd_309655 := by exact prefixLift 309655
  have htrace : WordTrace (prefixWord ++ tailWord_309655) baseStart_309655 baseEnd_309655 := by
    simpa [prefixWord, tailWord_309655, baseEnd_309655] using wordTrace_append hprefix tailTrace_309655
  have hstable : (prefixWord ++ tailWord_309655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309655).length < 2 ^ (prefixWord ++ tailWord_309655).sum := by decide
  have hdescent : baseEnd_309655 < baseStart_309655 := by decide
  rcases family_descends (prefixWord ++ tailWord_309655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309668 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_309668 : Nat := 118140960795 + 309668 * 2 ^ 59
def prefixEnd_309668 : Nat := 4983230072969 + 3 ^ 40 * 309668 * 2
def baseEnd_309668 : Nat := 106005684877733104150579

theorem tailTrace_309668 : CollatzResearch.WordTrace tailWord_309668 prefixEnd_309668 106005684877733104150579 := by
  unfold tailWord_309668
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647259921066598964476829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7529679894755465285969105 5647259921066598964476829)
  ·
    refine ⟨2117722470399974611678811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5647259921066598964476829 2117722470399974611678811)
    ·
      refine ⟨3176583705599961917518217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2117722470399974611678811 3176583705599961917518217)
      ·
        refine ⟨2382437779199971438138663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3176583705599961917518217 2382437779199971438138663)
        ·
          refine ⟨3573656668799957157207995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382437779199971438138663 3573656668799957157207995)
          ·
            refine ⟨5360485003199935735811993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3573656668799957157207995 5360485003199935735811993)
            ·
              refine ⟨4020363752399951801858995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5360485003199935735811993 4020363752399951801858995)
              ·
                refine ⟨6030545628599927702788493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4020363752399951801858995 6030545628599927702788493)
                ·
                  refine ⟨2261454610724972888545685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6030545628599927702788493 2261454610724972888545685)
                  ·
                    refine ⟨106005684877733104150579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2261454610724972888545685 106005684877733104150579)
                    ·
                      rfl

theorem cell22_309668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_309668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309668 prefixEnd_309668 := by exact prefixLift 309668
  have htrace : WordTrace (prefixWord ++ tailWord_309668) baseStart_309668 baseEnd_309668 := by
    simpa [prefixWord, tailWord_309668, baseEnd_309668] using wordTrace_append hprefix tailTrace_309668
  have hstable : (prefixWord ++ tailWord_309668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309668).length < 2 ^ (prefixWord ++ tailWord_309668).sum := by decide
  have hdescent : baseEnd_309668 < baseStart_309668 := by decide
  rcases family_descends (prefixWord ++ tailWord_309668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309700 : List Nat := [2, 3, 3, 2, 2, 10]
def baseStart_309700 : Nat := 118140960795 + 309700 * 2 ^ 59
def prefixEnd_309700 : Nat := 4983230072969 + 3 ^ 40 * 309700 * 2
def baseEnd_309700 : Nat := 1308847396687601078401

theorem tailTrace_309700 : CollatzResearch.WordTrace tailWord_309700 prefixEnd_309700 1308847396687601078401 := by
  unfold tailWord_309700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647843489008633697059277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7530457985344844929412369 5647843489008633697059277)
  ·
    refine ⟨2117941308378237636397229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5647843489008633697059277 2117941308378237636397229)
    ·
      refine ⟨794227990641839113648961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2117941308378237636397229 794227990641839113648961)
      ·
        refine ⟨595670992981379335236721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794227990641839113648961 595670992981379335236721)
        ·
          refine ⟨446753244736034501427541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595670992981379335236721 446753244736034501427541)
          ·
            refine ⟨1308847396687601078401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 446753244736034501427541 1308847396687601078401)
            ·
              rfl

theorem cell22_309700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 10].length) (baseStart_309700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309700 prefixEnd_309700 := by exact prefixLift 309700
  have htrace : WordTrace (prefixWord ++ tailWord_309700) baseStart_309700 baseEnd_309700 := by
    simpa [prefixWord, tailWord_309700, baseEnd_309700] using wordTrace_append hprefix tailTrace_309700
  have hstable : (prefixWord ++ tailWord_309700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309700).length < 2 ^ (prefixWord ++ tailWord_309700).sum := by decide
  have hdescent : baseEnd_309700 < baseStart_309700 := by decide
  rcases family_descends (prefixWord ++ tailWord_309700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309743 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 3, 7]
def baseStart_309743 : Nat := 118140960795 + 309743 * 2 ^ 59
def prefixEnd_309743 : Nat := 4983230072969 + 3 ^ 40 * 309743 * 2
def baseEnd_309743 : Nat := 106031358910457908525349

theorem tailTrace_309743 : CollatzResearch.WordTrace tailWord_309743 prefixEnd_309743 106031358910457908525349 := by
  unfold tailWord_309743
  simp only [CollatzResearch.WordTrace]
  refine ⟨11297255316861485737933883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7531503544574323825289255 11297255316861485737933883)
  ·
    refine ⟨16945882975292228606900825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11297255316861485737933883 16945882975292228606900825)
    ·
      refine ⟨12709412231469171455175619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16945882975292228606900825 12709412231469171455175619)
      ·
        refine ⟨19064118347203757182763429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12709412231469171455175619 19064118347203757182763429)
        ·
          refine ⟨3574522190100704471768143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19064118347203757182763429 3574522190100704471768143)
          ·
            refine ⟨5361783285151056707652215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574522190100704471768143 5361783285151056707652215)
            ·
              refine ⟨8042674927726585061478323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361783285151056707652215 8042674927726585061478323)
              ·
                refine ⟨12064012391589877592217485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8042674927726585061478323 12064012391589877592217485)
                ·
                  refine ⟨4524004646846204097081557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12064012391589877592217485 4524004646846204097081557)
                  ·
                    refine ⟨106031358910457908525349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4524004646846204097081557 106031358910457908525349)
                    ·
                      rfl

theorem cell22_309743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_309743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309743 prefixEnd_309743 := by exact prefixLift 309743
  have htrace : WordTrace (prefixWord ++ tailWord_309743) baseStart_309743 baseEnd_309743 := by
    simpa [prefixWord, tailWord_309743, baseEnd_309743] using wordTrace_append hprefix tailTrace_309743
  have hstable : (prefixWord ++ tailWord_309743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309743).length < 2 ^ (prefixWord ++ tailWord_309743).sum := by decide
  have hdescent : baseEnd_309743 < baseStart_309743 := by decide
  rcases family_descends (prefixWord ++ tailWord_309743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309839 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 2, 3]
def baseStart_309839 : Nat := 118140960795 + 309839 * 2 ^ 59
def prefixEnd_309839 : Nat := 4983230072969 + 3 ^ 40 * 309839 * 2
def baseEnd_309839 : Nat := 106064221672345658125055

theorem tailTrace_309839 : CollatzResearch.WordTrace tailWord_309839 prefixEnd_309839 106064221672345658125055 := by
  unfold tailWord_309839
  simp only [CollatzResearch.WordTrace]
  refine ⟨11300756724513694133428571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7533837816342462755619047 11300756724513694133428571)
  ·
    refine ⟨16951135086770541200142857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11300756724513694133428571 16951135086770541200142857)
    ·
      refine ⟨12713351315077905900107143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16951135086770541200142857 12713351315077905900107143)
      ·
        refine ⟨19070026972616858850160715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12713351315077905900107143 19070026972616858850160715)
        ·
          refine ⟨28605040458925288275241073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19070026972616858850160715 28605040458925288275241073)
          ·
            refine ⟨21453780344193966206430805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28605040458925288275241073 21453780344193966206430805)
            ·
              refine ⟨251411488408523041481611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 21453780344193966206430805 251411488408523041481611)
              ·
                refine ⟨377117232612784562222417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251411488408523041481611 377117232612784562222417)
                ·
                  refine ⟨282837924459588421666813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377117232612784562222417 282837924459588421666813)
                  ·
                    refine ⟨106064221672345658125055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282837924459588421666813 106064221672345658125055)
                    ·
                      rfl

theorem cell22_309839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_309839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309839 prefixEnd_309839 := by exact prefixLift 309839
  have htrace : WordTrace (prefixWord ++ tailWord_309839) baseStart_309839 baseEnd_309839 := by
    simpa [prefixWord, tailWord_309839, baseEnd_309839] using wordTrace_append hprefix tailTrace_309839
  have hstable : (prefixWord ++ tailWord_309839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309839).length < 2 ^ (prefixWord ++ tailWord_309839).sum := by decide
  have hdescent : baseEnd_309839 < baseStart_309839 := by decide
  rcases family_descends (prefixWord ++ tailWord_309839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309918 : List Nat := [4, 3, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_309918 : Nat := 118140960795 + 309918 * 2 ^ 59
def prefixEnd_309918 : Nat := 4983230072969 + 3 ^ 40 * 309918 * 2
def baseEnd_309918 : Nat := 106091264986815785399813

theorem tailTrace_309918 : CollatzResearch.WordTrace tailWord_309918 prefixEnd_309918 106091264986815785399813 := by
  unfold tailWord_309918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412954761403436328194301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7535758727484993750369605 1412954761403436328194301)
  ·
    refine ⟨529858035526288623072863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1412954761403436328194301 529858035526288623072863)
    ·
      refine ⟨794787053289432934609295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529858035526288623072863 794787053289432934609295)
      ·
        refine ⟨1192180579934149401913943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794787053289432934609295 1192180579934149401913943)
        ·
          refine ⟨1788270869901224102870915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192180579934149401913943 1788270869901224102870915)
          ·
            refine ⟨2682406304851836154306373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788270869901224102870915 2682406304851836154306373)
            ·
              refine ⟨502951182159719278932445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2682406304851836154306373 502951182159719278932445)
              ·
                refine ⟨188606693309894729599667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 502951182159719278932445 188606693309894729599667)
                ·
                  refine ⟨282910039964842094399501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188606693309894729599667 282910039964842094399501)
                  ·
                    refine ⟨106091264986815785399813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282910039964842094399501 106091264986815785399813)
                    ·
                      rfl

theorem cell22_309918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_309918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309918 prefixEnd_309918 := by exact prefixLift 309918
  have htrace : WordTrace (prefixWord ++ tailWord_309918) baseStart_309918 baseEnd_309918 := by
    simpa [prefixWord, tailWord_309918, baseEnd_309918] using wordTrace_append hprefix tailTrace_309918
  have hstable : (prefixWord ++ tailWord_309918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309918).length < 2 ^ (prefixWord ++ tailWord_309918).sum := by decide
  have hdescent : baseEnd_309918 < baseStart_309918 := by decide
  rcases family_descends (prefixWord ++ tailWord_309918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309925 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 10]
def baseStart_309925 : Nat := 118140960795 + 309925 * 2 ^ 59
def prefixEnd_309925 : Nat := 4983230072969 + 3 ^ 40 * 309925 * 2
def baseEnd_309925 : Nat := 35364553743290033491597

theorem tailTrace_309925 : CollatzResearch.WordTrace tailWord_309925 prefixEnd_309925 35364553743290033491597 := by
  unfold tailWord_309925
  simp only [CollatzResearch.WordTrace]
  refine ⟨11303893402202130821059229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7535928934801420547372819 11303893402202130821059229)
  ·
    refine ⟨4238960025825799057897211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11303893402202130821059229 4238960025825799057897211)
    ·
      refine ⟨6358440038738698586845817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4238960025825799057897211 6358440038738698586845817)
      ·
        refine ⟨4768830029054023940134363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6358440038738698586845817 4768830029054023940134363)
        ·
          refine ⟨7153245043581035910201545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4768830029054023940134363 7153245043581035910201545)
          ·
            refine ⟨5364933782685776932651159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7153245043581035910201545 5364933782685776932651159)
            ·
              refine ⟨8047400674028665398976739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5364933782685776932651159 8047400674028665398976739)
              ·
                refine ⟨12071101011042998098465109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8047400674028665398976739 12071101011042998098465109)
                ·
                  refine ⟨35364553743290033491597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 12071101011042998098465109 35364553743290033491597)
                  ·
                    rfl

theorem cell22_309925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_309925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309925 prefixEnd_309925 := by exact prefixLift 309925
  have htrace : WordTrace (prefixWord ++ tailWord_309925) baseStart_309925 baseEnd_309925 := by
    simpa [prefixWord, tailWord_309925, baseEnd_309925] using wordTrace_append hprefix tailTrace_309925
  have hstable : (prefixWord ++ tailWord_309925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309925).length < 2 ^ (prefixWord ++ tailWord_309925).sum := by decide
  have hdescent : baseEnd_309925 < baseStart_309925 := by decide
  rcases family_descends (prefixWord ++ tailWord_309925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309957 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 8, 3]
def baseStart_309957 : Nat := 118140960795 + 309957 * 2 ^ 59
def prefixEnd_309957 : Nat := 4983230072969 + 3 ^ 40 * 309957 * 2
def baseEnd_309957 : Nat := 106104615483832683674693

theorem tailTrace_309957 : CollatzResearch.WordTrace tailWord_309957 prefixEnd_309957 106104615483832683674693 := by
  unfold tailWord_309957
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305060538086200286224125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7536707025390800190816083 11305060538086200286224125)
  ·
    refine ⟨4239397701782325107334047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11305060538086200286224125 4239397701782325107334047)
    ·
      refine ⟨6359096552673487661001071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4239397701782325107334047 6359096552673487661001071)
      ·
        refine ⟨9538644829010231491501607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6359096552673487661001071 9538644829010231491501607)
        ·
          refine ⟨14307967243515347237252411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9538644829010231491501607 14307967243515347237252411)
          ·
            refine ⟨21461950865273020855878617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14307967243515347237252411 21461950865273020855878617)
            ·
              refine ⟨16096463148954765641908963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21461950865273020855878617 16096463148954765641908963)
              ·
                refine ⟨24144694723432148462863445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16096463148954765641908963 24144694723432148462863445)
                ·
                  refine ⟨282945641290220489799181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24144694723432148462863445 282945641290220489799181)
                  ·
                    refine ⟨106104615483832683674693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282945641290220489799181 106104615483832683674693)
                    ·
                      rfl

theorem cell22_309957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_309957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309957 prefixEnd_309957 := by exact prefixLift 309957
  have htrace : WordTrace (prefixWord ++ tailWord_309957) baseStart_309957 baseEnd_309957 := by
    simpa [prefixWord, tailWord_309957, baseEnd_309957] using wordTrace_append hprefix tailTrace_309957
  have hstable : (prefixWord ++ tailWord_309957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309957).length < 2 ^ (prefixWord ++ tailWord_309957).sum := by decide
  have hdescent : baseEnd_309957 < baseStart_309957 := by decide
  rcases family_descends (prefixWord ++ tailWord_309957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309976 : List Nat := [2, 1, 2, 2, 3, 4, 1, 3, 4]
def baseStart_309976 : Nat := 118140960795 + 309976 * 2 ^ 59
def prefixEnd_309976 : Nat := 4983230072969 + 3 ^ 40 * 309976 * 2
def baseEnd_309976 : Nat := 35370373190707655816545

theorem tailTrace_309976 : CollatzResearch.WordTrace tailWord_309976 prefixEnd_309976 35370373190707655816545 := by
  unfold tailWord_309976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652876762508683265582891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7537169016678244354110521 5652876762508683265582891)
  ·
    refine ⟨8479315143763024898374337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5652876762508683265582891 8479315143763024898374337)
    ·
      refine ⟨6359486357822268673780753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8479315143763024898374337 6359486357822268673780753)
      ·
        refine ⟨4769614768366701505335565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6359486357822268673780753 4769614768366701505335565)
        ·
          refine ⟨1788605538137513064500837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4769614768366701505335565 1788605538137513064500837)
          ·
            refine ⟨335363538400783699593907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1788605538137513064500837 335363538400783699593907)
            ·
              refine ⟨503045307601175549390861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335363538400783699593907 503045307601175549390861)
              ·
                refine ⟨188641990350440831021573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503045307601175549390861 188641990350440831021573)
                ·
                  refine ⟨35370373190707655816545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188641990350440831021573 35370373190707655816545)
                  ·
                    rfl

theorem cell22_309976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_309976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309976 prefixEnd_309976 := by exact prefixLift 309976
  have htrace : WordTrace (prefixWord ++ tailWord_309976) baseStart_309976 baseEnd_309976 := by
    simpa [prefixWord, tailWord_309976, baseEnd_309976] using wordTrace_append hprefix tailTrace_309976
  have hstable : (prefixWord ++ tailWord_309976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309976).length < 2 ^ (prefixWord ++ tailWord_309976).sum := by decide
  have hdescent : baseEnd_309976 < baseStart_309976 := by decide
  rcases family_descends (prefixWord ++ tailWord_309976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309987 : List Nat := [1, 1, 1, 7, 1, 1, 10]
def baseStart_309987 : Nat := 118140960795 + 309987 * 2 ^ 59
def prefixEnd_309987 : Nat := 4983230072969 + 3 ^ 40 * 309987 * 2
def baseEnd_309987 : Nat := 3930180929515652052763

theorem tailTrace_309987 : CollatzResearch.WordTrace tailWord_309987 prefixEnd_309987 3930180929515652052763 := by
  unfold tailWord_309987
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306154727977515409816215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7537436485318343606544143 11306154727977515409816215)
  ·
    refine ⟨16959232091966273114724323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11306154727977515409816215 16959232091966273114724323)
    ·
      refine ⟨25438848137949409672086485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16959232091966273114724323 25438848137949409672086485)
      ·
        refine ⟨596223003233189289189527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25438848137949409672086485 596223003233189289189527)
        ·
          refine ⟨894334504849783933784291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596223003233189289189527 894334504849783933784291)
          ·
            refine ⟨1341501757274675900676437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894334504849783933784291 1341501757274675900676437)
            ·
              refine ⟨3930180929515652052763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1341501757274675900676437 3930180929515652052763)
              ·
                rfl

theorem cell22_309987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 10].length) (baseStart_309987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309987 prefixEnd_309987 := by exact prefixLift 309987
  have htrace : WordTrace (prefixWord ++ tailWord_309987) baseStart_309987 baseEnd_309987 := by
    simpa [prefixWord, tailWord_309987, baseEnd_309987] using wordTrace_append hprefix tailTrace_309987
  have hstable : (prefixWord ++ tailWord_309987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309987).length < 2 ^ (prefixWord ++ tailWord_309987).sum := by decide
  have hdescent : baseEnd_309987 < baseStart_309987 := by decide
  rcases family_descends (prefixWord ++ tailWord_309987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309989 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_309989 : Nat := 118140960795 + 309989 * 2 ^ 59
def prefixEnd_309989 : Nat := 4983230072969 + 3 ^ 40 * 309989 * 2
def baseEnd_309989 : Nat := 106115569737795266874595

theorem tailTrace_309989 : CollatzResearch.WordTrace tailWord_309989 prefixEnd_309989 106115569737795266874595 := by
  unfold tailWord_309989
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306227673970269751389021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7537485115980179834259347 11306227673970269751389021)
  ·
    refine ⟨4239835377738851156770883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11306227673970269751389021 4239835377738851156770883)
    ·
      refine ⟨6359753066608276735156325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4239835377738851156770883 6359753066608276735156325)
      ·
        refine ⟨1192453699989051887841811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6359753066608276735156325 1192453699989051887841811)
        ·
          refine ⟨1788680549983577831762717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192453699989051887841811 1788680549983577831762717)
          ·
            refine ⟨670755206243841686911019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1788680549983577831762717 670755206243841686911019)
            ·
              refine ⟨1006132809365762530366529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670755206243841686911019 1006132809365762530366529)
              ·
                refine ⟨754599607024321897774897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006132809365762530366529 754599607024321897774897)
                ·
                  refine ⟨565949705268241423331173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 754599607024321897774897 565949705268241423331173)
                  ·
                    refine ⟨106115569737795266874595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 565949705268241423331173 106115569737795266874595)
                    ·
                      rfl

theorem cell22_309989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_309989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_309989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_309989 prefixEnd_309989 := by exact prefixLift 309989
  have htrace : WordTrace (prefixWord ++ tailWord_309989) baseStart_309989 baseEnd_309989 := by
    simpa [prefixWord, tailWord_309989, baseEnd_309989] using wordTrace_append hprefix tailTrace_309989
  have hstable : (prefixWord ++ tailWord_309989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309989).length < 2 ^ (prefixWord ++ tailWord_309989).sum := by decide
  have hdescent : baseEnd_309989 < baseStart_309989 := by decide
  rcases family_descends (prefixWord ++ tailWord_309989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310049 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 5]
def baseStart_310049 : Nat := 118140960795 + 310049 * 2 ^ 59
def prefixEnd_310049 : Nat := 4983230072969 + 3 ^ 40 * 310049 * 2
def baseEnd_310049 : Nat := 35378702987991703458137

theorem tailTrace_310049 : CollatzResearch.WordTrace tailWord_310049 prefixEnd_310049 35378702987991703458137 := by
  unfold tailWord_310049
  simp only [CollatzResearch.WordTrace]
  refine ⟨11308416053752899998573201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7538944035835266665715467 11308416053752899998573201)
  ·
    refine ⟨8481312040314674998929901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11308416053752899998573201 8481312040314674998929901)
    ·
      refine ⟨3180492015118003124598713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8481312040314674998929901 3180492015118003124598713)
      ·
        refine ⟨2385369011338502343449035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180492015118003124598713 2385369011338502343449035)
        ·
          refine ⟨3578053517007753515173553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2385369011338502343449035 3578053517007753515173553)
          ·
            refine ⟨2683540137755815136380165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578053517007753515173553 2683540137755815136380165)
            ·
              refine ⟨503163775829215338071281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2683540137755815136380165 503163775829215338071281)
              ·
                refine ⟨377372831871911503553461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503163775829215338071281 377372831871911503553461)
                ·
                  refine ⟨35378702987991703458137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377372831871911503553461 35378702987991703458137)
                  ·
                    rfl

theorem cell22_310049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_310049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310049 prefixEnd_310049 := by exact prefixLift 310049
  have htrace : WordTrace (prefixWord ++ tailWord_310049) baseStart_310049 baseEnd_310049 := by
    simpa [prefixWord, tailWord_310049, baseEnd_310049] using wordTrace_append hprefix tailTrace_310049
  have hstable : (prefixWord ++ tailWord_310049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310049).length < 2 ^ (prefixWord ++ tailWord_310049).sum := by decide
  have hdescent : baseEnd_310049 < baseStart_310049 := by decide
  rcases family_descends (prefixWord ++ tailWord_310049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310079 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 3, 4]
def baseStart_310079 : Nat := 118140960795 + 310079 * 2 ^ 59
def prefixEnd_310079 : Nat := 4983230072969 + 3 ^ 40 * 310079 * 2
def baseEnd_310079 : Nat := 106146378577065032124319

theorem tailTrace_310079 : CollatzResearch.WordTrace tailWord_310079 prefixEnd_310079 106146378577065032124319 := by
  unfold tailWord_310079
  simp only [CollatzResearch.WordTrace]
  refine ⟨11309510243644215122165291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7539673495762810081443527 11309510243644215122165291)
  ·
    refine ⟨16964265365466322683247937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11309510243644215122165291 16964265365466322683247937)
    ·
      refine ⟨12723199024099742012435953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16964265365466322683247937 12723199024099742012435953)
      ·
        refine ⟨9542399268074806509326965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12723199024099742012435953 9542399268074806509326965)
        ·
          refine ⟨894599931382013110249403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9542399268074806509326965 894599931382013110249403)
          ·
            refine ⟨1341899897073019665374105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894599931382013110249403 1341899897073019665374105)
            ·
              refine ⟨1006424922804764749030579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1341899897073019665374105 1006424922804764749030579)
              ·
                refine ⟨1509637384207147123545869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006424922804764749030579 1509637384207147123545869)
                ·
                  refine ⟨566114019077680171329701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1509637384207147123545869 566114019077680171329701)
                  ·
                    refine ⟨106146378577065032124319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566114019077680171329701 106146378577065032124319)
                    ·
                      rfl

theorem cell22_310079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_310079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310079 prefixEnd_310079 := by exact prefixLift 310079
  have htrace : WordTrace (prefixWord ++ tailWord_310079) baseStart_310079 baseEnd_310079 := by
    simpa [prefixWord, tailWord_310079, baseEnd_310079] using wordTrace_append hprefix tailTrace_310079
  have hstable : (prefixWord ++ tailWord_310079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310079).length < 2 ^ (prefixWord ++ tailWord_310079).sum := by decide
  have hdescent : baseEnd_310079 < baseStart_310079 := by decide
  rcases family_descends (prefixWord ++ tailWord_310079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310096 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 1, 4]
def baseStart_310096 : Nat := 118140960795 + 310096 * 2 ^ 59
def prefixEnd_310096 : Nat := 4983230072969 + 3 ^ 40 * 310096 * 2
def baseEnd_310096 : Nat := 106152198024482654449267

theorem tailTrace_310096 : CollatzResearch.WordTrace tailWord_310096 prefixEnd_310096 106152198024482654449267 := by
  unfold tailWord_310096
  simp only [CollatzResearch.WordTrace]
  refine ⟨5655065142291313512767071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7540086856388418017022761 5655065142291313512767071)
  ·
    refine ⟨8482597713436970269150607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5655065142291313512767071 8482597713436970269150607)
    ·
      refine ⟨12723896570155455403725911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8482597713436970269150607 12723896570155455403725911)
      ·
        refine ⟨19085844855233183105588867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12723896570155455403725911 19085844855233183105588867)
        ·
          refine ⟨28628767282849774658383301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19085844855233183105588867 28628767282849774658383301)
          ·
            refine ⟨5367893865534332748446869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28628767282849774658383301 5367893865534332748446869)
            ·
              refine ⟨251620024946921847583447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5367893865534332748446869 251620024946921847583447)
              ·
                refine ⟨377430037420382771375171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251620024946921847583447 377430037420382771375171)
                ·
                  refine ⟨566145056130574157062757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377430037420382771375171 566145056130574157062757)
                  ·
                    refine ⟨106152198024482654449267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566145056130574157062757 106152198024482654449267)
                    ·
                      rfl

theorem cell22_310096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_310096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310096 prefixEnd_310096 := by exact prefixLift 310096
  have htrace : WordTrace (prefixWord ++ tailWord_310096) baseStart_310096 baseEnd_310096 := by
    simpa [prefixWord, tailWord_310096, baseEnd_310096] using wordTrace_append hprefix tailTrace_310096
  have hstable : (prefixWord ++ tailWord_310096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310096).length < 2 ^ (prefixWord ++ tailWord_310096).sum := by decide
  have hdescent : baseEnd_310096 < baseStart_310096 := by decide
  rcases family_descends (prefixWord ++ tailWord_310096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310139 : List Nat := [1, 1, 1, 1, 1, 5, 6, 6]
def baseStart_310139 : Nat := 118140960795 + 310139 * 2 ^ 59
def prefixEnd_310139 : Nat := 4983230072969 + 3 ^ 40 * 310139 * 2
def baseEnd_310139 : Nat := 11796324200360541736015

theorem tailTrace_310139 : CollatzResearch.WordTrace tailWord_310139 prefixEnd_310139 11796324200360541736015 := by
  unfold tailWord_310139
  simp only [CollatzResearch.WordTrace]
  refine ⟨11311698623426845369349471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7541132415617896912899647 11311698623426845369349471)
  ·
    refine ⟨16967547935140268054024207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11311698623426845369349471 16967547935140268054024207)
    ·
      refine ⟨25451321902710402081036311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16967547935140268054024207 25451321902710402081036311)
      ·
        refine ⟨38176982854065603121554467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25451321902710402081036311 38176982854065603121554467)
        ·
          refine ⟨57265474281098404682331701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38176982854065603121554467 57265474281098404682331701)
          ·
            refine ⟨5368638213852975438968597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57265474281098404682331701 5368638213852975438968597)
            ·
              refine ⟨251654916274358223701653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5368638213852975438968597 251654916274358223701653)
              ·
                refine ⟨11796324200360541736015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 251654916274358223701653 11796324200360541736015)
                ·
                  rfl

theorem cell22_310139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 6].length) (baseStart_310139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310139 prefixEnd_310139 := by exact prefixLift 310139
  have htrace : WordTrace (prefixWord ++ tailWord_310139) baseStart_310139 baseEnd_310139 := by
    simpa [prefixWord, tailWord_310139, baseEnd_310139] using wordTrace_append hprefix tailTrace_310139
  have hstable : (prefixWord ++ tailWord_310139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310139).length < 2 ^ (prefixWord ++ tailWord_310139).sum := by decide
  have hdescent : baseEnd_310139 < baseStart_310139 := by decide
  rcases family_descends (prefixWord ++ tailWord_310139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310222 : List Nat := [4, 1, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_310222 : Nat := 118140960795 + 310222 * 2 ^ 59
def prefixEnd_310222 : Nat := 4983230072969 + 3 ^ 40 * 310222 * 2
def baseEnd_310222 : Nat := 106195330399460325798881

theorem tailTrace_310222 : CollatzResearch.WordTrace tailWord_310222 prefixEnd_310222 106195330399460325798881 := by
  unfold tailWord_310222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414340735265768818077615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7543150588084100363080613 1414340735265768818077615)
  ·
    refine ⟨2121511102898653227116423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1414340735265768818077615 2121511102898653227116423)
    ·
      refine ⟨3182266654347979840674635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2121511102898653227116423 3182266654347979840674635)
      ·
        refine ⟨4773399981521969761011953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3182266654347979840674635 4773399981521969761011953)
        ·
          refine ⟨3580049986141477320758965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4773399981521969761011953 3580049986141477320758965)
          ·
            refine ⟨335629686200763498821153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3580049986141477320758965 335629686200763498821153)
            ·
              refine ⟨251722264650572624115865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335629686200763498821153 251722264650572624115865)
              ·
                refine ⟨188791698487929468086899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251722264650572624115865 188791698487929468086899)
                ·
                  refine ⟨283187547731894202130349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188791698487929468086899 283187547731894202130349)
                  ·
                    refine ⟨106195330399460325798881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283187547731894202130349 106195330399460325798881)
                    ·
                      rfl

theorem cell22_310222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_310222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310222 prefixEnd_310222 := by exact prefixLift 310222
  have htrace : WordTrace (prefixWord ++ tailWord_310222) baseStart_310222 baseEnd_310222 := by
    simpa [prefixWord, tailWord_310222, baseEnd_310222] using wordTrace_append hprefix tailTrace_310222
  have hstable : (prefixWord ++ tailWord_310222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310222).length < 2 ^ (prefixWord ++ tailWord_310222).sum := by decide
  have hdescent : baseEnd_310222 < baseStart_310222 := by decide
  rcases family_descends (prefixWord ++ tailWord_310222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310308 : List Nat := [2, 3, 1, 4, 1, 1, 4, 6]
def baseStart_310308 : Nat := 118140960795 + 310308 * 2 ^ 59
def prefixEnd_310308 : Nat := 4983230072969 + 3 ^ 40 * 310308 * 2
def baseEnd_310308 : Nat := 11802752217442752016513

theorem tailTrace_310308 : CollatzResearch.WordTrace tailWord_310308 prefixEnd_310308 11802752217442752016513 := by
  unfold tailWord_310308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5658931279907293616125789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7545241706543058154834385 5658931279907293616125789)
  ·
    refine ⟨2122099229965235106047171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5658931279907293616125789 2122099229965235106047171)
    ·
      refine ⟨3183148844947852659070757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2122099229965235106047171 3183148844947852659070757)
      ·
        refine ⟨596840408427722373575767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3183148844947852659070757 596840408427722373575767)
        ·
          refine ⟨895260612641583560363651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596840408427722373575767 895260612641583560363651)
          ·
            refine ⟨1342890918962375340545477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895260612641583560363651 1342890918962375340545477)
            ·
              refine ⟨251792047305445376352277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1342890918962375340545477 251792047305445376352277)
              ·
                refine ⟨11802752217442752016513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 251792047305445376352277 11802752217442752016513)
                ·
                  rfl

theorem cell22_310308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 6].length) (baseStart_310308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310308 prefixEnd_310308 := by exact prefixLift 310308
  have htrace : WordTrace (prefixWord ++ tailWord_310308) baseStart_310308 baseEnd_310308 := by
    simpa [prefixWord, tailWord_310308, baseEnd_310308] using wordTrace_append hprefix tailTrace_310308
  have hstable : (prefixWord ++ tailWord_310308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310308).length < 2 ^ (prefixWord ++ tailWord_310308).sum := by decide
  have hdescent : baseEnd_310308 < baseStart_310308 := by decide
  rcases family_descends (prefixWord ++ tailWord_310308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310336 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 5]
def baseStart_310336 : Nat := 118140960795 + 310336 * 2 ^ 59
def prefixEnd_310336 : Nat := 4983230072969 + 3 ^ 40 * 310336 * 2
def baseEnd_310336 : Nat := 35411451643067342816177

theorem tailTrace_310336 : CollatzResearch.WordTrace tailWord_310336 prefixEnd_310336 35411451643067342816177 := by
  unfold tailWord_310336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5659441901856574007135431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7545922535808765342847241 5659441901856574007135431)
  ·
    refine ⟨8489162852784861010703147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5659441901856574007135431 8489162852784861010703147)
    ·
      refine ⟨12733744279177291516054721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8489162852784861010703147 12733744279177291516054721)
      ·
        refine ⟨9550308209382968637041041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12733744279177291516054721 9550308209382968637041041)
        ·
          refine ⟨7162731157037226477780781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9550308209382968637041041 7162731157037226477780781)
          ·
            refine ⟨2686024183888959929167793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7162731157037226477780781 2686024183888959929167793)
            ·
              refine ⟨2014518137916719946875845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2686024183888959929167793 2014518137916719946875845)
              ·
                refine ⟨377722150859384990039221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2014518137916719946875845 377722150859384990039221)
                ·
                  refine ⟨35411451643067342816177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377722150859384990039221 35411451643067342816177)
                  ·
                    rfl

theorem cell22_310336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_310336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310336 prefixEnd_310336 := by exact prefixLift 310336
  have htrace : WordTrace (prefixWord ++ tailWord_310336) baseStart_310336 baseEnd_310336 := by
    simpa [prefixWord, tailWord_310336, baseEnd_310336] using wordTrace_append hprefix tailTrace_310336
  have hstable : (prefixWord ++ tailWord_310336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310336).length < 2 ^ (prefixWord ++ tailWord_310336).sum := by decide
  have hdescent : baseEnd_310336 < baseStart_310336 := by decide
  rcases family_descends (prefixWord ++ tailWord_310336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310353 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 5]
def baseStart_310353 : Nat := 118140960795 + 310353 * 2 ^ 59
def prefixEnd_310353 : Nat := 4983230072969 + 3 ^ 40 * 310353 * 2
def baseEnd_310353 : Nat := 35413391458873216924493

theorem tailTrace_310353 : CollatzResearch.WordTrace tailWord_310353 prefixEnd_310353 35413391458873216924493 := by
  unfold tailWord_310353
  simp only [CollatzResearch.WordTrace]
  refine ⟨11319503844651559917639713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7546335896434373278426475 11319503844651559917639713)
  ·
    refine ⟨8489627883488669938229785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11319503844651559917639713 8489627883488669938229785)
    ·
      refine ⟨6367220912616502453672339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8489627883488669938229785 6367220912616502453672339)
      ·
        refine ⟨9550831368924753680508509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6367220912616502453672339 9550831368924753680508509)
        ·
          refine ⟨3581561763346782630190691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9550831368924753680508509 3581561763346782630190691)
          ·
            refine ⟨5372342645020173945286037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581561763346782630190691 5372342645020173945286037)
            ·
              refine ⟨251828561485320653685283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5372342645020173945286037 251828561485320653685283)
              ·
                refine ⟨377742842227980980527925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251828561485320653685283 377742842227980980527925)
                ·
                  refine ⟨35413391458873216924493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377742842227980980527925 35413391458873216924493)
                  ·
                    rfl

theorem cell22_310353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 5].length) (baseStart_310353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310353 prefixEnd_310353 := by exact prefixLift 310353
  have htrace : WordTrace (prefixWord ++ tailWord_310353) baseStart_310353 baseEnd_310353 := by
    simpa [prefixWord, tailWord_310353, baseEnd_310353] using wordTrace_append hprefix tailTrace_310353
  have hstable : (prefixWord ++ tailWord_310353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310353).length < 2 ^ (prefixWord ++ tailWord_310353).sum := by decide
  have hdescent : baseEnd_310353 < baseStart_310353 := by decide
  rcases family_descends (prefixWord ++ tailWord_310353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310396 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_310396 : Nat := 118140960795 + 310396 * 2 ^ 59
def prefixEnd_310396 : Nat := 4983230072969 + 3 ^ 40 * 310396 * 2
def baseEnd_310396 : Nat := 106254894155381871948347

theorem tailTrace_310396 : CollatzResearch.WordTrace tailWord_310396 prefixEnd_310396 106254894155381871948347 := by
  unfold tailWord_310396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660536091747889130727521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7547381455663852174303361 5660536091747889130727521)
  ·
    refine ⟨4245402068810916848045641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5660536091747889130727521 4245402068810916848045641)
    ·
      refine ⟨3184051551608187636034231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4245402068810916848045641 3184051551608187636034231)
      ·
        refine ⟨4776077327412281454051347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184051551608187636034231 4776077327412281454051347)
        ·
          refine ⟨7164115991118422181077021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776077327412281454051347 7164115991118422181077021)
          ·
            refine ⟨2686543496669408317903883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7164115991118422181077021 2686543496669408317903883)
            ·
              refine ⟨4029815245004112476855825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686543496669408317903883 4029815245004112476855825)
              ·
                refine ⟨3022361433753084357641869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4029815245004112476855825 3022361433753084357641869)
                ·
                  refine ⟨1133385537657406634115701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3022361433753084357641869 1133385537657406634115701)
                  ·
                    refine ⟨106254894155381871948347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1133385537657406634115701 106254894155381871948347)
                    ·
                      rfl

theorem cell22_310396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_310396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310396 prefixEnd_310396 := by exact prefixLift 310396
  have htrace : WordTrace (prefixWord ++ tailWord_310396) baseStart_310396 baseEnd_310396 := by
    simpa [prefixWord, tailWord_310396, baseEnd_310396] using wordTrace_append hprefix tailTrace_310396
  have hstable : (prefixWord ++ tailWord_310396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310396).length < 2 ^ (prefixWord ++ tailWord_310396).sum := by decide
  have hdescent : baseEnd_310396 < baseStart_310396 := by decide
  rcases family_descends (prefixWord ++ tailWord_310396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310411 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 4, 4]
def baseStart_310411 : Nat := 118140960795 + 310411 * 2 ^ 59
def prefixEnd_310411 : Nat := 4983230072969 + 3 ^ 40 * 310411 * 2
def baseEnd_310411 : Nat := 106260028961926832823301

theorem tailTrace_310411 : CollatzResearch.WordTrace tailWord_310411 prefixEnd_310411 106260028961926832823301 := by
  unfold tailWord_310411
  simp only [CollatzResearch.WordTrace]
  refine ⟨11321619278441435823251087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7547746185627623882167391 11321619278441435823251087)
  ·
    refine ⟨16982428917662153734876631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11321619278441435823251087 16982428917662153734876631)
    ·
      refine ⟨25473643376493230602314947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16982428917662153734876631 25473643376493230602314947)
      ·
        refine ⟨38210465064739845903472421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25473643376493230602314947 38210465064739845903472421)
        ·
          refine ⟨7164462199638721106901079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38210465064739845903472421 7164462199638721106901079)
          ·
            refine ⟨10746693299458081660351619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164462199638721106901079 10746693299458081660351619)
            ·
              refine ⟨16120039949187122490527429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746693299458081660351619 16120039949187122490527429)
              ·
                refine ⟨3022507490472585466973893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16120039949187122490527429 3022507490472585466973893)
                ·
                  refine ⟨566720154463609775057605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3022507490472585466973893 566720154463609775057605)
                  ·
                    refine ⟨106260028961926832823301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566720154463609775057605 106260028961926832823301)
                    ·
                      rfl

theorem cell22_310411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 4].length) (baseStart_310411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310411 prefixEnd_310411 := by exact prefixLift 310411
  have htrace : WordTrace (prefixWord ++ tailWord_310411) baseStart_310411 baseEnd_310411 := by
    simpa [prefixWord, tailWord_310411, baseEnd_310411] using wordTrace_append hprefix tailTrace_310411
  have hstable : (prefixWord ++ tailWord_310411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310411).length < 2 ^ (prefixWord ++ tailWord_310411).sum := by decide
  have hdescent : baseEnd_310411 < baseStart_310411 := by decide
  rcases family_descends (prefixWord ++ tailWord_310411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310428 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_310428 : Nat := 118140960795 + 310428 * 2 ^ 59
def prefixEnd_310428 : Nat := 4983230072969 + 3 ^ 40 * 310428 * 2
def baseEnd_310428 : Nat := 106265848409344455148249

theorem tailTrace_310428 : CollatzResearch.WordTrace tailWord_310428 prefixEnd_310428 106265848409344455148249 := by
  unfold tailWord_310428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5661119659689923863309969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7548159546253231817746625 5661119659689923863309969)
  ·
    refine ⟨4245839744767442897482477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5661119659689923863309969 4245839744767442897482477)
    ·
      refine ⟨1592189904287791086555929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4245839744767442897482477 1592189904287791086555929)
      ·
        refine ⟨1194142428215843314916947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1592189904287791086555929 1194142428215843314916947)
        ·
          refine ⟨1791213642323764972375421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194142428215843314916947 1791213642323764972375421)
          ·
            refine ⟨671705115871411864640783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1791213642323764972375421 671705115871411864640783)
            ·
              refine ⟨1007557673807117796961175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671705115871411864640783 1007557673807117796961175)
              ·
                refine ⟨1511336510710676695441763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007557673807117796961175 1511336510710676695441763)
                ·
                  refine ⟨2267004766066015043162645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511336510710676695441763 2267004766066015043162645)
                  ·
                    refine ⟨106265848409344455148249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2267004766066015043162645 106265848409344455148249)
                    ·
                      rfl

theorem cell22_310428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_310428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310428 prefixEnd_310428 := by exact prefixLift 310428
  have htrace : WordTrace (prefixWord ++ tailWord_310428) baseStart_310428 baseEnd_310428 := by
    simpa [prefixWord, tailWord_310428, baseEnd_310428] using wordTrace_append hprefix tailTrace_310428
  have hstable : (prefixWord ++ tailWord_310428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310428).length < 2 ^ (prefixWord ++ tailWord_310428).sum := by decide
  have hdescent : baseEnd_310428 < baseStart_310428 := by decide
  rcases family_descends (prefixWord ++ tailWord_310428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310430 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_310430 : Nat := 118140960795 + 310430 * 2 ^ 59
def prefixEnd_310430 : Nat := 4983230072969 + 3 ^ 40 * 310430 * 2
def baseEnd_310430 : Nat := 106266533050217116598243

theorem tailTrace_310430 : CollatzResearch.WordTrace tailWord_310430 prefixEnd_310430 106266533050217116598243 := by
  unfold tailWord_310430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415289033171575258524093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7548208176915068045461829 1415289033171575258524093)
  ·
    refine ⟨530733387439340721946535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1415289033171575258524093 530733387439340721946535)
    ·
      refine ⟨796100081159011082919803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530733387439340721946535 796100081159011082919803)
      ·
        refine ⟨1194150121738516624379705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796100081159011082919803 1194150121738516624379705)
        ·
          refine ⟨895612591303887468284779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1194150121738516624379705 895612591303887468284779)
          ·
            refine ⟨1343418886955831202427169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895612591303887468284779 1343418886955831202427169)
            ·
              refine ⟨1007564165216873401820377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343418886955831202427169 1007564165216873401820377)
              ·
                refine ⟨755673123912655051365283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007564165216873401820377 755673123912655051365283)
                ·
                  refine ⟨1133509685868982577047925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 755673123912655051365283 1133509685868982577047925)
                  ·
                    refine ⟨106266533050217116598243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1133509685868982577047925 106266533050217116598243)
                    ·
                      rfl

theorem cell22_310430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_310430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310430 prefixEnd_310430 := by exact prefixLift 310430
  have htrace : WordTrace (prefixWord ++ tailWord_310430) baseStart_310430 baseEnd_310430 := by
    simpa [prefixWord, tailWord_310430, baseEnd_310430] using wordTrace_append hprefix tailTrace_310430
  have hstable : (prefixWord ++ tailWord_310430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310430).length < 2 ^ (prefixWord ++ tailWord_310430).sum := by decide
  have hdescent : baseEnd_310430 < baseStart_310430 := by decide
  rcases family_descends (prefixWord ++ tailWord_310430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310434 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_310434 : Nat := 118140960795 + 310434 * 2 ^ 59
def prefixEnd_310434 : Nat := 4983230072969 + 3 ^ 40 * 310434 * 2
def baseEnd_310434 : Nat := 106267902331962439498231

theorem tailTrace_310434 : CollatzResearch.WordTrace tailWord_310434 prefixEnd_310434 106267902331962439498231 := by
  unfold tailWord_310434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2830614539339527687834589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7548305438238740500892237 2830614539339527687834589)
  ·
    refine ⟨1061480452252322882937971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2830614539339527687834589 1061480452252322882937971)
    ·
      refine ⟨1592220678378484324406957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061480452252322882937971 1592220678378484324406957)
      ·
        refine ⟨597082754391931621652609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1592220678378484324406957 597082754391931621652609)
        ·
          refine ⟨447812065793948716239457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597082754391931621652609 447812065793948716239457)
          ·
            refine ⟨335859049345461537179593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447812065793948716239457 335859049345461537179593)
            ·
              refine ⟨251894287009096152884695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335859049345461537179593 251894287009096152884695)
              ·
                refine ⟨377841430513644229327043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251894287009096152884695 377841430513644229327043)
                ·
                  refine ⟨566762145770466343990565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377841430513644229327043 566762145770466343990565)
                  ·
                    refine ⟨106267902331962439498231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566762145770466343990565 106267902331962439498231)
                    ·
                      rfl

theorem cell22_310434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_310434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310434 prefixEnd_310434 := by exact prefixLift 310434
  have htrace : WordTrace (prefixWord ++ tailWord_310434) baseStart_310434 baseEnd_310434 := by
    simpa [prefixWord, tailWord_310434, baseEnd_310434] using wordTrace_append hprefix tailTrace_310434
  have hstable : (prefixWord ++ tailWord_310434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310434).length < 2 ^ (prefixWord ++ tailWord_310434).sum := by decide
  have hdescent : baseEnd_310434 < baseStart_310434 := by decide
  rcases family_descends (prefixWord ++ tailWord_310434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310456 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_310456 : Nat := 118140960795 + 310456 * 2 ^ 59
def prefixEnd_310456 : Nat := 4983230072969 + 3 ^ 40 * 310456 * 2
def baseEnd_310456 : Nat := 106275433381561715448163

theorem tailTrace_310456 : CollatzResearch.WordTrace tailWord_310456 prefixEnd_310456 106275433381561715448163 := by
  unfold tailWord_310456
  simp only [CollatzResearch.WordTrace]
  refine ⟨5661630281639204254319611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7548840375518939005759481 5661630281639204254319611)
  ·
    refine ⟨8492445422458806381479417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5661630281639204254319611 8492445422458806381479417)
    ·
      refine ⟨6369334066844104786109563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8492445422458806381479417 6369334066844104786109563)
      ·
        refine ⟨9554001100266157179164345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6369334066844104786109563 9554001100266157179164345)
        ·
          refine ⟨7165500825199617884373259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9554001100266157179164345 7165500825199617884373259)
          ·
            refine ⟨10748251237799426826559889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7165500825199617884373259 10748251237799426826559889)
            ·
              refine ⟨8061188428349570119919917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10748251237799426826559889 8061188428349570119919917)
              ·
                refine ⟨3022945660631088794969969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8061188428349570119919917 3022945660631088794969969)
                ·
                  refine ⟨2267209245473316596227477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022945660631088794969969 2267209245473316596227477)
                  ·
                    refine ⟨106275433381561715448163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2267209245473316596227477 106275433381561715448163)
                    ·
                      rfl

theorem cell22_310456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_310456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310456 prefixEnd_310456 := by exact prefixLift 310456
  have htrace : WordTrace (prefixWord ++ tailWord_310456) baseStart_310456 baseEnd_310456 := by
    simpa [prefixWord, tailWord_310456, baseEnd_310456] using wordTrace_append hprefix tailTrace_310456
  have hstable : (prefixWord ++ tailWord_310456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310456).length < 2 ^ (prefixWord ++ tailWord_310456).sum := by decide
  have hdescent : baseEnd_310456 < baseStart_310456 := by decide
  rcases family_descends (prefixWord ++ tailWord_310456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310477 : List Nat := [1, 6, 2, 2, 1, 1, 1, 8]
def baseStart_310477 : Nat := 118140960795 + 310477 * 2 ^ 59
def prefixEnd_310477 : Nat := 4983230072969 + 3 ^ 40 * 310477 * 2
def baseEnd_310477 : Nat := 11809180234524962297011

theorem tailTrace_310477 : CollatzResearch.WordTrace tailWord_310477 prefixEnd_310477 11809180234524962297011 := by
  unfold tailWord_310477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11324026496202329095153685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7549350997468219396769123 11324026496202329095153685)
  ·
    refine ⟨530813742009484176335329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11324026496202329095153685 530813742009484176335329)
    ·
      refine ⟨398110306507113132251497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 530813742009484176335329 398110306507113132251497)
      ·
        refine ⟨298582729880334849188623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398110306507113132251497 298582729880334849188623)
        ·
          refine ⟨447874094820502273782935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298582729880334849188623 447874094820502273782935)
          ·
            refine ⟨671811142230753410674403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447874094820502273782935 671811142230753410674403)
            ·
              refine ⟨1007716713346130116011605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671811142230753410674403 1007716713346130116011605)
              ·
                refine ⟨11809180234524962297011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1007716713346130116011605 11809180234524962297011)
                ·
                  rfl

theorem cell22_310477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 8].length) (baseStart_310477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310477 prefixEnd_310477 := by exact prefixLift 310477
  have htrace : WordTrace (prefixWord ++ tailWord_310477) baseStart_310477 baseEnd_310477 := by
    simpa [prefixWord, tailWord_310477, baseEnd_310477] using wordTrace_append hprefix tailTrace_310477
  have hstable : (prefixWord ++ tailWord_310477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310477).length < 2 ^ (prefixWord ++ tailWord_310477).sum := by decide
  have hdescent : baseEnd_310477 < baseStart_310477 := by decide
  rcases family_descends (prefixWord ++ tailWord_310477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310518 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_310518 : Nat := 118140960795 + 310518 * 2 ^ 59
def prefixEnd_310518 : Nat := 4983230072969 + 3 ^ 40 * 310518 * 2
def baseEnd_310518 : Nat := 106296657248614220397973

theorem tailTrace_310518 : CollatzResearch.WordTrace tailWord_310518 prefixEnd_310518 106296657248614220397973 := by
  unfold tailWord_310518
  simp only [CollatzResearch.WordTrace]
  refine ⟨707845118065862068587263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7550347926035862064930805 707845118065862068587263)
  ·
    refine ⟨1061767677098793102880895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 707845118065862068587263 1061767677098793102880895)
    ·
      refine ⟨1592651515648189654321343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1061767677098793102880895 1592651515648189654321343)
      ·
        refine ⟨2388977273472284481482015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592651515648189654321343 2388977273472284481482015)
        ·
          refine ⟨3583465910208426722223023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388977273472284481482015 3583465910208426722223023)
          ·
            refine ⟨5375198865312640083334535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583465910208426722223023 5375198865312640083334535)
            ·
              refine ⟨8062798297968960125001803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375198865312640083334535 8062798297968960125001803)
              ·
                refine ⟨12094197446953440187502705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062798297968960125001803 12094197446953440187502705)
                ·
                  refine ⟨9070648085215080140627029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12094197446953440187502705 9070648085215080140627029)
                  ·
                    refine ⟨106296657248614220397973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9070648085215080140627029 106296657248614220397973)
                    ·
                      rfl

theorem cell22_310518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_310518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310518 prefixEnd_310518 := by exact prefixLift 310518
  have htrace : WordTrace (prefixWord ++ tailWord_310518) baseStart_310518 baseEnd_310518 := by
    simpa [prefixWord, tailWord_310518, baseEnd_310518] using wordTrace_append hprefix tailTrace_310518
  have hstable : (prefixWord ++ tailWord_310518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310518).length < 2 ^ (prefixWord ++ tailWord_310518).sum := by decide
  have hdescent : baseEnd_310518 < baseStart_310518 := by decide
  rcases family_descends (prefixWord ++ tailWord_310518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310552 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 1, 4]
def baseStart_310552 : Nat := 118140960795 + 310552 * 2 ^ 59
def prefixEnd_310552 : Nat := 4983230072969 + 3 ^ 40 * 310552 * 2
def baseEnd_310552 : Nat := 106308296143449465047869

theorem tailTrace_310552 : CollatzResearch.WordTrace tailWord_310552 prefixEnd_310552 106308296143449465047869 := by
  unfold tailWord_310552
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663380985465308452066955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7551174647287077936089273 5663380985465308452066955)
  ·
    refine ⟨8495071478197962678100433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5663380985465308452066955 8495071478197962678100433)
    ·
      refine ⟨6371303608648472008575325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8495071478197962678100433 6371303608648472008575325)
      ·
        refine ⟨2389238853243177003215747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6371303608648472008575325 2389238853243177003215747)
        ·
          refine ⟨3583858279864765504823621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389238853243177003215747 3583858279864765504823621)
          ·
            refine ⟨671973427474643532154429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3583858279864765504823621 671973427474643532154429)
            ·
              refine ⟨251990035302991324557911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 671973427474643532154429 251990035302991324557911)
              ·
                refine ⟨377985052954486986836867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251990035302991324557911 377985052954486986836867)
                ·
                  refine ⟨566977579431730480255301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377985052954486986836867 566977579431730480255301)
                  ·
                    refine ⟨106308296143449465047869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 566977579431730480255301 106308296143449465047869)
                    ·
                      rfl

theorem cell22_310552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_310552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310552 prefixEnd_310552 := by exact prefixLift 310552
  have htrace : WordTrace (prefixWord ++ tailWord_310552) baseStart_310552 baseEnd_310552 := by
    simpa [prefixWord, tailWord_310552, baseEnd_310552] using wordTrace_append hprefix tailTrace_310552
  have hstable : (prefixWord ++ tailWord_310552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310552).length < 2 ^ (prefixWord ++ tailWord_310552).sum := by decide
  have hdescent : baseEnd_310552 < baseStart_310552 := by decide
  rcases family_descends (prefixWord ++ tailWord_310552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310580 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_310580 : Nat := 118140960795 + 310580 * 2 ^ 59
def prefixEnd_310580 : Nat := 4983230072969 + 3 ^ 40 * 310580 * 2
def baseEnd_310580 : Nat := 106317881115666725347783

theorem tailTrace_310580 : CollatzResearch.WordTrace tailWord_310580 prefixEnd_310580 106317881115666725347783 := by
  unfold tailWord_310580
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663891607414588843076597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7551855476552785124102129 5663891607414588843076597)
  ·
    refine ⟨530989838195117704038431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5663891607414588843076597 530989838195117704038431)
    ·
      refine ⟨796484757292676556057647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530989838195117704038431 796484757292676556057647)
      ·
        refine ⟨1194727135939014834086471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 796484757292676556057647 1194727135939014834086471)
        ·
          refine ⟨1792090703908522251129707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194727135939014834086471 1792090703908522251129707)
          ·
            refine ⟨2688136055862783376694561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792090703908522251129707 2688136055862783376694561)
            ·
              refine ⟨2016102041897087532520921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2688136055862783376694561 2016102041897087532520921)
              ·
                refine ⟨1512076531422815649390691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016102041897087532520921 1512076531422815649390691)
                ·
                  refine ⟨2268114797134223474086037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512076531422815649390691 2268114797134223474086037)
                  ·
                    refine ⟨106317881115666725347783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2268114797134223474086037 106317881115666725347783)
                    ·
                      rfl

theorem cell22_310580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_310580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310580 prefixEnd_310580 := by exact prefixLift 310580
  have htrace : WordTrace (prefixWord ++ tailWord_310580) baseStart_310580 baseEnd_310580 := by
    simpa [prefixWord, tailWord_310580, baseEnd_310580] using wordTrace_append hprefix tailTrace_310580
  have hstable : (prefixWord ++ tailWord_310580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310580).length < 2 ^ (prefixWord ++ tailWord_310580).sum := by decide
  have hdescent : baseEnd_310580 < baseStart_310580 := by decide
  rcases family_descends (prefixWord ++ tailWord_310580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310610 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_310610 : Nat := 118140960795 + 310610 * 2 ^ 59
def prefixEnd_310610 : Nat := 4983230072969 + 3 ^ 40 * 310610 * 2
def baseEnd_310610 : Nat := 106328150728756647097691

theorem tailTrace_310610 : CollatzResearch.WordTrace tailWord_310610 prefixEnd_310610 106328150728756647097691 := by
  unfold tailWord_310610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832219351180123202436321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7552584936480328539830189 2832219351180123202436321)
  ·
    refine ⟨2124164513385092401827241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2832219351180123202436321 2124164513385092401827241)
    ·
      refine ⟨1593123385038819301370431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2124164513385092401827241 1593123385038819301370431)
      ·
        refine ⟨2389685077558228952055647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593123385038819301370431 2389685077558228952055647)
        ·
          refine ⟨3584527616337343428083471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389685077558228952055647 3584527616337343428083471)
          ·
            refine ⟨5376791424506015142125207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584527616337343428083471 5376791424506015142125207)
            ·
              refine ⟨8065187136759022713187811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376791424506015142125207 8065187136759022713187811)
              ·
                refine ⟨12097780705138534069781717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8065187136759022713187811 12097780705138534069781717)
                ·
                  refine ⟨283541735276684392260509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12097780705138534069781717 283541735276684392260509)
                  ·
                    refine ⟨106328150728756647097691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283541735276684392260509 106328150728756647097691)
                    ·
                      rfl

theorem cell22_310610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_310610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310610 prefixEnd_310610 := by exact prefixLift 310610
  have htrace : WordTrace (prefixWord ++ tailWord_310610) baseStart_310610 baseEnd_310610 := by
    simpa [prefixWord, tailWord_310610, baseEnd_310610] using wordTrace_append hprefix tailTrace_310610
  have hstable : (prefixWord ++ tailWord_310610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310610).length < 2 ^ (prefixWord ++ tailWord_310610).sum := by decide
  have hdescent : baseEnd_310610 < baseStart_310610 := by decide
  rcases family_descends (prefixWord ++ tailWord_310610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310627 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 3, 3]
def baseStart_310627 : Nat := 118140960795 + 310627 * 2 ^ 59
def prefixEnd_310627 : Nat := 4983230072969 + 3 ^ 40 * 310627 * 2
def baseEnd_310627 : Nat := 106333970176174269422639

theorem tailTrace_310627 : CollatzResearch.WordTrace tailWord_310627 prefixEnd_310627 106333970176174269422639 := by
  unfold tailWord_310627
  simp only [CollatzResearch.WordTrace]
  refine ⟨11329497445658904713114135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7552998297105936475409423 11329497445658904713114135)
  ·
    refine ⟨16994246168488357069671203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11329497445658904713114135 16994246168488357069671203)
    ·
      refine ⟨25491369252732535604506805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16994246168488357069671203 25491369252732535604506805)
      ·
        refine ⟨2389815867443675212922513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25491369252732535604506805 2389815867443675212922513)
        ·
          refine ⟨1792361900582756409691885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2389815867443675212922513 1792361900582756409691885)
          ·
            refine ⟨672135712718533653634457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1792361900582756409691885 672135712718533653634457)
            ·
              refine ⟨504101784538900240225843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672135712718533653634457 504101784538900240225843)
              ·
                refine ⟨756152676808350360338765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504101784538900240225843 756152676808350360338765)
                ·
                  refine ⟨283557253803131385127037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756152676808350360338765 283557253803131385127037)
                  ·
                    refine ⟨106333970176174269422639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283557253803131385127037 106333970176174269422639)
                    ·
                      rfl

theorem cell22_310627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 3].length) (baseStart_310627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310627 prefixEnd_310627 := by exact prefixLift 310627
  have htrace : WordTrace (prefixWord ++ tailWord_310627) baseStart_310627 baseEnd_310627 := by
    simpa [prefixWord, tailWord_310627, baseEnd_310627] using wordTrace_append hprefix tailTrace_310627
  have hstable : (prefixWord ++ tailWord_310627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310627).length < 2 ^ (prefixWord ++ tailWord_310627).sum := by decide
  have hdescent : baseEnd_310627 < baseStart_310627 := by decide
  rcases family_descends (prefixWord ++ tailWord_310627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310732 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_310732 : Nat := 118140960795 + 310732 * 2 ^ 59
def prefixEnd_310732 : Nat := 4983230072969 + 3 ^ 40 * 310732 * 2
def baseEnd_310732 : Nat := 106369913821988995547317

theorem tailTrace_310732 : CollatzResearch.WordTrace tailWord_310732 prefixEnd_310732 106369913821988995547317 := by
  unfold tailWord_310732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666663555139253822843225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7555551406852338430457633 5666663555139253822843225)
  ·
    refine ⟨4249997666354440367132419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5666663555139253822843225 4249997666354440367132419)
    ·
      refine ⟨6374996499531660550698629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4249997666354440367132419 6374996499531660550698629)
      ·
        refine ⟨1195311843662186353255993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6374996499531660550698629 1195311843662186353255993)
        ·
          refine ⟨896483882746639764941995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1195311843662186353255993 896483882746639764941995)
          ·
            refine ⟨1344725824119959647412993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896483882746639764941995 1344725824119959647412993)
            ·
              refine ⟨1008544368089969735559745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1344725824119959647412993 1008544368089969735559745)
              ·
                refine ⟨756408276067477301669809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008544368089969735559745 756408276067477301669809)
                ·
                  refine ⟨567306207050607976252357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756408276067477301669809 567306207050607976252357)
                  ·
                    refine ⟨106369913821988995547317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 567306207050607976252357 106369913821988995547317)
                    ·
                      rfl

theorem cell22_310732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_310732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310732 prefixEnd_310732 := by exact prefixLift 310732
  have htrace : WordTrace (prefixWord ++ tailWord_310732) baseStart_310732 baseEnd_310732 := by
    simpa [prefixWord, tailWord_310732, baseEnd_310732] using wordTrace_append hprefix tailTrace_310732
  have hstable : (prefixWord ++ tailWord_310732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310732).length < 2 ^ (prefixWord ++ tailWord_310732).sum := by decide
  have hdescent : baseEnd_310732 < baseStart_310732 := by decide
  rcases family_descends (prefixWord ++ tailWord_310732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310760 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_310760 : Nat := 118140960795 + 310760 * 2 ^ 59
def prefixEnd_310760 : Nat := 4983230072969 + 3 ^ 40 * 310760 * 2
def baseEnd_310760 : Nat := 106379498794206255847231

theorem tailTrace_310760 : CollatzResearch.WordTrace tailWord_310760 prefixEnd_310760 106379498794206255847231 := by
  unfold tailWord_310760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667174177088534213852867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7556232236118045618470489 5667174177088534213852867)
  ·
    refine ⟨8500761265632801320779301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5667174177088534213852867 8500761265632801320779301)
    ·
      refine ⟨1593892737306150247646119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8500761265632801320779301 1593892737306150247646119)
      ·
        refine ⟨2390839105959225371469179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593892737306150247646119 2390839105959225371469179)
        ·
          refine ⟨3586258658938838057203769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390839105959225371469179 3586258658938838057203769)
          ·
            refine ⟨2689693994204128542902827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3586258658938838057203769 2689693994204128542902827)
            ·
              refine ⟨4034540991306192814354241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689693994204128542902827 4034540991306192814354241)
              ·
                refine ⟨3025905743479644610765681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4034540991306192814354241 3025905743479644610765681)
                ·
                  refine ⟨2269429307609733458074261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025905743479644610765681 2269429307609733458074261)
                  ·
                    refine ⟨106379498794206255847231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2269429307609733458074261 106379498794206255847231)
                    ·
                      rfl

theorem cell22_310760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_310760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310760 prefixEnd_310760 := by exact prefixLift 310760
  have htrace : WordTrace (prefixWord ++ tailWord_310760) baseStart_310760 baseEnd_310760 := by
    simpa [prefixWord, tailWord_310760, baseEnd_310760] using wordTrace_append hprefix tailTrace_310760
  have hstable : (prefixWord ++ tailWord_310760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310760).length < 2 ^ (prefixWord ++ tailWord_310760).sum := by decide
  have hdescent : baseEnd_310760 < baseStart_310760 := by decide
  rcases family_descends (prefixWord ++ tailWord_310760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310792 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 5]
def baseStart_310792 : Nat := 118140960795 + 310792 * 2 ^ 59
def prefixEnd_310792 : Nat := 4983230072969 + 3 ^ 40 * 310792 * 2
def baseEnd_310792 : Nat := 35463484349389613015711

theorem tailTrace_310792 : CollatzResearch.WordTrace tailWord_310792 prefixEnd_310792 35463484349389613015711 := by
  unfold tailWord_310792
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667757745030568946435315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7557010326707425261913753 5667757745030568946435315)
  ·
    refine ⟨8501636617545853419652973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5667757745030568946435315 8501636617545853419652973)
    ·
      refine ⟨3188113731579695032369865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8501636617545853419652973 3188113731579695032369865)
      ·
        refine ⟨2391085298684771274277399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3188113731579695032369865 2391085298684771274277399)
        ·
          refine ⟨3586627948027156911416099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391085298684771274277399 3586627948027156911416099)
          ·
            refine ⟨5379941922040735367124149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586627948027156911416099 5379941922040735367124149)
            ·
              refine ⟨504369555191318940667889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5379941922040735367124149 504369555191318940667889)
              ·
                refine ⟨378277166393489205500917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504369555191318940667889 378277166393489205500917)
                ·
                  refine ⟨35463484349389613015711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 378277166393489205500917 35463484349389613015711)
                  ·
                    rfl

theorem cell22_310792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_310792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310792 prefixEnd_310792 := by exact prefixLift 310792
  have htrace : WordTrace (prefixWord ++ tailWord_310792) baseStart_310792 baseEnd_310792 := by
    simpa [prefixWord, tailWord_310792, baseEnd_310792] using wordTrace_append hprefix tailTrace_310792
  have hstable : (prefixWord ++ tailWord_310792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310792).length < 2 ^ (prefixWord ++ tailWord_310792).sum := by decide
  have hdescent : baseEnd_310792 < baseStart_310792 := by decide
  rcases family_descends (prefixWord ++ tailWord_310792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310884 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_310884 : Nat := 118140960795 + 310884 * 2 ^ 59
def prefixEnd_310884 : Nat := 4983230072969 + 3 ^ 40 * 310884 * 2
def baseEnd_310884 : Nat := 106421946528311265746851

theorem tailTrace_310884 : CollatzResearch.WordTrace tailWord_310884 prefixEnd_310884 106421946528311265746851 := by
  unfold tailWord_310884
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669435502863918802609853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7559247337151891736813137 5669435502863918802609853)
  ·
    refine ⟨2126038313573969550978695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5669435502863918802609853 2126038313573969550978695)
    ·
      refine ⟨3189057470360954326468043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126038313573969550978695 3189057470360954326468043)
      ·
        refine ⟨4783586205541431489702065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189057470360954326468043 4783586205541431489702065)
        ·
          refine ⟨3587689654156073617276549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4783586205541431489702065 3587689654156073617276549)
          ·
            refine ⟨672691810154263803239353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3587689654156073617276549 672691810154263803239353)
            ·
              refine ⟨504518857615697852429515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672691810154263803239353 504518857615697852429515)
              ·
                refine ⟨756778286423546778644273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504518857615697852429515 756778286423546778644273)
                ·
                  refine ⟨567583714817660083983205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756778286423546778644273 567583714817660083983205)
                  ·
                    refine ⟨106421946528311265746851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 567583714817660083983205 106421946528311265746851)
                    ·
                      rfl

theorem cell22_310884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_310884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310884 prefixEnd_310884 := by exact prefixLift 310884
  have htrace : WordTrace (prefixWord ++ tailWord_310884) baseStart_310884 baseEnd_310884 := by
    simpa [prefixWord, tailWord_310884, baseEnd_310884] using wordTrace_append hprefix tailTrace_310884
  have hstable : (prefixWord ++ tailWord_310884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310884).length < 2 ^ (prefixWord ++ tailWord_310884).sum := by decide
  have hdescent : baseEnd_310884 < baseStart_310884 := by decide
  rcases family_descends (prefixWord ++ tailWord_310884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310916 : List Nat := [2, 3, 2, 1, 5, 1, 1, 7]
def baseStart_310916 : Nat := 118140960795 + 310916 * 2 ^ 59
def prefixEnd_310916 : Nat := 4983230072969 + 3 ^ 40 * 310916 * 2
def baseEnd_310916 : Nat := 11825877864697094327417

theorem tailTrace_310916 : CollatzResearch.WordTrace tailWord_310916 prefixEnd_310916 11825877864697094327417 := by
  unfold tailWord_310916
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670019070805953535192301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7560025427741271380256401 5670019070805953535192301)
  ·
    refine ⟨2126257151552232575697113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5670019070805953535192301 2126257151552232575697113)
    ·
      refine ⟨1594692863664174431772835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2126257151552232575697113 1594692863664174431772835)
      ·
        refine ⟨2392039295496261647659253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1594692863664174431772835 2392039295496261647659253)
        ·
          refine ⟨224253683952774529468055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2392039295496261647659253 224253683952774529468055)
          ·
            refine ⟨336380525929161794202083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224253683952774529468055 336380525929161794202083)
            ·
              refine ⟨504570788893742691303125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336380525929161794202083 504570788893742691303125)
              ·
                refine ⟨11825877864697094327417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 504570788893742691303125 11825877864697094327417)
                ·
                  rfl

theorem cell22_310916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 7].length) (baseStart_310916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310916 prefixEnd_310916 := by exact prefixLift 310916
  have htrace : WordTrace (prefixWord ++ tailWord_310916) baseStart_310916 baseEnd_310916 := by
    simpa [prefixWord, tailWord_310916, baseEnd_310916] using wordTrace_append hprefix tailTrace_310916
  have hstable : (prefixWord ++ tailWord_310916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310916).length < 2 ^ (prefixWord ++ tailWord_310916).sum := by decide
  have hdescent : baseEnd_310916 < baseStart_310916 := by decide
  rcases family_descends (prefixWord ++ tailWord_310916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310948 : List Nat := [2, 3, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_310948 : Nat := 118140960795 + 310948 * 2 ^ 59
def prefixEnd_310948 : Nat := 4983230072969 + 3 ^ 40 * 310948 * 2
def baseEnd_310948 : Nat := 106443855036236432146655

theorem tailTrace_310948 : CollatzResearch.WordTrace tailWord_310948 prefixEnd_310948 106443855036236432146655 := by
  unfold tailWord_310948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670602638747988267774749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7560803518330651023699665 5670602638747988267774749)
  ·
    refine ⟨2126475989530495600415531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5670602638747988267774749 2126475989530495600415531)
    ·
      refine ⟨3189713984295743400623297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126475989530495600415531 3189713984295743400623297)
      ·
        refine ⟨2392285488221807550467473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3189713984295743400623297 2392285488221807550467473)
        ·
          refine ⟨1794214116166355662850605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2392285488221807550467473 1794214116166355662850605)
          ·
            refine ⟨672830293562383373568977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1794214116166355662850605 672830293562383373568977)
            ·
              refine ⟨504622720171787530176733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 672830293562383373568977 504622720171787530176733)
              ·
                refine ⟨189233520064420323816275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504622720171787530176733 189233520064420323816275)
                ·
                  refine ⟨283850280096630485724413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189233520064420323816275 283850280096630485724413)
                  ·
                    refine ⟨106443855036236432146655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283850280096630485724413 106443855036236432146655)
                    ·
                      rfl

theorem cell22_310948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_310948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_310948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_310948 prefixEnd_310948 := by exact prefixLift 310948
  have htrace : WordTrace (prefixWord ++ tailWord_310948) baseStart_310948 baseEnd_310948 := by
    simpa [prefixWord, tailWord_310948, baseEnd_310948] using wordTrace_append hprefix tailTrace_310948
  have hstable : (prefixWord ++ tailWord_310948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310948).length < 2 ^ (prefixWord ++ tailWord_310948).sum := by decide
  have hdescent : baseEnd_310948 < baseStart_310948 := by decide
  rcases family_descends (prefixWord ++ tailWord_310948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311021 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_311021 : Nat := 118140960795 + 311021 * 2 ^ 59
def prefixEnd_311021 : Nat := 4983230072969 + 3 ^ 40 * 311021 * 2
def baseEnd_311021 : Nat := 106468844428088575071431

theorem tailTrace_311021 : CollatzResearch.WordTrace tailWord_311021 prefixEnd_311021 106468844428088575071431 := by
  unfold tailWord_311021
  simp only [CollatzResearch.WordTrace]
  refine ⟨11343867806231510002956917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7562578537487673335304611 11343867806231510002956917)
  ·
    refine ⟨1063487606834204062777211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11343867806231510002956917 1063487606834204062777211)
    ·
      refine ⟨1595231410251306094165817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1063487606834204062777211 1595231410251306094165817)
      ·
        refine ⟨1196423557688479570624363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1595231410251306094165817 1196423557688479570624363)
        ·
          refine ⟨1794635336532719355936545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1196423557688479570624363 1794635336532719355936545)
          ·
            refine ⟨1345976502399539516952409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794635336532719355936545 1345976502399539516952409)
            ·
              refine ⟨1009482376799654637714307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345976502399539516952409 1009482376799654637714307)
              ·
                refine ⟨1514223565199481956571461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009482376799654637714307 1514223565199481956571461)
                ·
                  refine ⟨283916918474902866857149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1514223565199481956571461 283916918474902866857149)
                  ·
                    refine ⟨106468844428088575071431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283916918474902866857149 106468844428088575071431)
                    ·
                      rfl

theorem cell22_311021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_311021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311021 prefixEnd_311021 := by exact prefixLift 311021
  have htrace : WordTrace (prefixWord ++ tailWord_311021) baseStart_311021 baseEnd_311021 := by
    simpa [prefixWord, tailWord_311021, baseEnd_311021] using wordTrace_append hprefix tailTrace_311021
  have hstable : (prefixWord ++ tailWord_311021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311021).length < 2 ^ (prefixWord ++ tailWord_311021).sum := by decide
  have hdescent : baseEnd_311021 < baseStart_311021 := by decide
  rcases family_descends (prefixWord ++ tailWord_311021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311032 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_311032 : Nat := 118140960795 + 311032 * 2 ^ 59
def prefixEnd_311032 : Nat := 4983230072969 + 3 ^ 40 * 311032 * 2
def baseEnd_311032 : Nat := 106472609952888213046397

theorem tailTrace_311032 : CollatzResearch.WordTrace tailWord_311032 prefixEnd_311032 106472609952888213046397 := by
  unfold tailWord_311032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5672134504595829440803675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7562846006127772587738233 5672134504595829440803675)
  ·
    refine ⟨8508201756893744161205513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5672134504595829440803675 8508201756893744161205513)
    ·
      refine ⟨6381151317670308120904135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8508201756893744161205513 6381151317670308120904135)
      ·
        refine ⟨9571726976505462181356203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6381151317670308120904135 9571726976505462181356203)
        ·
          refine ⟨14357590464758193272034305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9571726976505462181356203 14357590464758193272034305)
          ·
            refine ⟨10768192848568644954025729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14357590464758193272034305 10768192848568644954025729)
            ·
              refine ⟨8076144636426483715519297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10768192848568644954025729 8076144636426483715519297)
              ·
                refine ⟨6057108477319862786639473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8076144636426483715519297 6057108477319862786639473)
                ·
                  refine ⟨4542831357989897089979605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6057108477319862786639473 4542831357989897089979605)
                  ·
                    refine ⟨106472609952888213046397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4542831357989897089979605 106472609952888213046397)
                    ·
                      rfl

theorem cell22_311032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_311032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311032 prefixEnd_311032 := by exact prefixLift 311032
  have htrace : WordTrace (prefixWord ++ tailWord_311032) baseStart_311032 baseEnd_311032 := by
    simpa [prefixWord, tailWord_311032, baseEnd_311032] using wordTrace_append hprefix tailTrace_311032
  have hstable : (prefixWord ++ tailWord_311032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311032).length < 2 ^ (prefixWord ++ tailWord_311032).sum := by decide
  have hdescent : baseEnd_311032 < baseStart_311032 := by decide
  rcases family_descends (prefixWord ++ tailWord_311032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311049 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 5, 3]
def baseStart_311049 : Nat := 118140960795 + 311049 * 2 ^ 59
def prefixEnd_311049 : Nat := 4983230072969 + 3 ^ 40 * 311049 * 2
def baseEnd_311049 : Nat := 106478429400305835371345

theorem tailTrace_311049 : CollatzResearch.WordTrace tailWord_311049 prefixEnd_311049 106478429400305835371345 := by
  unfold tailWord_311049
  simp only [CollatzResearch.WordTrace]
  refine ⟨11344889050130070784976201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7563259366753380523317467 11344889050130070784976201)
  ·
    refine ⟨8508666787597553088732151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11344889050130070784976201 8508666787597553088732151)
    ·
      refine ⟨12763000181396329633098227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8508666787597553088732151 12763000181396329633098227)
      ·
        refine ⟨19144500272094494449647341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12763000181396329633098227 19144500272094494449647341)
        ·
          refine ⟨7179187602035435418617753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19144500272094494449647341 7179187602035435418617753)
          ·
            refine ⟨5384390701526576563963315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7179187602035435418617753 5384390701526576563963315)
            ·
              refine ⟨8076586052289864845944973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5384390701526576563963315 8076586052289864845944973)
              ·
                refine ⟨3028719769608699317229365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8076586052289864845944973 3028719769608699317229365)
                ·
                  refine ⟨283942478400815560990253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3028719769608699317229365 283942478400815560990253)
                  ·
                    refine ⟨106478429400305835371345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 283942478400815560990253 106478429400305835371345)
                    ·
                      rfl

theorem cell22_311049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 3].length) (baseStart_311049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311049 prefixEnd_311049 := by exact prefixLift 311049
  have htrace : WordTrace (prefixWord ++ tailWord_311049) baseStart_311049 baseEnd_311049 := by
    simpa [prefixWord, tailWord_311049, baseEnd_311049] using wordTrace_append hprefix tailTrace_311049
  have hstable : (prefixWord ++ tailWord_311049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311049).length < 2 ^ (prefixWord ++ tailWord_311049).sum := by decide
  have hdescent : baseEnd_311049 < baseStart_311049 := by decide
  rcases family_descends (prefixWord ++ tailWord_311049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311109 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 3, 4]
def baseStart_311109 : Nat := 118140960795 + 311109 * 2 ^ 59
def prefixEnd_311109 : Nat := 4983230072969 + 3 ^ 40 * 311109 * 2
def baseEnd_311109 : Nat := 106498968626485678871161

theorem tailTrace_311109 : CollatzResearch.WordTrace tailWord_311109 prefixEnd_311109 106498968626485678871161 := by
  unfold tailWord_311109
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347077429912701032160381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7564718286608467354773587 11347077429912701032160381)
  ·
    refine ⟨4255154036217262887060143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11347077429912701032160381 4255154036217262887060143)
    ·
      refine ⟨6382731054325894330590215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4255154036217262887060143 6382731054325894330590215)
      ·
        refine ⟨9574096581488841495885323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6382731054325894330590215 9574096581488841495885323)
        ·
          refine ⟨14361144872233262243827985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9574096581488841495885323 14361144872233262243827985)
          ·
            refine ⟨10770858654174946682870989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14361144872233262243827985 10770858654174946682870989)
            ·
              refine ⟨4039071995315605006076621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10770858654174946682870989 4039071995315605006076621)
              ·
                refine ⟨1514651998243351877278733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4039071995315605006076621 1514651998243351877278733)
                ·
                  refine ⟨567994499341256953979525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1514651998243351877278733 567994499341256953979525)
                  ·
                    refine ⟨106498968626485678871161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 567994499341256953979525 106498968626485678871161)
                    ·
                      rfl

theorem cell22_311109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_311109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311109 prefixEnd_311109 := by exact prefixLift 311109
  have htrace : WordTrace (prefixWord ++ tailWord_311109) baseStart_311109 baseEnd_311109 := by
    simpa [prefixWord, tailWord_311109, baseEnd_311109] using wordTrace_append hprefix tailTrace_311109
  have hstable : (prefixWord ++ tailWord_311109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311109).length < 2 ^ (prefixWord ++ tailWord_311109).sum := by decide
  have hdescent : baseEnd_311109 < baseStart_311109 := by decide
  rcases family_descends (prefixWord ++ tailWord_311109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311117 : List Nat := [1, 6, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_311117 : Nat := 118140960795 + 311117 * 2 ^ 59
def prefixEnd_311117 : Nat := 4983230072969 + 3 ^ 40 * 311117 * 2
def baseEnd_311117 : Nat := 106501707189976324671137

theorem tailTrace_311117 : CollatzResearch.WordTrace tailWord_311117 prefixEnd_311117 106501707189976324671137 := by
  unfold tailWord_311117
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347369213883718398451605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7564912809255812265634403 11347369213883718398451605)
  ·
    refine ⟨531907931900799299927419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11347369213883718398451605 531907931900799299927419)
    ·
      refine ⟨797861897851198949891129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531907931900799299927419 797861897851198949891129)
      ·
        refine ⟨598396423388399212418347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797861897851198949891129 598396423388399212418347)
        ·
          refine ⟨897594635082598818627521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598396423388399212418347 897594635082598818627521)
          ·
            refine ⟨673195976311949113970641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897594635082598818627521 673195976311949113970641)
            ·
              refine ⟨504896982233961835477981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673195976311949113970641 504896982233961835477981)
              ·
                refine ⟨189336368337735688304243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504896982233961835477981 189336368337735688304243)
                ·
                  refine ⟨284004552506603532456365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189336368337735688304243 284004552506603532456365)
                  ·
                    refine ⟨106501707189976324671137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284004552506603532456365 106501707189976324671137)
                    ·
                      rfl

theorem cell22_311117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_311117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311117 prefixEnd_311117 := by exact prefixLift 311117
  have htrace : WordTrace (prefixWord ++ tailWord_311117) baseStart_311117 baseEnd_311117 := by
    simpa [prefixWord, tailWord_311117, baseEnd_311117] using wordTrace_append hprefix tailTrace_311117
  have hstable : (prefixWord ++ tailWord_311117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311117).length < 2 ^ (prefixWord ++ tailWord_311117).sum := by decide
  have hdescent : baseEnd_311117 < baseStart_311117 := by decide
  rcases family_descends (prefixWord ++ tailWord_311117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311175 : List Nat := [1, 1, 4, 2, 4, 2, 1, 3, 4]
def baseStart_311175 : Nat := 118140960795 + 311175 * 2 ^ 59
def prefixEnd_311175 : Nat := 4983230072969 + 3 ^ 40 * 311175 * 2
def baseEnd_311175 : Nat := 35507187258427835573653

theorem tailTrace_311175 : CollatzResearch.WordTrace tailWord_311175 prefixEnd_311175 35507187258427835573653 := by
  unfold tailWord_311175
  simp only [CollatzResearch.WordTrace]
  refine ⟨11349484647673594304062979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7566323098449062869375319 11349484647673594304062979)
  ·
    refine ⟨17024226971510391456094469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11349484647673594304062979 17024226971510391456094469)
    ·
      refine ⟨3192042557158198398017713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17024226971510391456094469 3192042557158198398017713)
      ·
        refine ⟨2394031917868648798513285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3192042557158198398017713 2394031917868648798513285)
        ·
          refine ⟨448880984600371649721241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2394031917868648798513285 448880984600371649721241)
          ·
            refine ⟨336660738450278737290931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448880984600371649721241 336660738450278737290931)
            ·
              refine ⟨504991107675418105936397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336660738450278737290931 504991107675418105936397)
              ·
                refine ⟨189371665378281789726149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504991107675418105936397 189371665378281789726149)
                ·
                  refine ⟨35507187258427835573653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189371665378281789726149 35507187258427835573653)
                  ·
                    rfl

theorem cell22_311175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 4].length) (baseStart_311175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311175 prefixEnd_311175 := by exact prefixLift 311175
  have htrace : WordTrace (prefixWord ++ tailWord_311175) baseStart_311175 baseEnd_311175 := by
    simpa [prefixWord, tailWord_311175, baseEnd_311175] using wordTrace_append hprefix tailTrace_311175
  have hstable : (prefixWord ++ tailWord_311175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311175).length < 2 ^ (prefixWord ++ tailWord_311175).sum := by decide
  have hdescent : baseEnd_311175 < baseStart_311175 := by decide
  rcases family_descends (prefixWord ++ tailWord_311175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311186 : List Nat := [3, 2, 3, 2, 1, 1, 10]
def baseStart_311186 : Nat := 118140960795 + 311186 * 2 ^ 59
def prefixEnd_311186 : Nat := 4983230072969 + 3 ^ 40 * 311186 * 2
def baseEnd_311186 : Nat := 3945382492595672025775

theorem tailTrace_311186 : CollatzResearch.WordTrace tailWord_311186 prefixEnd_311186 3945382492595672025775 := by
  unfold tailWord_311186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837471462658435795678353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7566590567089162121808941 2837471462658435795678353)
  ·
    refine ⟨2128103596993826846758765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2837471462658435795678353 2128103596993826846758765)
    ·
      refine ⟨798038848872685067534537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2128103596993826846758765 798038848872685067534537)
      ·
        refine ⟨598529136654513800650903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 798038848872685067534537 598529136654513800650903)
        ·
          refine ⟨897793704981770700976355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598529136654513800650903 897793704981770700976355)
          ·
            refine ⟨1346690557472656051464533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897793704981770700976355 1346690557472656051464533)
            ·
              refine ⟨3945382492595672025775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1346690557472656051464533 3945382492595672025775)
              ·
                rfl

theorem cell22_311186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 10].length) (baseStart_311186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311186 prefixEnd_311186 := by exact prefixLift 311186
  have htrace : WordTrace (prefixWord ++ tailWord_311186) baseStart_311186 baseEnd_311186 := by
    simpa [prefixWord, tailWord_311186, baseEnd_311186] using wordTrace_append hprefix tailTrace_311186
  have hstable : (prefixWord ++ tailWord_311186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311186).length < 2 ^ (prefixWord ++ tailWord_311186).sum := by decide
  have hdescent : baseEnd_311186 < baseStart_311186 := by decide
  rcases family_descends (prefixWord ++ tailWord_311186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311188 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_311188 : Nat := 118140960795 + 311188 * 2 ^ 59
def prefixEnd_311188 : Nat := 4983230072969 + 3 ^ 40 * 311188 * 2
def baseEnd_311188 : Nat := 106526011940955806145919

theorem tailTrace_311188 : CollatzResearch.WordTrace tailWord_311188 prefixEnd_311188 106526011940955806145919 := by
  unfold tailWord_311188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674979398313248762143109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7566639197750998349524145 5674979398313248762143109)
  ·
    refine ⟨1064058637183734142901833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5674979398313248762143109 1064058637183734142901833)
    ·
      refine ⟨798043977887800607176375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1064058637183734142901833 798043977887800607176375)
      ·
        refine ⟨1197065966831700910764563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798043977887800607176375 1197065966831700910764563)
        ·
          refine ⟨1795598950247551366146845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1197065966831700910764563 1795598950247551366146845)
          ·
            refine ⟨673349606342831762305067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1795598950247551366146845 673349606342831762305067)
            ·
              refine ⟨1010024409514247643457601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673349606342831762305067 1010024409514247643457601)
              ·
                refine ⟨757518307135685732593201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010024409514247643457601 757518307135685732593201)
                ·
                  refine ⟨568138730351764299444901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757518307135685732593201 568138730351764299444901)
                  ·
                    refine ⟨106526011940955806145919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 568138730351764299444901 106526011940955806145919)
                    ·
                      rfl

theorem cell22_311188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_311188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311188 prefixEnd_311188 := by exact prefixLift 311188
  have htrace : WordTrace (prefixWord ++ tailWord_311188) baseStart_311188 baseEnd_311188 := by
    simpa [prefixWord, tailWord_311188, baseEnd_311188] using wordTrace_append hprefix tailTrace_311188
  have hstable : (prefixWord ++ tailWord_311188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311188).length < 2 ^ (prefixWord ++ tailWord_311188).sum := by decide
  have hdescent : baseEnd_311188 < baseStart_311188 := by decide
  rcases family_descends (prefixWord ++ tailWord_311188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311192 : List Nat := [2, 1, 2, 6, 1, 1, 3, 2, 4]
def baseStart_311192 : Nat := 118140960795 + 311192 * 2 ^ 59
def prefixEnd_311192 : Nat := 4983230072969 + 3 ^ 40 * 311192 * 2
def baseEnd_311192 : Nat := 35509127074233709681969

theorem tailTrace_311192 : CollatzResearch.WordTrace tailWord_311192 prefixEnd_311192 35509127074233709681969 := by
  unfold tailWord_311192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675052344306003103715915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7566736459074670804954553 5675052344306003103715915)
  ·
    refine ⟨8512578516459004655573873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5675052344306003103715915 8512578516459004655573873)
    ·
      refine ⟨6384433887344253491680405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8512578516459004655573873 6384433887344253491680405)
      ·
        refine ⟨299270338469261882422519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6384433887344253491680405 299270338469261882422519)
        ·
          refine ⟨448905507703892823633779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299270338469261882422519 448905507703892823633779)
          ·
            refine ⟨673358261555839235450669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448905507703892823633779 673358261555839235450669)
            ·
              refine ⟨252509348083439713294001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673358261555839235450669 252509348083439713294001)
              ·
                refine ⟨189382011062579784970501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252509348083439713294001 189382011062579784970501)
                ·
                  refine ⟨35509127074233709681969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189382011062579784970501 35509127074233709681969)
                  ·
                    rfl

theorem cell22_311192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_311192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311192 prefixEnd_311192 := by exact prefixLift 311192
  have htrace : WordTrace (prefixWord ++ tailWord_311192) baseStart_311192 baseEnd_311192 := by
    simpa [prefixWord, tailWord_311192, baseEnd_311192] using wordTrace_append hprefix tailTrace_311192
  have hstable : (prefixWord ++ tailWord_311192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311192).length < 2 ^ (prefixWord ++ tailWord_311192).sum := by decide
  have hdescent : baseEnd_311192 < baseStart_311192 := by decide
  rcases family_descends (prefixWord ++ tailWord_311192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311207 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 2, 3]
def baseStart_311207 : Nat := 118140960795 + 311207 * 2 ^ 59
def prefixEnd_311207 : Nat := 4983230072969 + 3 ^ 40 * 311207 * 2
def baseEnd_311207 : Nat := 106532516029246089920861

theorem tailTrace_311207 : CollatzResearch.WordTrace tailWord_311207 prefixEnd_311207 106532516029246089920861 := by
  unfold tailWord_311207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11350651783557663769227875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7567101189038442512818583 11350651783557663769227875)
  ·
    refine ⟨17025977675336495653841813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11350651783557663769227875 17025977675336495653841813)
    ·
      refine ⟨798092703531398233773835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17025977675336495653841813 798092703531398233773835)
      ·
        refine ⟨1197139055297097350660753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798092703531398233773835 1197139055297097350660753)
        ·
          refine ⟨897854291472823012995565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197139055297097350660753 897854291472823012995565)
          ·
            refine ⟨336695359302308629873337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 897854291472823012995565 336695359302308629873337)
            ·
              refine ⟨252521519476731472405003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336695359302308629873337 252521519476731472405003)
              ·
                refine ⟨378782279215097208607505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252521519476731472405003 378782279215097208607505)
                ·
                  refine ⟨284086709411322906455629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 378782279215097208607505 284086709411322906455629)
                  ·
                    refine ⟨106532516029246089920861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284086709411322906455629 106532516029246089920861)
                    ·
                      rfl

theorem cell22_311207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_311207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311207 prefixEnd_311207 := by exact prefixLift 311207
  have htrace : WordTrace (prefixWord ++ tailWord_311207) baseStart_311207 baseEnd_311207 := by
    simpa [prefixWord, tailWord_311207, baseEnd_311207] using wordTrace_append hprefix tailTrace_311207
  have hstable : (prefixWord ++ tailWord_311207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311207).length < 2 ^ (prefixWord ++ tailWord_311207).sum := by decide
  have hdescent : baseEnd_311207 < baseStart_311207 := by decide
  rcases family_descends (prefixWord ++ tailWord_311207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311246 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_311246 : Nat := 118140960795 + 311246 * 2 ^ 59
def prefixEnd_311246 : Nat := 4983230072969 + 3 ^ 40 * 311246 * 2
def baseEnd_311246 : Nat := 106545866526262988195741

theorem tailTrace_311246 : CollatzResearch.WordTrace tailWord_311246 prefixEnd_311246 106545866526262988195741 := by
  unfold tailWord_311246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1419009278802046678737199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7568049486944248953265061 1419009278802046678737199)
  ·
    refine ⟨2128513918203070018105799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1419009278802046678737199 2128513918203070018105799)
    ·
      refine ⟨3192770877304605027158699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128513918203070018105799 3192770877304605027158699)
      ·
        refine ⟨4789156315956907540738049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3192770877304605027158699 4789156315956907540738049)
        ·
          refine ⟨3591867236967680655553537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4789156315956907540738049 3591867236967680655553537)
          ·
            refine ⟨2693900427725760491665153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3591867236967680655553537 2693900427725760491665153)
            ·
              refine ⟨2020425320794320368748865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2693900427725760491665153 2020425320794320368748865)
              ·
                refine ⟨1515318990595740276561649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020425320794320368748865 1515318990595740276561649)
                ·
                  refine ⟨1136489242946805207421237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1515318990595740276561649 1136489242946805207421237)
                  ·
                    refine ⟨106545866526262988195741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1136489242946805207421237 106545866526262988195741)
                    ·
                      rfl

theorem cell22_311246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_311246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311246 prefixEnd_311246 := by exact prefixLift 311246
  have htrace : WordTrace (prefixWord ++ tailWord_311246) baseStart_311246 baseEnd_311246 := by
    simpa [prefixWord, tailWord_311246, baseEnd_311246] using wordTrace_append hprefix tailTrace_311246
  have hstable : (prefixWord ++ tailWord_311246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311246).length < 2 ^ (prefixWord ++ tailWord_311246).sum := by decide
  have hdescent : baseEnd_311246 < baseStart_311246 := by decide
  rcases family_descends (prefixWord ++ tailWord_311246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311278 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_311278 : Nat := 118140960795 + 311278 * 2 ^ 59
def prefixEnd_311278 : Nat := 4983230072969 + 3 ^ 40 * 311278 * 2
def baseEnd_311278 : Nat := 106556820780225571395643

theorem tailTrace_311278 : CollatzResearch.WordTrace tailWord_311278 prefixEnd_311278 106556820780225571395643 := by
  unfold tailWord_311278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1419155170787555361882811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7568827577533628596708325 1419155170787555361882811)
  ·
    refine ⟨2128732756181333042824217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1419155170787555361882811 2128732756181333042824217)
    ·
      refine ⟨1596549567135999782118163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2128732756181333042824217 1596549567135999782118163)
      ·
        refine ⟨2394824350703999673177245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596549567135999782118163 2394824350703999673177245)
        ·
          refine ⟨898059131513999877441467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2394824350703999673177245 898059131513999877441467)
          ·
            refine ⟨1347088697270999816162201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898059131513999877441467 1347088697270999816162201)
            ·
              refine ⟨1010316522953249862121651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347088697270999816162201 1010316522953249862121651)
              ·
                refine ⟨1515474784429874793182477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010316522953249862121651 1515474784429874793182477)
                ·
                  refine ⟨568303044161203047443429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1515474784429874793182477 568303044161203047443429)
                  ·
                    refine ⟨106556820780225571395643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 568303044161203047443429 106556820780225571395643)
                    ·
                      rfl

theorem cell22_311278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_311278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311278 prefixEnd_311278 := by exact prefixLift 311278
  have htrace : WordTrace (prefixWord ++ tailWord_311278) baseStart_311278 baseEnd_311278 := by
    simpa [prefixWord, tailWord_311278, baseEnd_311278] using wordTrace_append hprefix tailTrace_311278
  have hstable : (prefixWord ++ tailWord_311278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311278).length < 2 ^ (prefixWord ++ tailWord_311278).sum := by decide
  have hdescent : baseEnd_311278 < baseStart_311278 := by decide
  rcases family_descends (prefixWord ++ tailWord_311278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311291 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 1, 5]
def baseStart_311291 : Nat := 118140960795 + 311291 * 2 ^ 59
def prefixEnd_311291 : Nat := 4983230072969 + 3 ^ 40 * 311291 * 2
def baseEnd_311291 : Nat := 106561270945897870820603

theorem tailTrace_311291 : CollatzResearch.WordTrace tailWord_311291 prefixEnd_311291 106561270945897870820603 := by
  unfold tailWord_311291
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353715515253346115285727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7569143676835564076857151 11353715515253346115285727)
  ·
    refine ⟨17030573272880019172928591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11353715515253346115285727 17030573272880019172928591)
    ·
      refine ⟨25545859909320028759392887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17030573272880019172928591 25545859909320028759392887)
      ·
        refine ⟨38318789863980043139089331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25545859909320028759392887 38318789863980043139089331)
        ·
          refine ⟨57478184795970064708633997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38318789863980043139089331 57478184795970064708633997)
          ·
            refine ⟨21554319298488774265737749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57478184795970064708633997 21554319298488774265737749)
            ·
              refine ⟨1010358717116661293706457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21554319298488774265737749 1010358717116661293706457)
              ·
                refine ⟨757769037837495970279843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010358717116661293706457 757769037837495970279843)
                ·
                  refine ⟨1136653556756243955419765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757769037837495970279843 1136653556756243955419765)
                  ·
                    refine ⟨106561270945897870820603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1136653556756243955419765 106561270945897870820603)
                    ·
                      rfl

theorem cell22_311291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_311291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311291 prefixEnd_311291 := by exact prefixLift 311291
  have htrace : WordTrace (prefixWord ++ tailWord_311291) baseStart_311291 baseEnd_311291 := by
    simpa [prefixWord, tailWord_311291, baseEnd_311291] using wordTrace_append hprefix tailTrace_311291
  have hstable : (prefixWord ++ tailWord_311291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311291).length < 2 ^ (prefixWord ++ tailWord_311291).sum := by decide
  have hdescent : baseEnd_311291 < baseStart_311291 := by decide
  rcases family_descends (prefixWord ++ tailWord_311291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311293 : List Nat := [1, 4, 1, 1, 1, 2, 3, 5, 4]
def baseStart_311293 : Nat := 118140960795 + 311293 * 2 ^ 59
def prefixEnd_311293 : Nat := 4983230072969 + 3 ^ 40 * 311293 * 2
def baseEnd_311293 : Nat := 35520651862256844090199

theorem tailTrace_311293 : CollatzResearch.WordTrace tailWord_311293 prefixEnd_311293 35520651862256844090199 := by
  unfold tailWord_311293
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353788461246100456858533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7569192307497400304572355 11353788461246100456858533)
  ·
    refine ⟨2128835336483643835660975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11353788461246100456858533 2128835336483643835660975)
    ·
      refine ⟨3193253004725465753491463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2128835336483643835660975 3193253004725465753491463)
      ·
        refine ⟨4789879507088198630237195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193253004725465753491463 4789879507088198630237195)
        ·
          refine ⟨7184819260632297945355793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789879507088198630237195 7184819260632297945355793)
          ·
            refine ⟨5388614445474223459016845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7184819260632297945355793 5388614445474223459016845)
            ·
              refine ⟨2020730417052833797131317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5388614445474223459016845 2020730417052833797131317)
              ·
                refine ⟨189443476598703168481061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2020730417052833797131317 189443476598703168481061)
                ·
                  refine ⟨35520651862256844090199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189443476598703168481061 35520651862256844090199)
                  ·
                    rfl

theorem cell22_311293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_311293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311293 prefixEnd_311293 := by exact prefixLift 311293
  have htrace : WordTrace (prefixWord ++ tailWord_311293) baseStart_311293 baseEnd_311293 := by
    simpa [prefixWord, tailWord_311293, baseEnd_311293] using wordTrace_append hprefix tailTrace_311293
  have hstable : (prefixWord ++ tailWord_311293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311293).length < 2 ^ (prefixWord ++ tailWord_311293).sum := by decide
  have hdescent : baseEnd_311293 < baseStart_311293 := by decide
  rcases family_descends (prefixWord ++ tailWord_311293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311308 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_311308 : Nat := 118140960795 + 311308 * 2 ^ 59
def prefixEnd_311308 : Nat := 4983230072969 + 3 ^ 40 * 311308 * 2
def baseEnd_311308 : Nat := 106567090393315493145551

theorem tailTrace_311308 : CollatzResearch.WordTrace tailWord_311308 prefixEnd_311308 106567090393315493145551 := by
  unfold tailWord_311308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5677167778095879009327289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7569557037461172012436385 5677167778095879009327289)
  ·
    refine ⟨4257875833571909256995467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5677167778095879009327289 4257875833571909256995467)
    ·
      refine ⟨6386813750357863885493201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4257875833571909256995467 6386813750357863885493201)
      ·
        refine ⟨4790110312768397914119901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6386813750357863885493201 4790110312768397914119901)
        ·
          refine ⟨1796291367288149217794963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4790110312768397914119901 1796291367288149217794963)
          ·
            refine ⟨2694437050932223826692445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796291367288149217794963 2694437050932223826692445)
            ·
              refine ⟨1010413894099583935009667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2694437050932223826692445 1010413894099583935009667)
              ·
                refine ⟨1515620841149375902514501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010413894099583935009667 1515620841149375902514501)
                ·
                  refine ⟨284178907715507981721469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515620841149375902514501 284178907715507981721469)
                  ·
                    refine ⟨106567090393315493145551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284178907715507981721469 106567090393315493145551)
                    ·
                      rfl

theorem cell22_311308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_311308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311308 prefixEnd_311308 := by exact prefixLift 311308
  have htrace : WordTrace (prefixWord ++ tailWord_311308) baseStart_311308 baseEnd_311308 := by
    simpa [prefixWord, tailWord_311308, baseEnd_311308] using wordTrace_append hprefix tailTrace_311308
  have hstable : (prefixWord ++ tailWord_311308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311308).length < 2 ^ (prefixWord ++ tailWord_311308).sum := by decide
  have hdescent : baseEnd_311308 < baseStart_311308 := by decide
  rcases family_descends (prefixWord ++ tailWord_311308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311325 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_311325 : Nat := 118140960795 + 311325 * 2 ^ 59
def prefixEnd_311325 : Nat := 4983230072969 + 3 ^ 40 * 311325 * 2
def baseEnd_311325 : Nat := 106572909840733115470499

theorem tailTrace_311325 : CollatzResearch.WordTrace tailWord_311325 prefixEnd_311325 106572909840733115470499 := by
  unfold tailWord_311325
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354955597130169922023429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7569970398086779948015619 11354955597130169922023429)
  ·
    refine ⟨2129054174461906860379393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11354955597130169922023429 2129054174461906860379393)
    ·
      refine ⟨1596790630846430145284545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2129054174461906860379393 1596790630846430145284545)
      ·
        refine ⟨1197592973134822608963409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1596790630846430145284545 1197592973134822608963409)
        ·
          refine ⟨898194729851116956722557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197592973134822608963409 898194729851116956722557)
          ·
            refine ⟨336823023694168858770959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 898194729851116956722557 336823023694168858770959)
            ·
              refine ⟨505234535541253288156439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336823023694168858770959 505234535541253288156439)
              ·
                refine ⟨757851803311879932234659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505234535541253288156439 757851803311879932234659)
                ·
                  refine ⟨1136777704967819898351989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757851803311879932234659 1136777704967819898351989)
                  ·
                    refine ⟨106572909840733115470499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1136777704967819898351989 106572909840733115470499)
                    ·
                      rfl

theorem cell22_311325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_311325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311325 prefixEnd_311325 := by exact prefixLift 311325
  have htrace : WordTrace (prefixWord ++ tailWord_311325) baseStart_311325 baseEnd_311325 := by
    simpa [prefixWord, tailWord_311325, baseEnd_311325] using wordTrace_append hprefix tailTrace_311325
  have hstable : (prefixWord ++ tailWord_311325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311325).length < 2 ^ (prefixWord ++ tailWord_311325).sum := by decide
  have hdescent : baseEnd_311325 < baseStart_311325 := by decide
  rcases family_descends (prefixWord ++ tailWord_311325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311338 : List Nat := [3, 1, 4, 1, 2, 2, 1, 8]
def baseStart_311338 : Nat := 118140960795 + 311338 * 2 ^ 59
def prefixEnd_311338 : Nat := 4983230072969 + 3 ^ 40 * 311338 * 2
def baseEnd_311338 : Nat := 11841928889600601655051

theorem tailTrace_311338 : CollatzResearch.WordTrace tailWord_311338 prefixEnd_311338 11841928889600601655051 := by
  unfold tailWord_311338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838857436520768285561667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7570286497388715428164445 2838857436520768285561667)
  ·
    refine ⟨4258286154781152428342501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2838857436520768285561667 4258286154781152428342501)
    ·
      refine ⟨798428654021466080314219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4258286154781152428342501 798428654021466080314219)
      ·
        refine ⟨1197642981032199120471329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798428654021466080314219 1197642981032199120471329)
        ·
          refine ⟨898232235774149340353497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197642981032199120471329 898232235774149340353497)
          ·
            refine ⟨673674176830612005265123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898232235774149340353497 673674176830612005265123)
            ·
              refine ⟨1010511265245918007897685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673674176830612005265123 1010511265245918007897685)
              ·
                refine ⟨11841928889600601655051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1010511265245918007897685 11841928889600601655051)
                ·
                  rfl

theorem cell22_311338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_311338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311338 prefixEnd_311338 := by exact prefixLift 311338
  have htrace : WordTrace (prefixWord ++ tailWord_311338) baseStart_311338 baseEnd_311338 := by
    simpa [prefixWord, tailWord_311338, baseEnd_311338] using wordTrace_append hprefix tailTrace_311338
  have hstable : (prefixWord ++ tailWord_311338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311338).length < 2 ^ (prefixWord ++ tailWord_311338).sum := by decide
  have hdescent : baseEnd_311338 < baseStart_311338 := by decide
  rcases family_descends (prefixWord ++ tailWord_311338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311428 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 6]
def baseStart_311428 : Nat := 118140960795 + 311428 * 2 ^ 59
def prefixEnd_311428 : Nat := 4983230072969 + 3 ^ 40 * 311428 * 2
def baseEnd_311428 : Nat := 35536056281891726715061

theorem tailTrace_311428 : CollatzResearch.WordTrace tailWord_311428 prefixEnd_311428 35536056281891726715061 := by
  unfold tailWord_311428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5679356157878509256511469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7572474877171345675348625 5679356157878509256511469)
  ·
    refine ⟨2129758559204440971191801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5679356157878509256511469 2129758559204440971191801)
    ·
      refine ⟨1597318919403330728393851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2129758559204440971191801 1597318919403330728393851)
      ·
        refine ⟨2395978379104996092590777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597318919403330728393851 2395978379104996092590777)
        ·
          refine ⟨1796983784328747069443083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2395978379104996092590777 1796983784328747069443083)
          ·
            refine ⟨2695475676493120604164625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796983784328747069443083 2695475676493120604164625)
            ·
              refine ⟨2021606757369840453123469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2695475676493120604164625 2021606757369840453123469)
              ·
                refine ⟨758102534013690169921301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2021606757369840453123469 758102534013690169921301)
                ·
                  refine ⟨35536056281891726715061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 758102534013690169921301 35536056281891726715061)
                  ·
                    rfl

theorem cell22_311428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_311428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311428 prefixEnd_311428 := by exact prefixLift 311428
  have htrace : WordTrace (prefixWord ++ tailWord_311428) baseStart_311428 baseEnd_311428 := by
    simpa [prefixWord, tailWord_311428, baseEnd_311428] using wordTrace_append hprefix tailTrace_311428
  have hstable : (prefixWord ++ tailWord_311428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311428).length < 2 ^ (prefixWord ++ tailWord_311428).sum := by decide
  have hdescent : baseEnd_311428 < baseStart_311428 := by decide
  rcases family_descends (prefixWord ++ tailWord_311428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311443 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 6, 3]
def baseStart_311443 : Nat := 118140960795 + 311443 * 2 ^ 59
def prefixEnd_311443 : Nat := 4983230072969 + 3 ^ 40 * 311443 * 2
def baseEnd_311443 : Nat := 106613303652220141020137

theorem tailTrace_311443 : CollatzResearch.WordTrace tailWord_311443 prefixEnd_311443 106613303652220141020137 := by
  unfold tailWord_311443
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359259410702676074818983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7572839607135117383212655 11359259410702676074818983)
  ·
    refine ⟨17038889116054014112228475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11359259410702676074818983 17038889116054014112228475)
    ·
      refine ⟨25558333674081021168342713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17038889116054014112228475 25558333674081021168342713)
      ·
        refine ⟨19168750255560765876257035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25558333674081021168342713 19168750255560765876257035)
        ·
          refine ⟨28753125383341148814385553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19168750255560765876257035 28753125383341148814385553)
          ·
            refine ⟨21564844037505861610789165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28753125383341148814385553 21564844037505861610789165)
            ·
              refine ⟨8086816514064698104045937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21564844037505861610789165 8086816514064698104045937)
              ·
                refine ⟨6065112385548523578034453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8086816514064698104045937 6065112385548523578034453)
                ·
                  refine ⟨284302143072587042720365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6065112385548523578034453 284302143072587042720365)
                  ·
                    refine ⟨106613303652220141020137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284302143072587042720365 106613303652220141020137)
                    ·
                      rfl

theorem cell22_311443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 3].length) (baseStart_311443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311443 prefixEnd_311443 := by exact prefixLift 311443
  have htrace : WordTrace (prefixWord ++ tailWord_311443) baseStart_311443 baseEnd_311443 := by
    simpa [prefixWord, tailWord_311443, baseEnd_311443] using wordTrace_append hprefix tailTrace_311443
  have hstable : (prefixWord ++ tailWord_311443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311443).length < 2 ^ (prefixWord ++ tailWord_311443).sum := by decide
  have hdescent : baseEnd_311443 < baseStart_311443 := by decide
  rcases family_descends (prefixWord ++ tailWord_311443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311505 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 3, 3]
def baseStart_311505 : Nat := 118140960795 + 311505 * 2 ^ 59
def prefixEnd_311505 : Nat := 4983230072969 + 3 ^ 40 * 311505 * 2
def baseEnd_311505 : Nat := 106634527519272645969947

theorem tailTrace_311505 : CollatzResearch.WordTrace tailWord_311505 prefixEnd_311505 106634527519272645969947 := by
  unfold tailWord_311505
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361520736478060663575969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7574347157652040442383979 11361520736478060663575969)
  ·
    refine ⟨8521140552358545497681977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11361520736478060663575969 8521140552358545497681977)
    ·
      refine ⟨6390855414268909123261483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8521140552358545497681977 6390855414268909123261483)
      ·
        refine ⟨9586283121403363684892225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390855414268909123261483 9586283121403363684892225)
        ·
          refine ⟨7189712341052522763669169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9586283121403363684892225 7189712341052522763669169)
          ·
            refine ⟨5392284255789392072751877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7189712341052522763669169 5392284255789392072751877)
            ·
              refine ⟨1011053297960511013640977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5392284255789392072751877 1011053297960511013640977)
              ·
                refine ⟨758289973470383260230733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011053297960511013640977 758289973470383260230733)
                ·
                  refine ⟨284358740051393722586525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758289973470383260230733 284358740051393722586525)
                  ·
                    refine ⟨106634527519272645969947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284358740051393722586525 106634527519272645969947)
                    ·
                      rfl

theorem cell22_311505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_311505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311505 prefixEnd_311505 := by exact prefixLift 311505
  have htrace : WordTrace (prefixWord ++ tailWord_311505) baseStart_311505 baseEnd_311505 := by
    simpa [prefixWord, tailWord_311505, baseEnd_311505] using wordTrace_append hprefix tailTrace_311505
  have hstable : (prefixWord ++ tailWord_311505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311505).length < 2 ^ (prefixWord ++ tailWord_311505).sum := by decide
  have hdescent : baseEnd_311505 < baseStart_311505 := by decide
  rcases family_descends (prefixWord ++ tailWord_311505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311539 : List Nat := [1, 1, 1, 2, 2, 4, 5, 2, 1, 3]
def baseStart_311539 : Nat := 118140960795 + 311539 * 2 ^ 59
def prefixEnd_311539 : Nat := 4983230072969 + 3 ^ 40 * 311539 * 2
def baseEnd_311539 : Nat := 106646166414107890619843

theorem tailTrace_311539 : CollatzResearch.WordTrace tailWord_311539 prefixEnd_311539 106646166414107890619843 := by
  unfold tailWord_311539
  simp only [CollatzResearch.WordTrace]
  refine ⟨11362760818354884470313671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7575173878903256313542447 11362760818354884470313671)
  ·
    refine ⟨17044141227532326705470507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11362760818354884470313671 17044141227532326705470507)
    ·
      refine ⟨25566211841298490058205761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17044141227532326705470507 25566211841298490058205761)
      ·
        refine ⟨19174658880973867543654321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25566211841298490058205761 19174658880973867543654321)
        ·
          refine ⟨14380994160730400657740741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19174658880973867543654321 14380994160730400657740741)
          ·
            refine ⟨2696436405136950123326389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14380994160730400657740741 2696436405136950123326389)
            ·
              refine ⟨252790912981589074061849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2696436405136950123326389 252790912981589074061849)
              ·
                refine ⟨189593184736191805546387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252790912981589074061849 189593184736191805546387)
                ·
                  refine ⟨284389777104287708319581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189593184736191805546387 284389777104287708319581)
                  ·
                    refine ⟨106646166414107890619843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284389777104287708319581 106646166414107890619843)
                    ·
                      rfl

theorem cell22_311539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 3].length) (baseStart_311539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311539 prefixEnd_311539 := by exact prefixLift 311539
  have htrace : WordTrace (prefixWord ++ tailWord_311539) baseStart_311539 baseEnd_311539 := by
    simpa [prefixWord, tailWord_311539, baseEnd_311539] using wordTrace_append hprefix tailTrace_311539
  have hstable : (prefixWord ++ tailWord_311539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311539).length < 2 ^ (prefixWord ++ tailWord_311539).sum := by decide
  have hdescent : baseEnd_311539 < baseStart_311539 := by decide
  rcases family_descends (prefixWord ++ tailWord_311539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311550 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_311550 : Nat := 118140960795 + 311550 * 2 ^ 59
def prefixEnd_311550 : Nat := 4983230072969 + 3 ^ 40 * 311550 * 2
def baseEnd_311550 : Nat := 106649931938907528594809

theorem tailTrace_311550 : CollatzResearch.WordTrace tailWord_311550 prefixEnd_311550 106649931938907528594809 := by
  unfold tailWord_311550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420395252664379168620513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7575441347543355565976069 1420395252664379168620513)
  ·
    refine ⟨1065296439498284376465385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1420395252664379168620513 1065296439498284376465385)
    ·
      refine ⟨798972329623713282349039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1065296439498284376465385 798972329623713282349039)
      ·
        refine ⟨1198458494435569923523559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798972329623713282349039 1198458494435569923523559)
        ·
          refine ⟨1797687741653354885285339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198458494435569923523559 1797687741653354885285339)
          ·
            refine ⟨2696531612480032327928009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797687741653354885285339 2696531612480032327928009)
            ·
              refine ⟨2022398709360024245946007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696531612480032327928009 2022398709360024245946007)
              ·
                refine ⟨3033598064040036368919011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022398709360024245946007 3033598064040036368919011)
                ·
                  refine ⟨4550397096060054553378517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3033598064040036368919011 4550397096060054553378517)
                  ·
                    refine ⟨106649931938907528594809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4550397096060054553378517 106649931938907528594809)
                    ·
                      rfl

theorem cell22_311550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_311550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311550 prefixEnd_311550 := by exact prefixLift 311550
  have htrace : WordTrace (prefixWord ++ tailWord_311550) baseStart_311550 baseEnd_311550 := by
    simpa [prefixWord, tailWord_311550, baseEnd_311550] using wordTrace_append hprefix tailTrace_311550
  have hstable : (prefixWord ++ tailWord_311550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311550).length < 2 ^ (prefixWord ++ tailWord_311550).sum := by decide
  have hdescent : baseEnd_311550 < baseStart_311550 := by decide
  rcases family_descends (prefixWord ++ tailWord_311550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311563 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 8]
def baseStart_311563 : Nat := 118140960795 + 311563 * 2 ^ 59
def prefixEnd_311563 : Nat := 4983230072969 + 3 ^ 40 * 311563 * 2
def baseEnd_311563 : Nat := 35551460701526609339923

theorem tailTrace_311563 : CollatzResearch.WordTrace tailWord_311563 prefixEnd_311563 35551460701526609339923 := by
  unfold tailWord_311563
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363636170267936569187343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7575757446845291046124895 11363636170267936569187343)
  ·
    refine ⟨17045454255401904853781015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11363636170267936569187343 17045454255401904853781015)
    ·
      refine ⟨25568181383102857280671523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17045454255401904853781015 25568181383102857280671523)
      ·
        refine ⟨38352272074654285921007285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25568181383102857280671523 38352272074654285921007285)
        ·
          refine ⟨3595525506998839305094433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38352272074654285921007285 3595525506998839305094433)
          ·
            refine ⟨2696644130249129478820825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3595525506998839305094433 2696644130249129478820825)
            ·
              refine ⟨2022483097686847109115619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696644130249129478820825 2022483097686847109115619)
              ·
                refine ⟨3033724646530270663673429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2022483097686847109115619 3033724646530270663673429)
                ·
                  refine ⟨35551460701526609339923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3033724646530270663673429 35551460701526609339923)
                  ·
                    rfl

theorem cell22_311563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 8].length) (baseStart_311563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311563 prefixEnd_311563 := by exact prefixLift 311563
  have htrace : WordTrace (prefixWord ++ tailWord_311563) baseStart_311563 baseEnd_311563 := by
    simpa [prefixWord, tailWord_311563, baseEnd_311563] using wordTrace_append hprefix tailTrace_311563
  have hstable : (prefixWord ++ tailWord_311563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311563).length < 2 ^ (prefixWord ++ tailWord_311563).sum := by decide
  have hdescent : baseEnd_311563 < baseStart_311563 := by decide
  rcases family_descends (prefixWord ++ tailWord_311563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311612 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_311612 : Nat := 118140960795 + 311612 * 2 ^ 59
def prefixEnd_311612 : Nat := 4983230072969 + 3 ^ 40 * 311612 * 2
def baseEnd_311612 : Nat := 106671155805960033544619

theorem tailTrace_311612 : CollatzResearch.WordTrace tailWord_311612 prefixEnd_311612 106671155805960033544619 := by
  unfold tailWord_311612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682711673545208968860545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7576948898060278625147393 5682711673545208968860545)
  ·
    refine ⟨4262033755158906726645409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5682711673545208968860545 4262033755158906726645409)
    ·
      refine ⟨3196525316369180044984057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4262033755158906726645409 3196525316369180044984057)
      ·
        refine ⟨2397393987276885033738043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3196525316369180044984057 2397393987276885033738043)
        ·
          refine ⟨3596090980915327550607065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397393987276885033738043 3596090980915327550607065)
          ·
            refine ⟨2697068235686495662955299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3596090980915327550607065 2697068235686495662955299)
            ·
              refine ⟨4045602353529743494432949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697068235686495662955299 4045602353529743494432949)
              ·
                refine ⟨379275220643413452603089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4045602353529743494432949 379275220643413452603089)
                ·
                  refine ⟨284456415482560089452317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379275220643413452603089 284456415482560089452317)
                  ·
                    refine ⟨106671155805960033544619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284456415482560089452317 106671155805960033544619)
                    ·
                      rfl

theorem cell22_311612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_311612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311612 prefixEnd_311612 := by exact prefixLift 311612
  have htrace : WordTrace (prefixWord ++ tailWord_311612) baseStart_311612 baseEnd_311612 := by
    simpa [prefixWord, tailWord_311612, baseEnd_311612] using wordTrace_append hprefix tailTrace_311612
  have hstable : (prefixWord ++ tailWord_311612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311612).length < 2 ^ (prefixWord ++ tailWord_311612).sum := by decide
  have hdescent : baseEnd_311612 < baseStart_311612 := by decide
  rcases family_descends (prefixWord ++ tailWord_311612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311657 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 3, 3]
def baseStart_311657 : Nat := 118140960795 + 311657 * 2 ^ 59
def prefixEnd_311657 : Nat := 4983230072969 + 3 ^ 40 * 311657 * 2
def baseEnd_311657 : Nat := 106686560225594916169481

theorem tailTrace_311657 : CollatzResearch.WordTrace tailWord_311657 prefixEnd_311657 106686560225594916169481 := by
  unfold tailWord_311657
  simp only [CollatzResearch.WordTrace]
  refine ⟨11367064631927390623109225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7578043087951593748739483 11367064631927390623109225)
  ·
    refine ⟨8525298473945542967331919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11367064631927390623109225 8525298473945542967331919)
    ·
      refine ⟨12787947710918314450997879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8525298473945542967331919 12787947710918314450997879)
      ·
        refine ⟨19181921566377471676496819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12787947710918314450997879 19181921566377471676496819)
        ·
          refine ⟨28772882349566207514745229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19181921566377471676496819 28772882349566207514745229)
          ·
            refine ⟨10789830881087327818029461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28772882349566207514745229 10789830881087327818029461)
            ·
              refine ⟨505773322550968491470131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10789830881087327818029461 505773322550968491470131)
              ·
                refine ⟨758659983826452737205197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505773322550968491470131 758659983826452737205197)
                ·
                  refine ⟨284497493934919776451949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758659983826452737205197 284497493934919776451949)
                  ·
                    refine ⟨106686560225594916169481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284497493934919776451949 106686560225594916169481)
                    ·
                      rfl

theorem cell22_311657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_311657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311657 prefixEnd_311657 := by exact prefixLift 311657
  have htrace : WordTrace (prefixWord ++ tailWord_311657) baseStart_311657 baseEnd_311657 := by
    simpa [prefixWord, tailWord_311657, baseEnd_311657] using wordTrace_append hprefix tailTrace_311657
  have hstable : (prefixWord ++ tailWord_311657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311657).length < 2 ^ (prefixWord ++ tailWord_311657).sum := by decide
  have hdescent : baseEnd_311657 < baseStart_311657 := by decide
  rcases family_descends (prefixWord ++ tailWord_311657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311691 : List Nat := [1, 1, 1, 1, 4, 6, 1, 3, 1, 3]
def baseStart_311691 : Nat := 118140960795 + 311691 * 2 ^ 59
def prefixEnd_311691 : Nat := 4983230072969 + 3 ^ 40 * 311691 * 2
def baseEnd_311691 : Nat := 106698199120430160819377

theorem tailTrace_311691 : CollatzResearch.WordTrace tailWord_311691 prefixEnd_311691 106698199120430160819377 := by
  unfold tailWord_311691
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368304713804214429846927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7578869809202809619897951 11368304713804214429846927)
  ·
    refine ⟨17052457070706321644770391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11368304713804214429846927 17052457070706321644770391)
    ·
      refine ⟨25578685606059482467155587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17052457070706321644770391 25578685606059482467155587)
      ·
        refine ⟨38368028409089223700733381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25578685606059482467155587 38368028409089223700733381)
        ·
          refine ⟨7194005326704229443887509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38368028409089223700733381 7194005326704229443887509)
          ·
            refine ⟨337218999689260755182227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7194005326704229443887509 337218999689260755182227)
            ·
              refine ⟨505828499533891132773341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337218999689260755182227 505828499533891132773341)
              ·
                refine ⟨189685687325209174790003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 505828499533891132773341 189685687325209174790003)
                ·
                  refine ⟨284528530987813762185005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189685687325209174790003 284528530987813762185005)
                  ·
                    refine ⟨106698199120430160819377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284528530987813762185005 106698199120430160819377)
                    ·
                      rfl

theorem cell22_311691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 3].length) (baseStart_311691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311691 prefixEnd_311691 := by exact prefixLift 311691
  have htrace : WordTrace (prefixWord ++ tailWord_311691) baseStart_311691 baseEnd_311691 := by
    simpa [prefixWord, tailWord_311691, baseEnd_311691] using wordTrace_append hprefix tailTrace_311691
  have hstable : (prefixWord ++ tailWord_311691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311691).length < 2 ^ (prefixWord ++ tailWord_311691).sum := by decide
  have hdescent : baseEnd_311691 < baseStart_311691 := by decide
  rcases family_descends (prefixWord ++ tailWord_311691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311766 : List Nat := [5, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_311766 : Nat := 118140960795 + 311766 * 2 ^ 59
def prefixEnd_311766 : Nat := 4983230072969 + 3 ^ 40 * 311766 * 2
def baseEnd_311766 : Nat := 35574624384384988398049

theorem tailTrace_311766 : CollatzResearch.WordTrace tailWord_311766 prefixEnd_311766 35574624384384988398049 := by
  unfold tailWord_311766
  simp only [CollatzResearch.WordTrace]
  refine ⟨710690011783281389926697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7580693459021668159218101 710690011783281389926697)
  ·
    refine ⟨533017508837461042445023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 710690011783281389926697 533017508837461042445023)
    ·
      refine ⟨799526263256191563667535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533017508837461042445023 799526263256191563667535)
      ·
        refine ⟨1199289394884287345501303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799526263256191563667535 1199289394884287345501303)
        ·
          refine ⟨1798934092326431018251955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199289394884287345501303 1798934092326431018251955)
          ·
            refine ⟨2698401138489646527377933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798934092326431018251955 2698401138489646527377933)
            ·
              refine ⟨1011900426933617447766725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2698401138489646527377933 1011900426933617447766725)
              ·
                refine ⟨189731330050053271456261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1011900426933617447766725 189731330050053271456261)
                ·
                  refine ⟨35574624384384988398049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189731330050053271456261 35574624384384988398049)
                  ·
                    rfl

theorem cell22_311766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_311766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311766 prefixEnd_311766 := by exact prefixLift 311766
  have htrace : WordTrace (prefixWord ++ tailWord_311766) baseStart_311766 baseEnd_311766 := by
    simpa [prefixWord, tailWord_311766, baseEnd_311766] using wordTrace_append hprefix tailTrace_311766
  have hstable : (prefixWord ++ tailWord_311766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311766).length < 2 ^ (prefixWord ++ tailWord_311766).sum := by decide
  have hdescent : baseEnd_311766 < baseStart_311766 := by decide
  rcases family_descends (prefixWord ++ tailWord_311766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311852 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_311852 : Nat := 118140960795 + 311852 * 2 ^ 59
def prefixEnd_311852 : Nat := 4983230072969 + 3 ^ 40 * 311852 * 2
def baseEnd_311852 : Nat := 106753312710679407543883

theorem tailTrace_311852 : CollatzResearch.WordTrace tailWord_311852 prefixEnd_311852 106753312710679407543883 := by
  unfold tailWord_311852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687088433110469463228905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7582784577480625950971873 5687088433110469463228905)
  ·
    refine ⟨4265316324832852097421679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5687088433110469463228905 4265316324832852097421679)
    ·
      refine ⟨6397974487249278146132519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4265316324832852097421679 6397974487249278146132519)
      ·
        refine ⟨9596961730873917219198779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6397974487249278146132519 9596961730873917219198779)
        ·
          refine ⟨14395442596310875828798169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9596961730873917219198779 14395442596310875828798169)
          ·
            refine ⟨10796581947233156871598627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14395442596310875828798169 10796581947233156871598627)
            ·
              refine ⟨16194872920849735307397941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10796581947233156871598627 16194872920849735307397941)
              ·
                refine ⟨1518269336329662685068557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16194872920849735307397941 1518269336329662685068557)
                ·
                  refine ⟨569351001123623506900709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1518269336329662685068557 569351001123623506900709)
                  ·
                    refine ⟨106753312710679407543883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 569351001123623506900709 106753312710679407543883)
                    ·
                      rfl

theorem cell22_311852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_311852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311852 prefixEnd_311852 := by exact prefixLift 311852
  have htrace : WordTrace (prefixWord ++ tailWord_311852) baseStart_311852 baseEnd_311852 := by
    simpa [prefixWord, tailWord_311852, baseEnd_311852] using wordTrace_append hprefix tailTrace_311852
  have hstable : (prefixWord ++ tailWord_311852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311852).length < 2 ^ (prefixWord ++ tailWord_311852).sum := by decide
  have hdescent : baseEnd_311852 < baseStart_311852 := by decide
  rcases family_descends (prefixWord ++ tailWord_311852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311933 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_311933 : Nat := 118140960795 + 311933 * 2 ^ 59
def prefixEnd_311933 : Nat := 4983230072969 + 3 ^ 40 * 311933 * 2
def baseEnd_311933 : Nat := 106781040666022196268635

theorem tailTrace_311933 : CollatzResearch.WordTrace tailWord_311933 prefixEnd_311933 106781040666022196268635 := by
  unfold tailWord_311933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377131178927489760156453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7584754119284993173437635 11377131178927489760156453)
  ·
    refine ⟨2133212096048904330029335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11377131178927489760156453 2133212096048904330029335)
    ·
      refine ⟨3199818144073356495044003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2133212096048904330029335 3199818144073356495044003)
      ·
        refine ⟨4799727216110034742566005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199818144073356495044003 4799727216110034742566005)
        ·
          refine ⟨449974426510315757115563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4799727216110034742566005 449974426510315757115563)
          ·
            refine ⟨674961639765473635673345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449974426510315757115563 674961639765473635673345)
            ·
              refine ⟨506221229824105226755009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674961639765473635673345 506221229824105226755009)
              ·
                refine ⟨379665922368078920066257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506221229824105226755009 379665922368078920066257)
                ·
                  refine ⟨284749441776059190049693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379665922368078920066257 284749441776059190049693)
                  ·
                    refine ⟨106781040666022196268635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284749441776059190049693 106781040666022196268635)
                    ·
                      rfl

theorem cell22_311933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_311933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311933 prefixEnd_311933 := by exact prefixLift 311933
  have htrace : WordTrace (prefixWord ++ tailWord_311933) baseStart_311933 baseEnd_311933 := by
    simpa [prefixWord, tailWord_311933, baseEnd_311933] using wordTrace_append hprefix tailTrace_311933
  have hstable : (prefixWord ++ tailWord_311933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311933).length < 2 ^ (prefixWord ++ tailWord_311933).sum := by decide
  have hdescent : baseEnd_311933 < baseStart_311933 := by decide
  rcases family_descends (prefixWord ++ tailWord_311933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311946 : List Nat := [3, 1, 2, 3, 3, 2, 1, 7]
def baseStart_311946 : Nat := 118140960795 + 311946 * 2 ^ 59
def prefixEnd_311946 : Nat := 4983230072969 + 3 ^ 40 * 311946 * 2
def baseEnd_311946 : Nat := 11865054536854943965955

theorem tailTrace_311946 : CollatzResearch.WordTrace tailWord_311946 prefixEnd_311946 11865054536854943965955 := by
  unfold tailWord_311946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2844401331970098245094923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7585070218586928653586461 2844401331970098245094923)
  ·
    refine ⟨4266601997955147367642385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2844401331970098245094923 4266601997955147367642385)
    ·
      refine ⟨3199951498466360525731789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4266601997955147367642385 3199951498466360525731789)
      ·
        refine ⟨1199981811924885197149421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3199951498466360525731789 1199981811924885197149421)
        ·
          refine ⟨449993179471831948931033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1199981811924885197149421 449993179471831948931033)
          ·
            refine ⟨337494884603873961698275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449993179471831948931033 337494884603873961698275)
            ·
              refine ⟨506242326905810942547413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337494884603873961698275 506242326905810942547413)
              ·
                refine ⟨11865054536854943965955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 506242326905810942547413 11865054536854943965955)
                ·
                  rfl

theorem cell22_311946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_311946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311946 prefixEnd_311946 := by exact prefixLift 311946
  have htrace : WordTrace (prefixWord ++ tailWord_311946) baseStart_311946 baseEnd_311946 := by
    simpa [prefixWord, tailWord_311946, baseEnd_311946] using wordTrace_append hprefix tailTrace_311946
  have hstable : (prefixWord ++ tailWord_311946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311946).length < 2 ^ (prefixWord ++ tailWord_311946).sum := by decide
  have hdescent : baseEnd_311946 < baseStart_311946 := by decide
  rcases family_descends (prefixWord ++ tailWord_311946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311957 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 11]
def baseStart_311957 : Nat := 118140960795 + 311957 * 2 ^ 59
def prefixEnd_311957 : Nat := 4983230072969 + 3 ^ 40 * 311957 * 2
def baseEnd_311957 : Nat := 35596418785498044556187

theorem tailTrace_311957 : CollatzResearch.WordTrace tailWord_311957 prefixEnd_311957 35596418785498044556187 := by
  unfold tailWord_311957
  simp only [CollatzResearch.WordTrace]
  refine ⟨11378006530840541859030125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7585337687227027906020083 11378006530840541859030125)
  ·
    refine ⟨4266752449065203197136297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11378006530840541859030125 4266752449065203197136297)
    ·
      refine ⟨3200064336798902397852223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4266752449065203197136297 3200064336798902397852223)
      ·
        refine ⟨4800096505198353596778335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200064336798902397852223 4800096505198353596778335)
        ·
          refine ⟨7200144757797530395167503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800096505198353596778335 7200144757797530395167503)
          ·
            refine ⟨10800217136696295592751255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7200144757797530395167503 10800217136696295592751255)
            ·
              refine ⟨16200325705044443389126883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10800217136696295592751255 16200325705044443389126883)
              ·
                refine ⟨24300488557566665083690325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16200325705044443389126883 24300488557566665083690325)
                ·
                  refine ⟨35596418785498044556187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 24300488557566665083690325 35596418785498044556187)
                  ·
                    rfl

theorem cell22_311957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_311957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_311957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_311957 prefixEnd_311957 := by exact prefixLift 311957
  have htrace : WordTrace (prefixWord ++ tailWord_311957) baseStart_311957 baseEnd_311957 := by
    simpa [prefixWord, tailWord_311957, baseEnd_311957] using wordTrace_append hprefix tailTrace_311957
  have hstable : (prefixWord ++ tailWord_311957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311957).length < 2 ^ (prefixWord ++ tailWord_311957).sum := by decide
  have hdescent : baseEnd_311957 < baseStart_311957 := by decide
  rcases family_descends (prefixWord ++ tailWord_311957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312051 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 2, 3]
def baseStart_312051 : Nat := 118140960795 + 312051 * 2 ^ 59
def prefixEnd_312051 : Nat := 4983230072969 + 3 ^ 40 * 312051 * 2
def baseEnd_312051 : Nat := 106821434477509221818273

theorem tailTrace_312051 : CollatzResearch.WordTrace tailWord_312051 prefixEnd_312051 106821434477509221818273 := by
  unfold tailWord_312051
  simp only [CollatzResearch.WordTrace]
  refine ⟨11381434992499995912952007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7587623328333330608634671 11381434992499995912952007)
  ·
    refine ⟨17072152488749993869428011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11381434992499995912952007 17072152488749993869428011)
    ·
      refine ⟨25608228733124990804142017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17072152488749993869428011 25608228733124990804142017)
      ·
        refine ⟨19206171549843743103106513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25608228733124990804142017 19206171549843743103106513)
        ·
          refine ⟨14404628662382807327329885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19206171549843743103106513 14404628662382807327329885)
          ·
            refine ⟨5401735748393552747748707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14404628662382807327329885 5401735748393552747748707)
            ·
              refine ⟨8102603622590329121623061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5401735748393552747748707 8102603622590329121623061)
              ·
                refine ⟨379809544808921677576081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8102603622590329121623061 379809544808921677576081)
                ·
                  refine ⟨284857158606691258182061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379809544808921677576081 284857158606691258182061)
                  ·
                    refine ⟨106821434477509221818273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284857158606691258182061 106821434477509221818273)
                    ·
                      rfl

theorem cell22_312051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 3].length) (baseStart_312051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312051 prefixEnd_312051 := by exact prefixLift 312051
  have htrace : WordTrace (prefixWord ++ tailWord_312051) baseStart_312051 baseEnd_312051 := by
    simpa [prefixWord, tailWord_312051, baseEnd_312051] using wordTrace_append hprefix tailTrace_312051
  have hstable : (prefixWord ++ tailWord_312051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312051).length < 2 ^ (prefixWord ++ tailWord_312051).sum := by decide
  have hdescent : baseEnd_312051 < baseStart_312051 := by decide
  rcases family_descends (prefixWord ++ tailWord_312051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312068 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_312068 : Nat := 118140960795 + 312068 * 2 ^ 59
def prefixEnd_312068 : Nat := 4983230072969 + 3 ^ 40 * 312068 * 2
def baseEnd_312068 : Nat := 106827253924926844143221

theorem tailTrace_312068 : CollatzResearch.WordTrace tailWord_312068 prefixEnd_312068 106827253924926844143221 := by
  unfold tailWord_312068
  simp only [CollatzResearch.WordTrace]
  refine ⟨5691027516719203908160429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7588036688958938544213905 5691027516719203908160429)
  ·
    refine ⟨2134135318769701465560161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5691027516719203908160429 2134135318769701465560161)
    ·
      refine ⟨1600601489077276099170121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2134135318769701465560161 1600601489077276099170121)
      ·
        refine ⟨1200451116807957074377591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1600601489077276099170121 1200451116807957074377591)
        ·
          refine ⟨1800676675211935611566387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200451116807957074377591 1800676675211935611566387)
          ·
            refine ⟨2701015012817903417349581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800676675211935611566387 2701015012817903417349581)
            ·
              refine ⟨1012880629806713781506093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2701015012817903417349581 1012880629806713781506093)
              ·
                refine ⟨379830236177517668064785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1012880629806713781506093 379830236177517668064785)
                ·
                  refine ⟨284872677133138251048589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379830236177517668064785 284872677133138251048589)
                  ·
                    refine ⟨106827253924926844143221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 284872677133138251048589 106827253924926844143221)
                    ·
                      rfl

theorem cell22_312068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_312068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312068 prefixEnd_312068 := by exact prefixLift 312068
  have htrace : WordTrace (prefixWord ++ tailWord_312068) baseStart_312068 baseEnd_312068 := by
    simpa [prefixWord, tailWord_312068, baseEnd_312068] using wordTrace_append hprefix tailTrace_312068
  have hstable : (prefixWord ++ tailWord_312068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312068).length < 2 ^ (prefixWord ++ tailWord_312068).sum := by decide
  have hdescent : baseEnd_312068 < baseStart_312068 := by decide
  rcases family_descends (prefixWord ++ tailWord_312068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312134 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_312134 : Nat := 118140960795 + 312134 * 2 ^ 59
def prefixEnd_312134 : Nat := 4983230072969 + 3 ^ 40 * 312134 * 2
def baseEnd_312134 : Nat := 106849847073724671993019

theorem tailTrace_312134 : CollatzResearch.WordTrace tailWord_312134 prefixEnd_312134 106849847073724671993019 := by
  unfold tailWord_312134
  simp only [CollatzResearch.WordTrace]
  refine ⟨355764445349978159006983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7589641500799534058815637 355764445349978159006983)
  ·
    refine ⟨533646668024967238510475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 355764445349978159006983 533646668024967238510475)
    ·
      refine ⟨800470002037450857765713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533646668024967238510475 800470002037450857765713)
      ·
        refine ⟨600352501528088143324285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 800470002037450857765713 600352501528088143324285)
        ·
          refine ⟨225132188073033053746607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 600352501528088143324285 225132188073033053746607)
          ·
            refine ⟨337698282109549580619911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225132188073033053746607 337698282109549580619911)
            ·
              refine ⟨506547423164324370929867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337698282109549580619911 506547423164324370929867)
              ·
                refine ⟨759821134746486556394801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506547423164324370929867 759821134746486556394801)
                ·
                  refine ⟨569865851059864917296101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 759821134746486556394801 569865851059864917296101)
                  ·
                    refine ⟨106849847073724671993019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 569865851059864917296101 106849847073724671993019)
                    ·
                      rfl

theorem cell22_312134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_312134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312134 prefixEnd_312134 := by exact prefixLift 312134
  have htrace : WordTrace (prefixWord ++ tailWord_312134) baseStart_312134 baseEnd_312134 := by
    simpa [prefixWord, tailWord_312134, baseEnd_312134] using wordTrace_append hprefix tailTrace_312134
  have hstable : (prefixWord ++ tailWord_312134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312134).length < 2 ^ (prefixWord ++ tailWord_312134).sum := by decide
  have hdescent : baseEnd_312134 < baseStart_312134 := by decide
  rcases family_descends (prefixWord ++ tailWord_312134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312169 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 9]
def baseStart_312169 : Nat := 118140960795 + 312169 * 2 ^ 59
def prefixEnd_312169 : Nat := 4983230072969 + 3 ^ 40 * 312169 * 2
def baseEnd_312169 : Nat := 106861828288996247367911

theorem tailTrace_312169 : CollatzResearch.WordTrace tailWord_312169 prefixEnd_312169 106861828288996247367911 := by
  unfold tailWord_312169
  simp only [CollatzResearch.WordTrace]
  refine ⟨11385738806072502065747561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7590492537381668043831707 11385738806072502065747561)
  ·
    refine ⟨8539304104554376549310671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11385738806072502065747561 8539304104554376549310671)
    ·
      refine ⟨12808956156831564823966007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8539304104554376549310671 12808956156831564823966007)
      ·
        refine ⟨19213434235247347235949011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12808956156831564823966007 19213434235247347235949011)
        ·
          refine ⟨28820151352871020853923517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19213434235247347235949011 28820151352871020853923517)
          ·
            refine ⟨10807556757326632820221319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28820151352871020853923517 10807556757326632820221319)
            ·
              refine ⟨16211335135989949230331979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10807556757326632820221319 16211335135989949230331979)
              ·
                refine ⟨24317002703984923845497969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16211335135989949230331979 24317002703984923845497969)
                ·
                  refine ⟨18237752027988692884123477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24317002703984923845497969 18237752027988692884123477)
                  ·
                    refine ⟨106861828288996247367911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 18237752027988692884123477 106861828288996247367911)
                    ·
                      rfl

theorem cell22_312169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_312169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312169 prefixEnd_312169 := by exact prefixLift 312169
  have htrace : WordTrace (prefixWord ++ tailWord_312169) baseStart_312169 baseEnd_312169 := by
    simpa [prefixWord, tailWord_312169, baseEnd_312169] using wordTrace_append hprefix tailTrace_312169
  have hstable : (prefixWord ++ tailWord_312169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312169).length < 2 ^ (prefixWord ++ tailWord_312169).sum := by decide
  have hdescent : baseEnd_312169 < baseStart_312169 := by decide
  rcases family_descends (prefixWord ++ tailWord_312169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312201 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 1, 6]
def baseStart_312201 : Nat := 118140960795 + 312201 * 2 ^ 59
def prefixEnd_312201 : Nat := 4983230072969 + 3 ^ 40 * 312201 * 2
def baseEnd_312201 : Nat := 106872782542958830567813

theorem tailTrace_312201 : CollatzResearch.WordTrace tailWord_312201 prefixEnd_312201 106872782542958830567813 := by
  unfold tailWord_312201
  simp only [CollatzResearch.WordTrace]
  refine ⟨11386905941956571530912457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7591270627971047687274971 11386905941956571530912457)
  ·
    refine ⟨8540179456467428648184343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11386905941956571530912457 8540179456467428648184343)
    ·
      refine ⟨12810269184701142972276515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8540179456467428648184343 12810269184701142972276515)
      ·
        refine ⟨19215403777051714458414773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12810269184701142972276515 19215403777051714458414773)
        ·
          refine ⟨1801444104098598230476385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19215403777051714458414773 1801444104098598230476385)
          ·
            refine ⟨1351083078073948672857289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801444104098598230476385 1351083078073948672857289)
            ·
              refine ⟨1013312308555461504642967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351083078073948672857289 1013312308555461504642967)
              ·
                refine ⟨1519968462833192256964451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013312308555461504642967 1519968462833192256964451)
                ·
                  refine ⟨2279952694249788385446677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519968462833192256964451 2279952694249788385446677)
                  ·
                    refine ⟨106872782542958830567813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2279952694249788385446677 106872782542958830567813)
                    ·
                      rfl

theorem cell22_312201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 6].length) (baseStart_312201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312201 prefixEnd_312201 := by exact prefixLift 312201
  have htrace : WordTrace (prefixWord ++ tailWord_312201) baseStart_312201 baseEnd_312201 := by
    simpa [prefixWord, tailWord_312201, baseEnd_312201] using wordTrace_append hprefix tailTrace_312201
  have hstable : (prefixWord ++ tailWord_312201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312201).length < 2 ^ (prefixWord ++ tailWord_312201).sum := by decide
  have hdescent : baseEnd_312201 < baseStart_312201 := by decide
  rcases family_descends (prefixWord ++ tailWord_312201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312282 : List Nat := [3, 1, 1, 2, 4, 2, 1, 4, 1, 3]
def baseStart_312282 : Nat := 118140960795 + 312282 * 2 ^ 59
def prefixEnd_312282 : Nat := 4983230072969 + 3 ^ 40 * 312282 * 2
def baseEnd_312282 : Nat := 106900510498301619292565

theorem tailTrace_312282 : CollatzResearch.WordTrace tailWord_312282 prefixEnd_312282 106900510498301619292565 := by
  unfold tailWord_312282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847465063665780591152775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7593240169775414909740733 2847465063665780591152775)
  ·
    refine ⟨4271197595498670886729163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847465063665780591152775 4271197595498670886729163)
    ·
      refine ⟨6406796393248006330093745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4271197595498670886729163 6406796393248006330093745)
      ·
        refine ⟨4805097294936004747570309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6406796393248006330093745 4805097294936004747570309)
        ·
          refine ⟨900955742800500890169433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4805097294936004747570309 900955742800500890169433)
          ·
            refine ⟨675716807100375667627075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 900955742800500890169433 675716807100375667627075)
            ·
              refine ⟨1013575210650563501440613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675716807100375667627075 1013575210650563501440613)
              ·
                refine ⟨190045351996980656520115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1013575210650563501440613 190045351996980656520115)
                ·
                  refine ⟨285068027995470984780173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190045351996980656520115 285068027995470984780173)
                  ·
                    refine ⟨106900510498301619292565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285068027995470984780173 106900510498301619292565)
                    ·
                      rfl

theorem cell22_312282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 3].length) (baseStart_312282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312282 prefixEnd_312282 := by exact prefixLift 312282
  have htrace : WordTrace (prefixWord ++ tailWord_312282) baseStart_312282 baseEnd_312282 := by
    simpa [prefixWord, tailWord_312282, baseEnd_312282] using wordTrace_append hprefix tailTrace_312282
  have hstable : (prefixWord ++ tailWord_312282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312282).length < 2 ^ (prefixWord ++ tailWord_312282).sum := by decide
  have hdescent : baseEnd_312282 < baseStart_312282 := by decide
  rcases family_descends (prefixWord ++ tailWord_312282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312336 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_312336 : Nat := 118140960795 + 312336 * 2 ^ 59
def prefixEnd_312336 : Nat := 4983230072969 + 3 ^ 40 * 312336 * 2
def baseEnd_312336 : Nat := 106918995801863478442399

theorem tailTrace_312336 : CollatzResearch.WordTrace tailWord_312336 prefixEnd_312336 106918995801863478442399 := by
  unfold tailWord_312336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5695914898233744793538431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7594553197644993058051241 5695914898233744793538431)
  ·
    refine ⟨8543872347350617190307647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5695914898233744793538431 8543872347350617190307647)
    ·
      refine ⟨12815808521025925785461471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8543872347350617190307647 12815808521025925785461471)
      ·
        refine ⟨19223712781538888678192207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12815808521025925785461471 19223712781538888678192207)
        ·
          refine ⟨28835569172308333017288311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19223712781538888678192207 28835569172308333017288311)
          ·
            refine ⟨43253353758462499525932467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28835569172308333017288311 43253353758462499525932467)
            ·
              refine ⟨64880030637693749288898701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43253353758462499525932467 64880030637693749288898701)
              ·
                refine ⟨24330011489135155983337013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64880030637693749288898701 24330011489135155983337013)
                ·
                  refine ⟨2280938577106420873437845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24330011489135155983337013 2280938577106420873437845)
                  ·
                    refine ⟨106918995801863478442399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2280938577106420873437845 106918995801863478442399)
                    ·
                      rfl

theorem cell22_312336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_312336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312336 prefixEnd_312336 := by exact prefixLift 312336
  have htrace : WordTrace (prefixWord ++ tailWord_312336) baseStart_312336 baseEnd_312336 := by
    simpa [prefixWord, tailWord_312336, baseEnd_312336] using wordTrace_append hprefix tailTrace_312336
  have hstable : (prefixWord ++ tailWord_312336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312336).length < 2 ^ (prefixWord ++ tailWord_312336).sum := by decide
  have hdescent : baseEnd_312336 < baseStart_312336 := by decide
  rcases family_descends (prefixWord ++ tailWord_312336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312353 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_312353 : Nat := 118140960795 + 312353 * 2 ^ 59
def prefixEnd_312353 : Nat := 4983230072969 + 3 ^ 40 * 312353 * 2
def baseEnd_312353 : Nat := 106924815249281100767347

theorem tailTrace_312353 : CollatzResearch.WordTrace tailWord_312353 prefixEnd_312353 106924815249281100767347 := by
  unfold tailWord_312353
  simp only [CollatzResearch.WordTrace]
  refine ⟨11392449837405901490445713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7594966558270600993630475 11392449837405901490445713)
  ·
    refine ⟨8544337378054426117834285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11392449837405901490445713 8544337378054426117834285)
    ·
      refine ⟨3204126516770409794187857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8544337378054426117834285 3204126516770409794187857)
      ·
        refine ⟨2403094887577807345640893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3204126516770409794187857 2403094887577807345640893)
        ·
          refine ⟨901160582841677754615335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2403094887577807345640893 901160582841677754615335)
          ·
            refine ⟨1351740874262516631923003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901160582841677754615335 1351740874262516631923003)
            ·
              refine ⟨2027611311393774947884505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351740874262516631923003 2027611311393774947884505)
              ·
                refine ⟨1520708483545331210913379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027611311393774947884505 1520708483545331210913379)
                ·
                  refine ⟨2281062725317996816370069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520708483545331210913379 2281062725317996816370069)
                  ·
                    refine ⟨106924815249281100767347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2281062725317996816370069 106924815249281100767347)
                    ·
                      rfl

theorem cell22_312353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_312353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312353 prefixEnd_312353 := by exact prefixLift 312353
  have htrace : WordTrace (prefixWord ++ tailWord_312353) baseStart_312353 baseEnd_312353 := by
    simpa [prefixWord, tailWord_312353, baseEnd_312353] using wordTrace_append hprefix tailTrace_312353
  have hstable : (prefixWord ++ tailWord_312353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312353).length < 2 ^ (prefixWord ++ tailWord_312353).sum := by decide
  have hdescent : baseEnd_312353 < baseStart_312353 := by decide
  rcases family_descends (prefixWord ++ tailWord_312353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312355 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 1, 5]
def baseStart_312355 : Nat := 118140960795 + 312355 * 2 ^ 59
def prefixEnd_312355 : Nat := 4983230072969 + 3 ^ 40 * 312355 * 2
def baseEnd_312355 : Nat := 106925499890153762217341

theorem tailTrace_312355 : CollatzResearch.WordTrace tailWord_312355 prefixEnd_312355 106925499890153762217341 := by
  unfold tailWord_312355
  simp only [CollatzResearch.WordTrace]
  refine ⟨11392522783398655832018519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7595015188932437221345679 11392522783398655832018519)
  ·
    refine ⟨17088784175097983748027779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11392522783398655832018519 17088784175097983748027779)
    ·
      refine ⟨25633176262646975622041669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17088784175097983748027779 25633176262646975622041669)
      ·
        refine ⟨4806220549246307929132813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25633176262646975622041669 4806220549246307929132813)
        ·
          refine ⟨1802332705967365473424805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4806220549246307929132813 1802332705967365473424805)
          ·
            refine ⟨337937382368881026267151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1802332705967365473424805 337937382368881026267151)
            ·
              refine ⟨506906073553321539400727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337937382368881026267151 506906073553321539400727)
              ·
                refine ⟨760359110329982309101091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506906073553321539400727 760359110329982309101091)
                ·
                  refine ⟨1140538665494973463651637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760359110329982309101091 1140538665494973463651637)
                  ·
                    refine ⟨106925499890153762217341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1140538665494973463651637 106925499890153762217341)
                    ·
                      rfl

theorem cell22_312355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 5].length) (baseStart_312355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312355 prefixEnd_312355 := by exact prefixLift 312355
  have htrace : WordTrace (prefixWord ++ tailWord_312355) baseStart_312355 baseEnd_312355 := by
    simpa [prefixWord, tailWord_312355, baseEnd_312355] using wordTrace_append hprefix tailTrace_312355
  have hstable : (prefixWord ++ tailWord_312355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312355).length < 2 ^ (prefixWord ++ tailWord_312355).sum := by decide
  have hdescent : baseEnd_312355 < baseStart_312355 := by decide
  rcases family_descends (prefixWord ++ tailWord_312355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312372 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_312372 : Nat := 118140960795 + 312372 * 2 ^ 59
def prefixEnd_312372 : Nat := 4983230072969 + 3 ^ 40 * 312372 * 2
def baseEnd_312372 : Nat := 106931319337571384542289

theorem tailTrace_312372 : CollatzResearch.WordTrace tailWord_312372 prefixEnd_312372 106931319337571384542289 := by
  unfold tailWord_312372
  simp only [CollatzResearch.WordTrace]
  refine ⟨5696571412168533867693685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7595428549558045156924913 5696571412168533867693685)
  ·
    refine ⟨534053569890800050096283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5696571412168533867693685 534053569890800050096283)
    ·
      refine ⟨801080354836200075144425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534053569890800050096283 801080354836200075144425)
      ·
        refine ⟨600810266127150056358319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801080354836200075144425 600810266127150056358319)
        ·
          refine ⟨901215399190725084537479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600810266127150056358319 901215399190725084537479)
          ·
            refine ⟨1351823098786087626806219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901215399190725084537479 1351823098786087626806219)
            ·
              refine ⟨2027734648179131440209329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351823098786087626806219 2027734648179131440209329)
              ·
                refine ⟨1520800986134348580156997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027734648179131440209329 1520800986134348580156997)
                ·
                  refine ⟨285150184900190358779437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520800986134348580156997 285150184900190358779437)
                  ·
                    refine ⟨106931319337571384542289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285150184900190358779437 106931319337571384542289)
                    ·
                      rfl

theorem cell22_312372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_312372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312372 prefixEnd_312372 := by exact prefixLift 312372
  have htrace : WordTrace (prefixWord ++ tailWord_312372) baseStart_312372 baseEnd_312372 := by
    simpa [prefixWord, tailWord_312372, baseEnd_312372] using wordTrace_append hprefix tailTrace_312372
  have hstable : (prefixWord ++ tailWord_312372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312372).length < 2 ^ (prefixWord ++ tailWord_312372).sum := by decide
  have hdescent : baseEnd_312372 < baseStart_312372 := by decide
  rcases family_descends (prefixWord ++ tailWord_312372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312374 : List Nat := [5, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_312374 : Nat := 118140960795 + 312374 * 2 ^ 59
def prefixEnd_312374 : Nat := 4983230072969 + 3 ^ 40 * 312374 * 2
def baseEnd_312374 : Nat := 35644001326148015330761

theorem tailTrace_312374 : CollatzResearch.WordTrace tailWord_312374 prefixEnd_312374 35644001326148015330761 := by
  unfold tailWord_312374
  simp only [CollatzResearch.WordTrace]
  refine ⟨712075985645613879810011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7595477180219881384640117 712075985645613879810011)
  ·
    refine ⟨1068113978468420819715017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 712075985645613879810011 1068113978468420819715017)
    ·
      refine ⟨801085483851315614786263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1068113978468420819715017 801085483851315614786263)
      ·
        refine ⟨1201628225776973422179395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801085483851315614786263 1201628225776973422179395)
        ·
          refine ⟨1802442338665460133269093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201628225776973422179395 1802442338665460133269093)
          ·
            refine ⟨337957938499773774987955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1802442338665460133269093 337957938499773774987955)
            ·
              refine ⟨506936907749660662481933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337957938499773774987955 506936907749660662481933)
              ·
                refine ⟨190101340406122748430725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 506936907749660662481933 190101340406122748430725)
                ·
                  refine ⟨35644001326148015330761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190101340406122748430725 35644001326148015330761)
                  ·
                    rfl

theorem cell22_312374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_312374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312374 prefixEnd_312374 := by exact prefixLift 312374
  have htrace : WordTrace (prefixWord ++ tailWord_312374) baseStart_312374 baseEnd_312374 := by
    simpa [prefixWord, tailWord_312374, baseEnd_312374] using wordTrace_append hprefix tailTrace_312374
  have hstable : (prefixWord ++ tailWord_312374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312374).length < 2 ^ (prefixWord ++ tailWord_312374).sum := by decide
  have hdescent : baseEnd_312374 < baseStart_312374 := by decide
  rcases family_descends (prefixWord ++ tailWord_312374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312385 : List Nat := [1, 2, 5, 1, 3, 2, 8]
def baseStart_312385 : Nat := 118140960795 + 312385 * 2 ^ 59
def prefixEnd_312385 : Nat := 4983230072969 + 3 ^ 40 * 312385 * 2
def baseEnd_312385 : Nat := 3960584055675691998787

theorem tailTrace_312385 : CollatzResearch.WordTrace tailWord_312385 prefixEnd_312385 3960584055675691998787 := by
  unfold tailWord_312385
  simp only [CollatzResearch.WordTrace]
  refine ⟨11393616973289970955610609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7595744648859980637073739 11393616973289970955610609)
  ·
    refine ⟨8545212729967478216707957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11393616973289970955610609 8545212729967478216707957)
    ·
      refine ⟨801113693434451082816371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8545212729967478216707957 801113693434451082816371)
      ·
        refine ⟨1201670540151676624224557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801113693434451082816371 1201670540151676624224557)
        ·
          refine ⟨450626452556878734084209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1201670540151676624224557 450626452556878734084209)
          ·
            refine ⟨337969839417659050563157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450626452556878734084209 337969839417659050563157)
            ·
              refine ⟨3960584055675691998787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 337969839417659050563157 3960584055675691998787)
              ·
                rfl

theorem cell22_312385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 8].length) (baseStart_312385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312385 prefixEnd_312385 := by exact prefixLift 312385
  have htrace : WordTrace (prefixWord ++ tailWord_312385) baseStart_312385 baseEnd_312385 := by
    simpa [prefixWord, tailWord_312385, baseEnd_312385] using wordTrace_append hprefix tailTrace_312385
  have hstable : (prefixWord ++ tailWord_312385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312385).length < 2 ^ (prefixWord ++ tailWord_312385).sum := by decide
  have hdescent : baseEnd_312385 < baseStart_312385 := by decide
  rcases family_descends (prefixWord ++ tailWord_312385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312398 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_312398 : Nat := 118140960795 + 312398 * 2 ^ 59
def prefixEnd_312398 : Nat := 4983230072969 + 3 ^ 40 * 312398 * 2
def baseEnd_312398 : Nat := 106940219668915983392209

theorem tailTrace_312398 : CollatzResearch.WordTrace tailWord_312398 prefixEnd_312398 106940219668915983392209 := by
  unfold tailWord_312398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424261390280359271979231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7596060748161916117222565 1424261390280359271979231)
  ·
    refine ⟨2136392085420538907968847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424261390280359271979231 2136392085420538907968847)
    ·
      refine ⟨3204588128130808361953271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136392085420538907968847 3204588128130808361953271)
      ·
        refine ⟨4806882192196212542929907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204588128130808361953271 4806882192196212542929907)
        ·
          refine ⟨7210323288294318814394861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806882192196212542929907 7210323288294318814394861)
          ·
            refine ⟨2703871233110369555398073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7210323288294318814394861 2703871233110369555398073)
            ·
              refine ⟨2027903424832777166548555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2703871233110369555398073 2027903424832777166548555)
              ·
                refine ⟨3041855137249165749822833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027903424832777166548555 3041855137249165749822833)
                ·
                  refine ⟨2281391352936874312367125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3041855137249165749822833 2281391352936874312367125)
                  ·
                    refine ⟨106940219668915983392209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2281391352936874312367125 106940219668915983392209)
                    ·
                      rfl

theorem cell22_312398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_312398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312398 prefixEnd_312398 := by exact prefixLift 312398
  have htrace : WordTrace (prefixWord ++ tailWord_312398) baseStart_312398 baseEnd_312398 := by
    simpa [prefixWord, tailWord_312398, baseEnd_312398] using wordTrace_append hprefix tailTrace_312398
  have hstable : (prefixWord ++ tailWord_312398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312398).length < 2 ^ (prefixWord ++ tailWord_312398).sum := by decide
  have hdescent : baseEnd_312398 < baseStart_312398 := by decide
  rcases family_descends (prefixWord ++ tailWord_312398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312406 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_312406 : Nat := 118140960795 + 312406 * 2 ^ 59
def prefixEnd_312406 : Nat := 4983230072969 + 3 ^ 40 * 312406 * 2
def baseEnd_312406 : Nat := 106942958232406629192185

theorem tailTrace_312406 : CollatzResearch.WordTrace tailWord_312406 prefixEnd_312406 106942958232406629192185 := by
  unfold tailWord_312406
  simp only [CollatzResearch.WordTrace]
  refine ⟨712148931638368221382817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7596255270809261028083381 712148931638368221382817)
  ·
    refine ⟨534111698728776166037113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 712148931638368221382817 534111698728776166037113)
    ·
      refine ⟨400583774046582124527835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 534111698728776166037113 400583774046582124527835)
      ·
        refine ⟨600875661069873186791753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400583774046582124527835 600875661069873186791753)
        ·
          refine ⟨450656745802404890093815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600875661069873186791753 450656745802404890093815)
          ·
            refine ⟨675985118703607335140723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450656745802404890093815 675985118703607335140723)
            ·
              refine ⟨1013977678055411002711085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675985118703607335140723 1013977678055411002711085)
              ·
                refine ⟨380241629270779126016657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1013977678055411002711085 380241629270779126016657)
                ·
                  refine ⟨285181221953084344512493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380241629270779126016657 285181221953084344512493)
                  ·
                    refine ⟨106942958232406629192185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285181221953084344512493 106942958232406629192185)
                    ·
                      rfl

theorem cell22_312406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_312406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312406 prefixEnd_312406 := by exact prefixLift 312406
  have htrace : WordTrace (prefixWord ++ tailWord_312406) baseStart_312406 baseEnd_312406 := by
    simpa [prefixWord, tailWord_312406, baseEnd_312406] using wordTrace_append hprefix tailTrace_312406
  have hstable : (prefixWord ++ tailWord_312406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312406).length < 2 ^ (prefixWord ++ tailWord_312406).sum := by decide
  have hdescent : baseEnd_312406 < baseStart_312406 := by decide
  rcases family_descends (prefixWord ++ tailWord_312406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312503 : List Nat := [1, 1, 3, 1, 4, 1, 11]
def baseStart_312503 : Nat := 118140960795 + 312503 * 2 ^ 59
def prefixEnd_312503 : Nat := 4983230072969 + 3 ^ 40 * 312503 * 2
def baseEnd_312503 : Nat := 3962080122767804056181

theorem tailTrace_312503 : CollatzResearch.WordTrace tailWord_312503 prefixEnd_312503 3962080122767804056181 := by
  unfold tailWord_312503
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397920786862477108406163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7598613857908318072270775 11397920786862477108406163)
  ·
    refine ⟨17096881180293715662609245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11397920786862477108406163 17096881180293715662609245)
    ·
      refine ⟨6411330442610143373478467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17096881180293715662609245 6411330442610143373478467)
      ·
        refine ⟨9616995663915215060217701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411330442610143373478467 9616995663915215060217701)
        ·
          refine ⟨1803186686984102823790819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9616995663915215060217701 1803186686984102823790819)
          ·
            refine ⟨2704780030476154235686229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1803186686984102823790819 2704780030476154235686229)
            ·
              refine ⟨3962080122767804056181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2704780030476154235686229 3962080122767804056181)
              ·
                rfl

theorem cell22_312503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 11].length) (baseStart_312503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312503 prefixEnd_312503 := by exact prefixLift 312503
  have htrace : WordTrace (prefixWord ++ tailWord_312503) baseStart_312503 baseEnd_312503 := by
    simpa [prefixWord, tailWord_312503, baseEnd_312503] using wordTrace_append hprefix tailTrace_312503
  have hstable : (prefixWord ++ tailWord_312503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312503).length < 2 ^ (prefixWord ++ tailWord_312503).sum := by decide
  have hdescent : baseEnd_312503 < baseStart_312503 := by decide
  rcases family_descends (prefixWord ++ tailWord_312503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312640 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_312640 : Nat := 118140960795 + 312640 * 2 ^ 59
def prefixEnd_312640 : Nat := 4983230072969 + 3 ^ 40 * 312640 * 2
def baseEnd_312640 : Nat := 107023061214508018841467

theorem tailTrace_312640 : CollatzResearch.WordTrace tailWord_312640 prefixEnd_312640 107023061214508018841467 := by
  unfold tailWord_312640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5701458793683074753071687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7601945058244099670762249 5701458793683074753071687)
  ·
    refine ⟨8552188190524612129607531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5701458793683074753071687 8552188190524612129607531)
    ·
      refine ⟨12828282285786918194411297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8552188190524612129607531 12828282285786918194411297)
      ·
        refine ⟨9621211714340188645808473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12828282285786918194411297 9621211714340188645808473)
        ·
          refine ⟨7215908785755141484356355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9621211714340188645808473 7215908785755141484356355)
          ·
            refine ⟨10823863178632712226534533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215908785755141484356355 10823863178632712226534533)
            ·
              refine ⟨2029474345993633542475225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10823863178632712226534533 2029474345993633542475225)
              ·
                refine ⟨1522105759495225156856419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2029474345993633542475225 1522105759495225156856419)
                ·
                  refine ⟨2283158639242837735284629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522105759495225156856419 2283158639242837735284629)
                  ·
                    refine ⟨107023061214508018841467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2283158639242837735284629 107023061214508018841467)
                    ·
                      rfl

theorem cell22_312640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_312640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312640 prefixEnd_312640 := by exact prefixLift 312640
  have htrace : WordTrace (prefixWord ++ tailWord_312640) baseStart_312640 baseEnd_312640 := by
    simpa [prefixWord, tailWord_312640, baseEnd_312640] using wordTrace_append hprefix tailTrace_312640
  have hstable : (prefixWord ++ tailWord_312640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312640).length < 2 ^ (prefixWord ++ tailWord_312640).sum := by decide
  have hdescent : baseEnd_312640 < baseStart_312640 := by decide
  rcases family_descends (prefixWord ++ tailWord_312640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312644 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 6]
def baseStart_312644 : Nat := 118140960795 + 312644 * 2 ^ 59
def prefixEnd_312644 : Nat := 4983230072969 + 3 ^ 40 * 312644 * 2
def baseEnd_312644 : Nat := 35674810165417780580485

theorem tailTrace_312644 : CollatzResearch.WordTrace tailWord_312644 prefixEnd_312644 35674810165417780580485 := by
  unfold tailWord_312644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5701531739675829094644493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7602042319567772126192657 5701531739675829094644493)
  ·
    refine ⟨2138074402378435910491685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5701531739675829094644493 2138074402378435910491685)
    ·
      refine ⟨400888950445956733217191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2138074402378435910491685 400888950445956733217191)
      ·
        refine ⟨601333425668935099825787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400888950445956733217191 601333425668935099825787)
        ·
          refine ⟨902000138503402649738681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601333425668935099825787 902000138503402649738681)
          ·
            refine ⟨676500103877551987304011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902000138503402649738681 676500103877551987304011)
            ·
              refine ⟨1014750155816327980956017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676500103877551987304011 1014750155816327980956017)
              ·
                refine ⟨761062616862245985717013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014750155816327980956017 761062616862245985717013)
                ·
                  refine ⟨35674810165417780580485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 761062616862245985717013 35674810165417780580485)
                  ·
                    rfl

theorem cell22_312644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_312644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312644 prefixEnd_312644 := by exact prefixLift 312644
  have htrace : WordTrace (prefixWord ++ tailWord_312644) baseStart_312644 baseEnd_312644 := by
    simpa [prefixWord, tailWord_312644, baseEnd_312644] using wordTrace_append hprefix tailTrace_312644
  have hstable : (prefixWord ++ tailWord_312644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312644).length < 2 ^ (prefixWord ++ tailWord_312644).sum := by decide
  have hdescent : baseEnd_312644 < baseStart_312644 := by decide
  rcases family_descends (prefixWord ++ tailWord_312644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312676 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_312676 : Nat := 118140960795 + 312676 * 2 ^ 59
def prefixEnd_312676 : Nat := 4983230072969 + 3 ^ 40 * 312676 * 2
def baseEnd_312676 : Nat := 107035384750215924941357

theorem tailTrace_312676 : CollatzResearch.WordTrace tailWord_312676 prefixEnd_312676 107035384750215924941357 := by
  unfold tailWord_312676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702115307617863827226941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7602820410157151769635921 5702115307617863827226941)
  ·
    refine ⟨2138293240356698935210103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5702115307617863827226941 2138293240356698935210103)
    ·
      refine ⟨3207439860535048402815155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2138293240356698935210103 3207439860535048402815155)
      ·
        refine ⟨4811159790802572604222733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207439860535048402815155 4811159790802572604222733)
        ·
          refine ⟨1804184921550964726583525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4811159790802572604222733 1804184921550964726583525)
          ·
            refine ⟨338284672790805886234411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1804184921550964726583525 338284672790805886234411)
            ·
              refine ⟨507427009186208829351617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338284672790805886234411 507427009186208829351617)
              ·
                refine ⟨380570256889656622013713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507427009186208829351617 380570256889656622013713)
                ·
                  refine ⟨285427692667242466510285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380570256889656622013713 285427692667242466510285)
                  ·
                    refine ⟨107035384750215924941357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285427692667242466510285 107035384750215924941357)
                    ·
                      rfl

theorem cell22_312676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_312676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312676 prefixEnd_312676 := by exact prefixLift 312676
  have htrace : WordTrace (prefixWord ++ tailWord_312676) baseStart_312676 baseEnd_312676 := by
    simpa [prefixWord, tailWord_312676, baseEnd_312676] using wordTrace_append hprefix tailTrace_312676
  have hstable : (prefixWord ++ tailWord_312676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312676).length < 2 ^ (prefixWord ++ tailWord_312676).sum := by decide
  have hdescent : baseEnd_312676 < baseStart_312676 := by decide
  rcases family_descends (prefixWord ++ tailWord_312676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312693 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 2, 3]
def baseStart_312693 : Nat := 118140960795 + 312693 * 2 ^ 59
def prefixEnd_312693 : Nat := 4983230072969 + 3 ^ 40 * 312693 * 2
def baseEnd_312693 : Nat := 107041204197633547266305

theorem tailTrace_312693 : CollatzResearch.WordTrace tailWord_312693 prefixEnd_312693 107041204197633547266305 := by
  unfold tailWord_312693
  simp only [CollatzResearch.WordTrace]
  refine ⟨11404850656174139557822733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7603233770782759705215155 11404850656174139557822733)
  ·
    refine ⟨4276818996065302334183525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11404850656174139557822733 4276818996065302334183525)
    ·
      refine ⟨801903561762244187659411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4276818996065302334183525 801903561762244187659411)
      ·
        refine ⟨1202855342643366281489117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801903561762244187659411 1202855342643366281489117)
        ·
          refine ⟨451070753491262355558419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1202855342643366281489117 451070753491262355558419)
          ·
            refine ⟨676606130236893533337629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451070753491262355558419 676606130236893533337629)
            ·
              refine ⟨253727298838835075001611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676606130236893533337629 253727298838835075001611)
              ·
                refine ⟨380590948258252612502417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253727298838835075001611 380590948258252612502417)
                ·
                  refine ⟨285443211193689459376813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 380590948258252612502417 285443211193689459376813)
                  ·
                    refine ⟨107041204197633547266305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285443211193689459376813 107041204197633547266305)
                    ·
                      rfl

theorem cell22_312693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_312693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312693 prefixEnd_312693 := by exact prefixLift 312693
  have htrace : WordTrace (prefixWord ++ tailWord_312693) baseStart_312693 baseEnd_312693 := by
    simpa [prefixWord, tailWord_312693, baseEnd_312693] using wordTrace_append hprefix tailTrace_312693
  have hstable : (prefixWord ++ tailWord_312693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312693).length < 2 ^ (prefixWord ++ tailWord_312693).sum := by decide
  have hdescent : baseEnd_312693 < baseStart_312693 := by decide
  rcases family_descends (prefixWord ++ tailWord_312693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312706 : List Nat := [3, 4, 2, 1, 1, 1, 4, 6]
def baseStart_312706 : Nat := 118140960795 + 312706 * 2 ^ 59
def prefixEnd_312706 : Nat := 4983230072969 + 3 ^ 40 * 312706 * 2
def baseEnd_312706 : Nat := 11893961595922871854585

theorem tailTrace_312706 : CollatzResearch.WordTrace tailWord_312706 prefixEnd_312706 11893961595922871854585 := by
  unfold tailWord_312706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2851331201281760694511493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7603549870084695185363981 2851331201281760694511493)
  ·
    refine ⟨534624600240330130220905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2851331201281760694511493 534624600240330130220905)
    ·
      refine ⟨400968450180247597665679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 534624600240330130220905 400968450180247597665679)
      ·
        refine ⟨601452675270371396498519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400968450180247597665679 601452675270371396498519)
        ·
          refine ⟨902179012905557094747779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601452675270371396498519 902179012905557094747779)
          ·
            refine ⟨1353268519358335642121669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902179012905557094747779 1353268519358335642121669)
            ·
              refine ⟨253737847379687932897813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1353268519358335642121669 253737847379687932897813)
              ·
                refine ⟨11893961595922871854585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 253737847379687932897813 11893961595922871854585)
                ·
                  rfl

theorem cell22_312706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_312706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312706 prefixEnd_312706 := by exact prefixLift 312706
  have htrace : WordTrace (prefixWord ++ tailWord_312706) baseStart_312706 baseEnd_312706 := by
    simpa [prefixWord, tailWord_312706, baseEnd_312706] using wordTrace_append hprefix tailTrace_312706
  have hstable : (prefixWord ++ tailWord_312706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312706).length < 2 ^ (prefixWord ++ tailWord_312706).sum := by decide
  have hdescent : baseEnd_312706 < baseStart_312706 := by decide
  rcases family_descends (prefixWord ++ tailWord_312706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312824 : List Nat := [2, 1, 2, 1, 1, 6, 3, 6]
def baseStart_312824 : Nat := 118140960795 + 312824 * 2 ^ 59
def prefixEnd_312824 : Nat := 4983230072969 + 3 ^ 40 * 312824 * 2
def baseEnd_312824 : Nat := 11898449797199208026767

theorem tailTrace_312824 : CollatzResearch.WordTrace tailWord_312824 prefixEnd_312824 11898449797199208026767 := by
  unfold tailWord_312824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704814309349774465420763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7606419079133032620561017 5704814309349774465420763)
  ·
    refine ⟨8557221464024661698131145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5704814309349774465420763 8557221464024661698131145)
    ·
      refine ⟨6417916098018496273598359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8557221464024661698131145 6417916098018496273598359)
      ·
        refine ⟨9626874147027744410397539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417916098018496273598359 9626874147027744410397539)
        ·
          refine ⟨14440311220541616615596309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9626874147027744410397539 14440311220541616615596309)
          ·
            refine ⟨676889588462888278856077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14440311220541616615596309 676889588462888278856077)
            ·
              refine ⟨253833595673583104571029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676889588462888278856077 253833595673583104571029)
              ·
                refine ⟨11898449797199208026767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 253833595673583104571029 11898449797199208026767)
                ·
                  rfl

theorem cell22_312824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 6].length) (baseStart_312824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312824 prefixEnd_312824 := by exact prefixLift 312824
  have htrace : WordTrace (prefixWord ++ tailWord_312824) baseStart_312824 baseEnd_312824 := by
    simpa [prefixWord, tailWord_312824, baseEnd_312824] using wordTrace_append hprefix tailTrace_312824
  have hstable : (prefixWord ++ tailWord_312824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312824).length < 2 ^ (prefixWord ++ tailWord_312824).sum := by decide
  have hdescent : baseEnd_312824 < baseStart_312824 := by decide
  rcases family_descends (prefixWord ++ tailWord_312824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312830 : List Nat := [4, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_312830 : Nat := 118140960795 + 312830 * 2 ^ 59
def prefixEnd_312830 : Nat := 4983230072969 + 3 ^ 40 * 312830 * 2
def baseEnd_312830 : Nat := 35696034032470285530295

theorem tailTrace_312830 : CollatzResearch.WordTrace tailWord_312830 prefixEnd_312830 35696034032470285530295 := by
  unfold tailWord_312830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426230932084726494444993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7606564971118541303706629 1426230932084726494444993)
  ·
    refine ⟨1069673199063544870833745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1426230932084726494444993 1069673199063544870833745)
    ·
      refine ⟨802254899297658653125309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1069673199063544870833745 802254899297658653125309)
      ·
        refine ⟨300845587236621994921991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 802254899297658653125309 300845587236621994921991)
        ·
          refine ⟨451268380854932992382987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300845587236621994921991 451268380854932992382987)
          ·
            refine ⟨676902571282399488574481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451268380854932992382987 676902571282399488574481)
            ·
              refine ⟨507676928461799616430861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676902571282399488574481 507676928461799616430861)
              ·
                refine ⟨190378848173174856161573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507676928461799616430861 190378848173174856161573)
                ·
                  refine ⟨35696034032470285530295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190378848173174856161573 35696034032470285530295)
                  ·
                    rfl

theorem cell22_312830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_312830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312830 prefixEnd_312830 := by exact prefixLift 312830
  have htrace : WordTrace (prefixWord ++ tailWord_312830) baseStart_312830 baseEnd_312830 := by
    simpa [prefixWord, tailWord_312830, baseEnd_312830] using wordTrace_append hprefix tailTrace_312830
  have hstable : (prefixWord ++ tailWord_312830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312830).length < 2 ^ (prefixWord ++ tailWord_312830).sum := by decide
  have hdescent : baseEnd_312830 < baseStart_312830 := by decide
  rcases family_descends (prefixWord ++ tailWord_312830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312845 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_312845 : Nat := 118140960795 + 312845 * 2 ^ 59
def prefixEnd_312845 : Nat := 4983230072969 + 3 ^ 40 * 312845 * 2
def baseEnd_312845 : Nat := 107093236903955817465839

theorem tailTrace_312845 : CollatzResearch.WordTrace tailWord_312845 prefixEnd_312845 107093236903955817465839 := by
  unfold tailWord_312845
  simp only [CollatzResearch.WordTrace]
  refine ⟨11410394551623469517355989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7606929701082313011570659 11410394551623469517355989)
  ·
    refine ⟨267431122303675066813031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11410394551623469517355989 267431122303675066813031)
    ·
      refine ⟨401146683455512600219547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267431122303675066813031 401146683455512600219547)
      ·
        refine ⟨601720025183268900329321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401146683455512600219547 601720025183268900329321)
        ·
          refine ⟨451290018887451675246991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601720025183268900329321 451290018887451675246991)
          ·
            refine ⟨676935028331177512870487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451290018887451675246991 676935028331177512870487)
            ·
              refine ⟨1015402542496766269305731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676935028331177512870487 1015402542496766269305731)
              ·
                refine ⟨1523103813745149403958597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015402542496766269305731 1523103813745149403958597)
                ·
                  refine ⟨285581965077215513242237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1523103813745149403958597 285581965077215513242237)
                  ·
                    refine ⟨107093236903955817465839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285581965077215513242237 107093236903955817465839)
                    ·
                      rfl

theorem cell22_312845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_312845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312845 prefixEnd_312845 := by exact prefixLift 312845
  have htrace : WordTrace (prefixWord ++ tailWord_312845) baseStart_312845 baseEnd_312845 := by
    simpa [prefixWord, tailWord_312845, baseEnd_312845] using wordTrace_append hprefix tailTrace_312845
  have hstable : (prefixWord ++ tailWord_312845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312845).length < 2 ^ (prefixWord ++ tailWord_312845).sum := by decide
  have hdescent : baseEnd_312845 < baseStart_312845 := by decide
  rcases family_descends (prefixWord ++ tailWord_312845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312862 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_312862 : Nat := 118140960795 + 312862 * 2 ^ 59
def prefixEnd_312862 : Nat := 4983230072969 + 3 ^ 40 * 312862 * 2
def baseEnd_312862 : Nat := 107099056351373439790787

theorem tailTrace_312862 : CollatzResearch.WordTrace tailWord_312862 prefixEnd_312862 107099056351373439790787 := by
  unfold tailWord_312862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426376824070235177590605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7607343061707920947149893 1426376824070235177590605)
  ·
    refine ⟨534891309026338191596477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1426376824070235177590605 534891309026338191596477)
    ·
      refine ⟨200584240884876821848679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 534891309026338191596477 200584240884876821848679)
      ·
        refine ⟨300876361327315232773019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200584240884876821848679 300876361327315232773019)
        ·
          refine ⟨451314541990972849159529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300876361327315232773019 451314541990972849159529)
          ·
            refine ⟨338485906493229636869647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451314541990972849159529 338485906493229636869647)
            ·
              refine ⟨507728859739844455304471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338485906493229636869647 507728859739844455304471)
              ·
                refine ⟨761593289609766682956707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507728859739844455304471 761593289609766682956707)
                ·
                  refine ⟨1142389934414650024435061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761593289609766682956707 1142389934414650024435061)
                  ·
                    refine ⟨107099056351373439790787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1142389934414650024435061 107099056351373439790787)
                    ·
                      rfl

theorem cell22_312862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_312862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312862 prefixEnd_312862 := by exact prefixLift 312862
  have htrace : WordTrace (prefixWord ++ tailWord_312862) baseStart_312862 baseEnd_312862 := by
    simpa [prefixWord, tailWord_312862, baseEnd_312862] using wordTrace_append hprefix tailTrace_312862
  have hstable : (prefixWord ++ tailWord_312862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312862).length < 2 ^ (prefixWord ++ tailWord_312862).sum := by decide
  have hdescent : baseEnd_312862 < baseStart_312862 := by decide
  rcases family_descends (prefixWord ++ tailWord_312862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312929 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_312929 : Nat := 118140960795 + 312929 * 2 ^ 59
def prefixEnd_312929 : Nat := 4983230072969 + 3 ^ 40 * 312929 * 2
def baseEnd_312929 : Nat := 107121991820607598365581

theorem tailTrace_312929 : CollatzResearch.WordTrace tailWord_312929 prefixEnd_312929 107121991820607598365581 := by
  unfold tailWord_312929
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413458283319151863413841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7608972188879434575609227 11413458283319151863413841)
  ·
    refine ⟨8560093712489363897560381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11413458283319151863413841 8560093712489363897560381)
    ·
      refine ⟨3210035142183511461585143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8560093712489363897560381 3210035142183511461585143)
      ·
        refine ⟨4815052713275267192377715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210035142183511461585143 4815052713275267192377715)
        ·
          refine ⟨7222579069912900788566573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815052713275267192377715 7222579069912900788566573)
          ·
            refine ⟨2708467151217337795712465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7222579069912900788566573 2708467151217337795712465)
            ·
              refine ⟨2031350363413003346784349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708467151217337795712465 2031350363413003346784349)
              ·
                refine ⟨761756386279876255044131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2031350363413003346784349 761756386279876255044131)
                ·
                  refine ⟨1142634579419814382566197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761756386279876255044131 1142634579419814382566197)
                  ·
                    refine ⟨107121991820607598365581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1142634579419814382566197 107121991820607598365581)
                    ·
                      rfl

theorem cell22_312929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_312929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312929 prefixEnd_312929 := by exact prefixLift 312929
  have htrace : WordTrace (prefixWord ++ tailWord_312929) baseStart_312929 baseEnd_312929 := by
    simpa [prefixWord, tailWord_312929, baseEnd_312929] using wordTrace_append hprefix tailTrace_312929
  have hstable : (prefixWord ++ tailWord_312929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312929).length < 2 ^ (prefixWord ++ tailWord_312929).sum := by decide
  have hdescent : baseEnd_312929 < baseStart_312929 := by decide
  rcases family_descends (prefixWord ++ tailWord_312929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312933 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 1, 4]
def baseStart_312933 : Nat := 118140960795 + 312933 * 2 ^ 59
def prefixEnd_312933 : Nat := 4983230072969 + 3 ^ 40 * 312933 * 2
def baseEnd_312933 : Nat := 107123361102352921265569

theorem tailTrace_312933 : CollatzResearch.WordTrace tailWord_312933 prefixEnd_312933 107123361102352921265569 := by
  unfold tailWord_312933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413604175304660546559453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7609069450203107031039635 11413604175304660546559453)
  ·
    refine ⟨4280101565739247704959795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11413604175304660546559453 4280101565739247704959795)
    ·
      refine ⟨6420152348608871557439693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280101565739247704959795 6420152348608871557439693)
      ·
        refine ⟨2407557130728326834039885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6420152348608871557439693 2407557130728326834039885)
        ·
          refine ⟨902833924023122562764957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2407557130728326834039885 902833924023122562764957)
          ·
            refine ⟨338562721508670961036859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 902833924023122562764957 338562721508670961036859)
            ·
              refine ⟨507844082263006441555289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338562721508670961036859 507844082263006441555289)
              ·
                refine ⟨380883061697254831166467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507844082263006441555289 380883061697254831166467)
                ·
                  refine ⟨571324592545882246749701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380883061697254831166467 571324592545882246749701)
                  ·
                    refine ⟨107123361102352921265569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 571324592545882246749701 107123361102352921265569)
                    ·
                      rfl

theorem cell22_312933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_312933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312933 prefixEnd_312933 := by exact prefixLift 312933
  have htrace : WordTrace (prefixWord ++ tailWord_312933) baseStart_312933 baseEnd_312933 := by
    simpa [prefixWord, tailWord_312933, baseEnd_312933] using wordTrace_append hprefix tailTrace_312933
  have hstable : (prefixWord ++ tailWord_312933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312933).length < 2 ^ (prefixWord ++ tailWord_312933).sum := by decide
  have hdescent : baseEnd_312933 < baseStart_312933 := by decide
  rcases family_descends (prefixWord ++ tailWord_312933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312946 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 1, 5]
def baseStart_312946 : Nat := 118140960795 + 312946 * 2 ^ 59
def prefixEnd_312946 : Nat := 4983230072969 + 3 ^ 40 * 312946 * 2
def baseEnd_312946 : Nat := 107127811268025220690529

theorem tailTrace_312946 : CollatzResearch.WordTrace tailWord_312946 prefixEnd_312946 107127811268025220690529 := by
  unfold tailWord_312946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853519581064390941695673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7609385549505042511188461 2853519581064390941695673)
  ·
    refine ⟨2140139685798293206271755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2853519581064390941695673 2140139685798293206271755)
    ·
      refine ⟨3210209528697439809407633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2140139685798293206271755 3210209528697439809407633)
      ·
        refine ⟨2407657146523079857055725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3210209528697439809407633 2407657146523079857055725)
        ·
          refine ⟨902871429946154946395897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2407657146523079857055725 902871429946154946395897)
          ·
            refine ⟨677153572459616209796923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902871429946154946395897 677153572459616209796923)
            ·
              refine ⟨1015730358689424314695385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677153572459616209796923 1015730358689424314695385)
              ·
                refine ⟨761797769017068236021539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015730358689424314695385 761797769017068236021539)
                ·
                  refine ⟨1142696653525602354032309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761797769017068236021539 1142696653525602354032309)
                  ·
                    refine ⟨107127811268025220690529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1142696653525602354032309 107127811268025220690529)
                    ·
                      rfl

theorem cell22_312946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_312946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312946 prefixEnd_312946 := by exact prefixLift 312946
  have htrace : WordTrace (prefixWord ++ tailWord_312946) baseStart_312946 baseEnd_312946 := by
    simpa [prefixWord, tailWord_312946, baseEnd_312946] using wordTrace_append hprefix tailTrace_312946
  have hstable : (prefixWord ++ tailWord_312946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312946).length < 2 ^ (prefixWord ++ tailWord_312946).sum := by decide
  have hdescent : baseEnd_312946 < baseStart_312946 := by decide
  rcases family_descends (prefixWord ++ tailWord_312946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312950 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_312950 : Nat := 118140960795 + 312950 * 2 ^ 59
def prefixEnd_312950 : Nat := 4983230072969 + 3 ^ 40 * 312950 * 2
def baseEnd_312950 : Nat := 107129180549770543590517

theorem tailTrace_312950 : CollatzResearch.WordTrace tailWord_312950 prefixEnd_312950 107129180549770543590517 := by
  unfold tailWord_312950
  simp only [CollatzResearch.WordTrace]
  refine ⟨713389013515192028120519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7609482810828714966618869 713389013515192028120519)
  ·
    refine ⟨1070083520272788042180779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713389013515192028120519 1070083520272788042180779)
    ·
      refine ⟨1605125280409182063271169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1070083520272788042180779 1605125280409182063271169)
      ·
        refine ⟨1203843960306886547453377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1605125280409182063271169 1203843960306886547453377)
        ·
          refine ⟨902882970230164910590033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203843960306886547453377 902882970230164910590033)
          ·
            refine ⟨677162227672623682942525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902882970230164910590033 677162227672623682942525)
            ·
              refine ⟨253935835377233881103447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 677162227672623682942525 253935835377233881103447)
              ·
                refine ⟨380903753065850821655171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253935835377233881103447 380903753065850821655171)
                ·
                  refine ⟨571355629598776232482757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380903753065850821655171 571355629598776232482757)
                  ·
                    refine ⟨107129180549770543590517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 571355629598776232482757 107129180549770543590517)
                    ·
                      rfl

theorem cell22_312950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_312950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312950 prefixEnd_312950 := by exact prefixLift 312950
  have htrace : WordTrace (prefixWord ++ tailWord_312950) baseStart_312950 baseEnd_312950 := by
    simpa [prefixWord, tailWord_312950, baseEnd_312950] using wordTrace_append hprefix tailTrace_312950
  have hstable : (prefixWord ++ tailWord_312950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312950).length < 2 ^ (prefixWord ++ tailWord_312950).sum := by decide
  have hdescent : baseEnd_312950 < baseStart_312950 := by decide
  rcases family_descends (prefixWord ++ tailWord_312950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312961 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 2, 4]
def baseStart_312961 : Nat := 118140960795 + 312961 * 2 ^ 59
def prefixEnd_312961 : Nat := 4983230072969 + 3 ^ 40 * 312961 * 2
def baseEnd_312961 : Nat := 107132946074570181565483

theorem tailTrace_312961 : CollatzResearch.WordTrace tailWord_312961 prefixEnd_312961 107132946074570181565483 := by
  unfold tailWord_312961
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414625419203221328578737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7609750279468814219052491 11414625419203221328578737)
  ·
    refine ⟨8560969064402415996434053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11414625419203221328578737 8560969064402415996434053)
    ·
      refine ⟨1605181699575452999331385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8560969064402415996434053 1605181699575452999331385)
      ·
        refine ⟨1203886274681589749498539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1605181699575452999331385 1203886274681589749498539)
        ·
          refine ⟨1805829412022384624247809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203886274681589749498539 1805829412022384624247809)
          ·
            refine ⟨1354372059016788468185857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805829412022384624247809 1354372059016788468185857)
            ·
              refine ⟨1015779044262591351139393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354372059016788468185857 1015779044262591351139393)
              ·
                refine ⟨761834283196943513354545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015779044262591351139393 761834283196943513354545)
                ·
                  refine ⟨571375712397707635015909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 761834283196943513354545 571375712397707635015909)
                  ·
                    refine ⟨107132946074570181565483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 571375712397707635015909 107132946074570181565483)
                    ·
                      rfl

theorem cell22_312961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_312961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312961 prefixEnd_312961 := by exact prefixLift 312961
  have htrace : WordTrace (prefixWord ++ tailWord_312961) baseStart_312961 baseEnd_312961 := by
    simpa [prefixWord, tailWord_312961, baseEnd_312961] using wordTrace_append hprefix tailTrace_312961
  have hstable : (prefixWord ++ tailWord_312961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312961).length < 2 ^ (prefixWord ++ tailWord_312961).sum := by decide
  have hdescent : baseEnd_312961 < baseStart_312961 := by decide
  rcases family_descends (prefixWord ++ tailWord_312961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312989 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_312989 : Nat := 118140960795 + 312989 * 2 ^ 59
def prefixEnd_312989 : Nat := 4983230072969 + 3 ^ 40 * 312989 * 2
def baseEnd_312989 : Nat := 107142531046787441865397

theorem tailTrace_312989 : CollatzResearch.WordTrace tailWord_312989 prefixEnd_312989 107142531046787441865397 := by
  unfold tailWord_312989
  simp only [CollatzResearch.WordTrace]
  refine ⟨11415646663101782110598021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7610431108734521407065347 11415646663101782110598021)
  ·
    refine ⟨2140433749331584145737129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11415646663101782110598021 2140433749331584145737129)
    ·
      refine ⟨1605325311998688109302847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2140433749331584145737129 1605325311998688109302847)
      ·
        refine ⟨2407987967998032163954271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605325311998688109302847 2407987967998032163954271)
        ·
          refine ⟨3611981951997048245931407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407987967998032163954271 3611981951997048245931407)
          ·
            refine ⟨5417972927995572368897111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611981951997048245931407 5417972927995572368897111)
            ·
              refine ⟨8126959391993358553345667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417972927995572368897111 8126959391993358553345667)
              ·
                refine ⟨12190439087990037830018501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8126959391993358553345667 12190439087990037830018501)
                ·
                  refine ⟨2285707328998132093128469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12190439087990037830018501 2285707328998132093128469)
                  ·
                    refine ⟨107142531046787441865397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2285707328998132093128469 107142531046787441865397)
                    ·
                      rfl

theorem cell22_312989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_312989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_312989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_312989 prefixEnd_312989 := by exact prefixLift 312989
  have htrace : WordTrace (prefixWord ++ tailWord_312989) baseStart_312989 baseEnd_312989 := by
    simpa [prefixWord, tailWord_312989, baseEnd_312989] using wordTrace_append hprefix tailTrace_312989
  have hstable : (prefixWord ++ tailWord_312989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312989).length < 2 ^ (prefixWord ++ tailWord_312989).sum := by decide
  have hdescent : baseEnd_312989 < baseStart_312989 := by decide
  rcases family_descends (prefixWord ++ tailWord_312989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313008 : List Nat := [2, 1, 1, 1, 2, 1, 5, 5, 1, 3]
def baseStart_313008 : Nat := 118140960795 + 313008 * 2 ^ 59
def prefixEnd_313008 : Nat := 4983230072969 + 3 ^ 40 * 313008 * 2
def baseEnd_313008 : Nat := 107149035135077725640339

theorem tailTrace_313008 : CollatzResearch.WordTrace tailWord_313008 prefixEnd_313008 107149035135077725640339 := by
  unfold tailWord_313008
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708169825016474177769839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7610893100021965570359785 5708169825016474177769839)
  ·
    refine ⟨8562254737524711266654759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5708169825016474177769839 8562254737524711266654759)
    ·
      refine ⟨12843382106287066899982139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562254737524711266654759 12843382106287066899982139)
      ·
        refine ⟨19265073159430600349973209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12843382106287066899982139 19265073159430600349973209)
        ·
          refine ⟨14448804869572950262479907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19265073159430600349973209 14448804869572950262479907)
          ·
            refine ⟨21673207304359425393719861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14448804869572950262479907 21673207304359425393719861)
            ·
              refine ⟨2031863184783696130661237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21673207304359425393719861 2031863184783696130661237)
              ·
                refine ⟨190487173573471512249491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2031863184783696130661237 190487173573471512249491)
                ·
                  refine ⟨285730760360207268374237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190487173573471512249491 285730760360207268374237)
                  ·
                    refine ⟨107149035135077725640339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285730760360207268374237 107149035135077725640339)
                    ·
                      rfl

theorem cell22_313008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 3].length) (baseStart_313008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313008 prefixEnd_313008 := by exact prefixLift 313008
  have htrace : WordTrace (prefixWord ++ tailWord_313008) baseStart_313008 baseEnd_313008 := by
    simpa [prefixWord, tailWord_313008, baseEnd_313008] using wordTrace_append hprefix tailTrace_313008
  have hstable : (prefixWord ++ tailWord_313008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313008).length < 2 ^ (prefixWord ++ tailWord_313008).sum := by decide
  have hdescent : baseEnd_313008 < baseStart_313008 := by decide
  rcases family_descends (prefixWord ++ tailWord_313008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313038 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_313038 : Nat := 118140960795 + 313038 * 2 ^ 59
def prefixEnd_313038 : Nat := 4983230072969 + 3 ^ 40 * 313038 * 2
def baseEnd_313038 : Nat := 35719768249389215796749

theorem tailTrace_313038 : CollatzResearch.WordTrace tailWord_313038 prefixEnd_313038 35719768249389215796749 := by
  unfold tailWord_313038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427179229990532934891471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7611622559949508986087845 1427179229990532934891471)
  ·
    refine ⟨2140768844985799402337207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1427179229990532934891471 2140768844985799402337207)
    ·
      refine ⟨3211153267478699103505811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2140768844985799402337207 3211153267478699103505811)
      ·
        refine ⟨4816729901218048655258717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211153267478699103505811 4816729901218048655258717)
        ·
          refine ⟨1806273712956768245722019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4816729901218048655258717 1806273712956768245722019)
          ·
            refine ⟨2709410569435152368583029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806273712956768245722019 2709410569435152368583029)
            ·
              refine ⟨254007240884545534554659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2709410569435152368583029 254007240884545534554659)
              ·
                refine ⟨381010861326818301831989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254007240884545534554659 381010861326818301831989)
                ·
                  refine ⟨35719768249389215796749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 381010861326818301831989 35719768249389215796749)
                  ·
                    rfl

theorem cell22_313038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_313038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313038 prefixEnd_313038 := by exact prefixLift 313038
  have htrace : WordTrace (prefixWord ++ tailWord_313038) baseStart_313038 baseEnd_313038 := by
    simpa [prefixWord, tailWord_313038, baseEnd_313038] using wordTrace_append hprefix tailTrace_313038
  have hstable : (prefixWord ++ tailWord_313038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313038).length < 2 ^ (prefixWord ++ tailWord_313038).sum := by decide
  have hdescent : baseEnd_313038 < baseStart_313038 := by decide
  rcases family_descends (prefixWord ++ tailWord_313038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313059 : List Nat := [1, 1, 1, 7, 3, 1, 1, 3, 1, 3]
def baseStart_313059 : Nat := 118140960795 + 313059 * 2 ^ 59
def prefixEnd_313059 : Nat := 4983230072969 + 3 ^ 40 * 313059 * 2
def baseEnd_313059 : Nat := 107166493477330592615183

theorem tailTrace_313059 : CollatzResearch.WordTrace tailWord_313059 prefixEnd_313059 107166493477330592615183 := by
  unfold tailWord_313059
  simp only [CollatzResearch.WordTrace]
  refine ⟨11418199772848184065646231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7612133181898789377097487 11418199772848184065646231)
  ·
    refine ⟨17127299659272276098469347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11418199772848184065646231 17127299659272276098469347)
    ·
      refine ⟨25690949488908414147704021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17127299659272276098469347 25690949488908414147704021)
      ·
        refine ⟨602131628646290956586813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25690949488908414147704021 602131628646290956586813)
        ·
          refine ⟨225799360742359108720055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602131628646290956586813 225799360742359108720055)
          ·
            refine ⟨338699041113538663080083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225799360742359108720055 338699041113538663080083)
            ·
              refine ⟨508048561670307994620125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338699041113538663080083 508048561670307994620125)
              ·
                refine ⟨190518210626365497982547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508048561670307994620125 190518210626365497982547)
                ·
                  refine ⟨285777315939548246973821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190518210626365497982547 285777315939548246973821)
                  ·
                    refine ⟨107166493477330592615183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285777315939548246973821 107166493477330592615183)
                    ·
                      rfl

theorem cell22_313059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 3].length) (baseStart_313059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313059 prefixEnd_313059 := by exact prefixLift 313059
  have htrace : WordTrace (prefixWord ++ tailWord_313059) baseStart_313059 baseEnd_313059 := by
    simpa [prefixWord, tailWord_313059, baseEnd_313059] using wordTrace_append hprefix tailTrace_313059
  have hstable : (prefixWord ++ tailWord_313059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313059).length < 2 ^ (prefixWord ++ tailWord_313059).sum := by decide
  have hdescent : baseEnd_313059 < baseStart_313059 := by decide
  rcases family_descends (prefixWord ++ tailWord_313059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313076 : List Nat := [2, 6, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_313076 : Nat := 118140960795 + 313076 * 2 ^ 59
def prefixEnd_313076 : Nat := 4983230072969 + 3 ^ 40 * 313076 * 2
def baseEnd_313076 : Nat := 107172312924748214940131

theorem tailTrace_313076 : CollatzResearch.WordTrace tailWord_313076 prefixEnd_313076 107172312924748214940131 := by
  unfold tailWord_313076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709409906893297984507541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7612546542524397312676721 5709409906893297984507541)
  ·
    refine ⟨267628589385623343023791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5709409906893297984507541 267628589385623343023791)
    ·
      refine ⟨401442884078435014535687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267628589385623343023791 401442884078435014535687)
      ·
        refine ⟨602164326117652521803531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401442884078435014535687 602164326117652521803531)
        ·
          refine ⟨903246489176478782705297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602164326117652521803531 903246489176478782705297)
          ·
            refine ⟨677434866882359087028973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903246489176478782705297 677434866882359087028973)
            ·
              refine ⟨254038075080884657635865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 677434866882359087028973 254038075080884657635865)
              ·
                refine ⟨190528556310663493226899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254038075080884657635865 190528556310663493226899)
                ·
                  refine ⟨285792834465995239840349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190528556310663493226899 285792834465995239840349)
                  ·
                    refine ⟨107172312924748214940131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285792834465995239840349 107172312924748214940131)
                    ·
                      rfl

theorem cell22_313076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_313076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313076 prefixEnd_313076 := by exact prefixLift 313076
  have htrace : WordTrace (prefixWord ++ tailWord_313076) baseStart_313076 baseEnd_313076 := by
    simpa [prefixWord, tailWord_313076, baseEnd_313076] using wordTrace_append hprefix tailTrace_313076
  have hstable : (prefixWord ++ tailWord_313076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313076).length < 2 ^ (prefixWord ++ tailWord_313076).sum := by decide
  have hdescent : baseEnd_313076 < baseStart_313076 := by decide
  rcases family_descends (prefixWord ++ tailWord_313076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313096 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_313096 : Nat := 118140960795 + 313096 * 2 ^ 59
def prefixEnd_313096 : Nat := 4983230072969 + 3 ^ 40 * 313096 * 2
def baseEnd_313096 : Nat := 107179159333474829440069

theorem tailTrace_313096 : CollatzResearch.WordTrace tailWord_313096 prefixEnd_313096 107179159333474829440069 := by
  unfold tailWord_313096
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709774636857069692371571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7613032849142759589828761 5709774636857069692371571)
  ·
    refine ⟨8564661955285604538557357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5709774636857069692371571 8564661955285604538557357)
    ·
      refine ⟨3211748233232101701959009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8564661955285604538557357 3211748233232101701959009)
      ·
        refine ⟨2408811174924076276469257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3211748233232101701959009 2408811174924076276469257)
        ·
          refine ⟨1806608381193057207351943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2408811174924076276469257 1806608381193057207351943)
          ·
            refine ⟨2709912571789585811027915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806608381193057207351943 2709912571789585811027915)
            ·
              refine ⟨4064868857684378716541873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709912571789585811027915 4064868857684378716541873)
              ·
                refine ⟨3048651643263284037406405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064868857684378716541873 3048651643263284037406405)
                ·
                  refine ⟨571622183111865757013701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3048651643263284037406405 571622183111865757013701)
                  ·
                    refine ⟨107179159333474829440069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 571622183111865757013701 107179159333474829440069)
                    ·
                      rfl

theorem cell22_313096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_313096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313096 prefixEnd_313096 := by exact prefixLift 313096
  have htrace : WordTrace (prefixWord ++ tailWord_313096) baseStart_313096 baseEnd_313096 := by
    simpa [prefixWord, tailWord_313096, baseEnd_313096] using wordTrace_append hprefix tailTrace_313096
  have hstable : (prefixWord ++ tailWord_313096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313096).length < 2 ^ (prefixWord ++ tailWord_313096).sum := by decide
  have hdescent : baseEnd_313096 < baseStart_313096 := by decide
  rcases family_descends (prefixWord ++ tailWord_313096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313111 : List Nat := [1, 1, 3, 4, 2, 1, 2, 8]
def baseStart_313111 : Nat := 118140960795 + 313111 * 2 ^ 59
def prefixEnd_313111 : Nat := 4983230072969 + 3 ^ 40 * 313111 * 2
def baseEnd_313111 : Nat := 11909366015557754479447

theorem tailTrace_313111 : CollatzResearch.WordTrace tailWord_313111 prefixEnd_313111 11909366015557754479447 := by
  unfold tailWord_313111
  simp only [CollatzResearch.WordTrace]
  refine ⟨11420096368659796946539187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7613397579106531297692791 11420096368659796946539187)
  ·
    refine ⟨17130144552989695419808781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11420096368659796946539187 17130144552989695419808781)
    ·
      refine ⟨6423804207371135782428293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17130144552989695419808781 6423804207371135782428293)
      ·
        refine ⟨1204463288882087959205305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6423804207371135782428293 1204463288882087959205305)
        ·
          refine ⟨903347466661565969403979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204463288882087959205305 903347466661565969403979)
          ·
            refine ⟨1355021199992348954105969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903347466661565969403979 1355021199992348954105969)
            ·
              refine ⟨1016265899994261715579477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1355021199992348954105969 1016265899994261715579477)
              ·
                refine ⟨11909366015557754479447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1016265899994261715579477 11909366015557754479447)
                ·
                  rfl

theorem cell22_313111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 8].length) (baseStart_313111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313111 prefixEnd_313111 := by exact prefixLift 313111
  have htrace : WordTrace (prefixWord ++ tailWord_313111) baseStart_313111 baseEnd_313111 := by
    simpa [prefixWord, tailWord_313111, baseEnd_313111] using wordTrace_append hprefix tailTrace_313111
  have hstable : (prefixWord ++ tailWord_313111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313111).length < 2 ^ (prefixWord ++ tailWord_313111).sum := by decide
  have hdescent : baseEnd_313111 < baseStart_313111 := by decide
  rcases family_descends (prefixWord ++ tailWord_313111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313134 : List Nat := [4, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_313134 : Nat := 118140960795 + 313134 * 2 ^ 59
def prefixEnd_313134 : Nat := 4983230072969 + 3 ^ 40 * 313134 * 2
def baseEnd_313134 : Nat := 35730722503351798996651

theorem tailTrace_313134 : CollatzResearch.WordTrace tailWord_313134 prefixEnd_313134 35730722503351798996651 := by
  unfold tailWord_313134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427616905947058984328307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7613956831717647916417637 1427616905947058984328307)
  ·
    refine ⟨2141425358920588476492461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1427616905947058984328307 2141425358920588476492461)
    ·
      refine ⟨803034509595220678684673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2141425358920588476492461 803034509595220678684673)
      ·
        refine ⟨602275882196415509013505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 803034509595220678684673 602275882196415509013505)
        ·
          refine ⟨451706911647311631760129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602275882196415509013505 451706911647311631760129)
          ·
            refine ⟨338780183735483723820097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451706911647311631760129 338780183735483723820097)
            ·
              refine ⟨254085137801612792865073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338780183735483723820097 254085137801612792865073)
              ·
                refine ⟨190563853351209594648805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254085137801612792865073 190563853351209594648805)
                ·
                  refine ⟨35730722503351798996651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190563853351209594648805 35730722503351798996651)
                  ·
                    rfl

theorem cell22_313134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_313134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313134 prefixEnd_313134 := by exact prefixLift 313134
  have htrace : WordTrace (prefixWord ++ tailWord_313134) baseStart_313134 baseEnd_313134 := by
    simpa [prefixWord, tailWord_313134, baseEnd_313134] using wordTrace_append hprefix tailTrace_313134
  have hstable : (prefixWord ++ tailWord_313134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313134).length < 2 ^ (prefixWord ++ tailWord_313134).sum := by decide
  have hdescent : baseEnd_313134 < baseStart_313134 := by decide
  rcases family_descends (prefixWord ++ tailWord_313134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313145 : List Nat := [1, 2, 1, 7, 1, 2, 1, 7]
def baseStart_313145 : Nat := 118140960795 + 313145 * 2 ^ 59
def prefixEnd_313145 : Nat := 4983230072969 + 3 ^ 40 * 313145 * 2
def baseEnd_313145 : Nat := 11910659226095003884991

theorem tailTrace_313145 : CollatzResearch.WordTrace tailWord_313145 prefixEnd_313145 11910659226095003884991 := by
  unfold tailWord_313145
  simp only [CollatzResearch.WordTrace]
  refine ⟨11421336450536620753276889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7614224300357747168851259 11421336450536620753276889)
  ·
    refine ⟨8566002337902465564957667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11421336450536620753276889 8566002337902465564957667)
    ·
      refine ⟨12849003506853698347436501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566002337902465564957667 12849003506853698347436501)
      ·
        refine ⟨301148519691883555018043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12849003506853698347436501 301148519691883555018043)
        ·
          refine ⟨451722779537825332527065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301148519691883555018043 451722779537825332527065)
          ·
            refine ⟨338792084653368999395299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451722779537825332527065 338792084653368999395299)
            ·
              refine ⟨508188126980053499092949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338792084653368999395299 508188126980053499092949)
              ·
                refine ⟨11910659226095003884991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 508188126980053499092949 11910659226095003884991)
                ·
                  rfl

theorem cell22_313145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 7].length) (baseStart_313145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313145 prefixEnd_313145 := by exact prefixLift 313145
  have htrace : WordTrace (prefixWord ++ tailWord_313145) baseStart_313145 baseEnd_313145 := by
    simpa [prefixWord, tailWord_313145, baseEnd_313145] using wordTrace_append hprefix tailTrace_313145
  have hstable : (prefixWord ++ tailWord_313145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313145).length < 2 ^ (prefixWord ++ tailWord_313145).sum := by decide
  have hdescent : baseEnd_313145 < baseStart_313145 := by decide
  rcases family_descends (prefixWord ++ tailWord_313145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313233 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 4, 3]
def baseStart_313233 : Nat := 118140960795 + 313233 * 2 ^ 59
def prefixEnd_313233 : Nat := 4983230072969 + 3 ^ 40 * 313233 * 2
def baseEnd_313233 : Nat := 107226057233252138764649

theorem tailTrace_313233 : CollatzResearch.WordTrace tailWord_313233 prefixEnd_313233 107226057233252138764649 := by
  unfold tailWord_313233
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424546074217811782480353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7616364049478541188320235 11424546074217811782480353)
  ·
    refine ⟨8568409555663358836860265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11424546074217811782480353 8568409555663358836860265)
    ·
      refine ⟨6426307166747519127645199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8568409555663358836860265 6426307166747519127645199)
      ·
        refine ⟨9639460750121278691467799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426307166747519127645199 9639460750121278691467799)
        ·
          refine ⟨14459191125181918037201699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9639460750121278691467799 14459191125181918037201699)
          ·
            refine ⟨21688786687772877055802549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14459191125181918037201699 21688786687772877055802549)
            ·
              refine ⟨2033323751978707223981489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21688786687772877055802549 2033323751978707223981489)
              ·
                refine ⟨1524992813984030417986117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033323751978707223981489 1524992813984030417986117)
                ·
                  refine ⟨285936152622005703372397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1524992813984030417986117 285936152622005703372397)
                  ·
                    refine ⟨107226057233252138764649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285936152622005703372397 107226057233252138764649)
                    ·
                      rfl

theorem cell22_313233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_313233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313233 prefixEnd_313233 := by exact prefixLift 313233
  have htrace : WordTrace (prefixWord ++ tailWord_313233) baseStart_313233 baseEnd_313233 := by
    simpa [prefixWord, tailWord_313233, baseEnd_313233] using wordTrace_append hprefix tailTrace_313233
  have hstable : (prefixWord ++ tailWord_313233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313233).length < 2 ^ (prefixWord ++ tailWord_313233).sum := by decide
  have hdescent : baseEnd_313233 < baseStart_313233 := by decide
  rcases family_descends (prefixWord ++ tailWord_313233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313252 : List Nat := [2, 3, 1, 2, 1, 4, 3, 2, 4]
def baseStart_313252 : Nat := 118140960795 + 313252 * 2 ^ 59
def prefixEnd_313252 : Nat := 4983230072969 + 3 ^ 40 * 313252 * 2
def baseEnd_313252 : Nat := 35744187107180807513197

theorem tailTrace_313252 : CollatzResearch.WordTrace tailWord_313252 prefixEnd_313252 35744187107180807513197 := by
  unfold tailWord_313252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712619530574489013711005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7616826040765985351614673 5712619530574489013711005)
  ·
    refine ⟨2142232323965433380141627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5712619530574489013711005 2142232323965433380141627)
    ·
      refine ⟨3213348485948150070212441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142232323965433380141627 3213348485948150070212441)
      ·
        refine ⟨2410011364461112552659331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3213348485948150070212441 2410011364461112552659331)
        ·
          refine ⟨3615017046691668828988997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410011364461112552659331 3615017046691668828988997)
          ·
            refine ⟨677815696254687905435437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3615017046691668828988997 677815696254687905435437)
            ·
              refine ⟨254180886095507964538289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 677815696254687905435437 254180886095507964538289)
              ·
                refine ⟨190635664571630973403717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254180886095507964538289 190635664571630973403717)
                ·
                  refine ⟨35744187107180807513197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190635664571630973403717 35744187107180807513197)
                  ·
                    rfl

theorem cell22_313252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_313252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313252 prefixEnd_313252 := by exact prefixLift 313252
  have htrace : WordTrace (prefixWord ++ tailWord_313252) baseStart_313252 baseEnd_313252 := by
    simpa [prefixWord, tailWord_313252, baseEnd_313252] using wordTrace_append hprefix tailTrace_313252
  have hstable : (prefixWord ++ tailWord_313252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313252).length < 2 ^ (prefixWord ++ tailWord_313252).sum := by decide
  have hdescent : baseEnd_313252 < baseStart_313252 := by decide
  rcases family_descends (prefixWord ++ tailWord_313252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313314 : List Nat := [3, 3, 3, 1, 3, 1, 1, 7]
def baseStart_313314 : Nat := 118140960795 + 313314 * 2 ^ 59
def prefixEnd_313314 : Nat := 4983230072969 + 3 ^ 40 * 313314 * 2
def baseEnd_313314 : Nat := 11917087243177214165489

theorem tailTrace_313314 : CollatzResearch.WordTrace tailWord_313314 prefixEnd_313314 11917087243177214165489 := by
  unfold tailWord_313314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856875096731090654044749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7618333591282908410785997 2856875096731090654044749)
  ·
    refine ⟨1071328161274158995266781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2856875096731090654044749 1071328161274158995266781)
    ·
      refine ⟨401748060477809623225043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1071328161274158995266781 401748060477809623225043)
      ·
        refine ⟨602622090716714434837565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401748060477809623225043 602622090716714434837565)
        ·
          refine ⟨225983284018767913064087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602622090716714434837565 225983284018767913064087)
          ·
            refine ⟨338974926028151869596131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225983284018767913064087 338974926028151869596131)
            ·
              refine ⟨508462389042227804394197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338974926028151869596131 508462389042227804394197)
              ·
                refine ⟨11917087243177214165489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 508462389042227804394197 11917087243177214165489)
                ·
                  rfl

theorem cell22_313314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_313314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313314 prefixEnd_313314 := by exact prefixLift 313314
  have htrace : WordTrace (prefixWord ++ tailWord_313314) baseStart_313314 baseEnd_313314 := by
    simpa [prefixWord, tailWord_313314, baseEnd_313314] using wordTrace_append hprefix tailTrace_313314
  have hstable : (prefixWord ++ tailWord_313314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313314).length < 2 ^ (prefixWord ++ tailWord_313314).sum := by decide
  have hdescent : baseEnd_313314 < baseStart_313314 := by decide
  rcases family_descends (prefixWord ++ tailWord_313314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313355 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 1, 4]
def baseStart_313355 : Nat := 118140960795 + 313355 * 2 ^ 59
def prefixEnd_313355 : Nat := 4983230072969 + 3 ^ 40 * 313355 * 2
def baseEnd_313355 : Nat := 107267820326484487214275

theorem tailTrace_313355 : CollatzResearch.WordTrace tailWord_313355 prefixEnd_313355 107267820326484487214275 := by
  unfold tailWord_313355
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428995779775826618421519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7619330519850551078947679 11428995779775826618421519)
  ·
    refine ⟨17143493669663739927632279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11428995779775826618421519 17143493669663739927632279)
    ·
      refine ⟨25715240504495609891448419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17143493669663739927632279 25715240504495609891448419)
      ·
        refine ⟨38572860756743414837172629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25715240504495609891448419 38572860756743414837172629)
        ·
          refine ⟨1808102847972347570492467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38572860756743414837172629 1808102847972347570492467)
          ·
            refine ⟨2712154271958521355738701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808102847972347570492467 2712154271958521355738701)
            ·
              refine ⟨1017057851984445508402013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2712154271958521355738701 1017057851984445508402013)
              ·
                refine ⟨381396694494167065650755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1017057851984445508402013 381396694494167065650755)
                ·
                  refine ⟨572095041741250598476133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381396694494167065650755 572095041741250598476133)
                  ·
                    refine ⟨107267820326484487214275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 572095041741250598476133 107267820326484487214275)
                    ·
                      rfl

theorem cell22_313355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 4].length) (baseStart_313355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313355 prefixEnd_313355 := by exact prefixLift 313355
  have htrace : WordTrace (prefixWord ++ tailWord_313355) baseStart_313355 baseEnd_313355 := by
    simpa [prefixWord, tailWord_313355, baseEnd_313355] using wordTrace_append hprefix tailTrace_313355
  have hstable : (prefixWord ++ tailWord_313355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313355).length < 2 ^ (prefixWord ++ tailWord_313355).sum := by decide
  have hdescent : baseEnd_313355 < baseStart_313355 := by decide
  rcases family_descends (prefixWord ++ tailWord_313355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313370 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_313370 : Nat := 118140960795 + 313370 * 2 ^ 59
def prefixEnd_313370 : Nat := 4983230072969 + 3 ^ 40 * 313370 * 2
def baseEnd_313370 : Nat := 35757651711009816029743

theorem tailTrace_313370 : CollatzResearch.WordTrace tailWord_313370 prefixEnd_313370 35757651711009816029743 := by
  unfold tailWord_313370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857385718680371045054391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7619695249814322786811709 2857385718680371045054391)
  ·
    refine ⟨4286078578020556567581587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2857385718680371045054391 4286078578020556567581587)
    ·
      refine ⟨6429117867030834851372381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4286078578020556567581587 6429117867030834851372381)
      ·
        refine ⟨2410919200136563069264643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6429117867030834851372381 2410919200136563069264643)
        ·
          refine ⟨3616378800204844603896965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410919200136563069264643 3616378800204844603896965)
          ·
            refine ⟨678071025038408363230681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3616378800204844603896965 678071025038408363230681)
            ·
              refine ⟨508553268778806272423011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678071025038408363230681 508553268778806272423011)
              ·
                refine ⟨762829903168209408634517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508553268778806272423011 762829903168209408634517)
                ·
                  refine ⟨35757651711009816029743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 762829903168209408634517 35757651711009816029743)
                  ·
                    rfl

theorem cell22_313370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_313370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313370 prefixEnd_313370 := by exact prefixLift 313370
  have htrace : WordTrace (prefixWord ++ tailWord_313370) baseStart_313370 baseEnd_313370 := by
    simpa [prefixWord, tailWord_313370, baseEnd_313370] using wordTrace_append hprefix tailTrace_313370
  have hstable : (prefixWord ++ tailWord_313370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313370).length < 2 ^ (prefixWord ++ tailWord_313370).sum := by decide
  have hdescent : baseEnd_313370 < baseStart_313370 := by decide
  rcases family_descends (prefixWord ++ tailWord_313370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313436 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_313436 : Nat := 118140960795 + 313436 * 2 ^ 59
def prefixEnd_313436 : Nat := 4983230072969 + 3 ^ 40 * 313436 * 2
def baseEnd_313436 : Nat := 107295548281827275939027

theorem tailTrace_313436 : CollatzResearch.WordTrace tailWord_313436 prefixEnd_313436 107295548281827275939027 := by
  unfold tailWord_313436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5715975046241188726060081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7621300061654918301413441 5715975046241188726060081)
  ·
    refine ⟨4286981284680891544545061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5715975046241188726060081 4286981284680891544545061)
    ·
      refine ⟨803808990877667164602199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4286981284680891544545061 803808990877667164602199)
      ·
        refine ⟨1205713486316500746903299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803808990877667164602199 1205713486316500746903299)
        ·
          refine ⟨1808570229474751120354949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205713486316500746903299 1808570229474751120354949)
          ·
            refine ⟨339106918026515835066553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1808570229474751120354949 339106918026515835066553)
            ·
              refine ⟨254330188519886876299915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339106918026515835066553 254330188519886876299915)
              ·
                refine ⟨381495282779830314449873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254330188519886876299915 381495282779830314449873)
                ·
                  refine ⟨286121462084872735837405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381495282779830314449873 286121462084872735837405)
                  ·
                    refine ⟨107295548281827275939027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286121462084872735837405 107295548281827275939027)
                    ·
                      rfl

theorem cell22_313436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_313436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313436 prefixEnd_313436 := by exact prefixLift 313436
  have htrace : WordTrace (prefixWord ++ tailWord_313436) baseStart_313436 baseEnd_313436 := by
    simpa [prefixWord, tailWord_313436, baseEnd_313436] using wordTrace_append hprefix tailTrace_313436
  have hstable : (prefixWord ++ tailWord_313436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313436).length < 2 ^ (prefixWord ++ tailWord_313436).sum := by decide
  have hdescent : baseEnd_313436 < baseStart_313436 := by decide
  rcases family_descends (prefixWord ++ tailWord_313436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313477 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 5]
def baseStart_313477 : Nat := 118140960795 + 313477 * 2 ^ 59
def prefixEnd_313477 : Nat := 4983230072969 + 3 ^ 40 * 313477 * 2
def baseEnd_313477 : Nat := 35769861139905611887967

theorem tailTrace_313477 : CollatzResearch.WordTrace tailWord_313477 prefixEnd_313477 35769861139905611887967 := by
  unfold tailWord_313477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11433445485333841454362685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7622296990222560969575123 11433445485333841454362685)
  ·
    refine ⟨4287542057000190545386007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11433445485333841454362685 4287542057000190545386007)
    ·
      refine ⟨6431313085500285818079011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4287542057000190545386007 6431313085500285818079011)
      ·
        refine ⟨9646969628250428727118517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431313085500285818079011 9646969628250428727118517)
        ·
          refine ⟨904403402648477693167361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9646969628250428727118517 904403402648477693167361)
          ·
            refine ⟨678302551986358269875521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 904403402648477693167361 678302551986358269875521)
            ·
              refine ⟨508726913989768702406641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678302551986358269875521 508726913989768702406641)
              ·
                refine ⟨381545185492326526804981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508726913989768702406641 381545185492326526804981)
                ·
                  refine ⟨35769861139905611887967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 381545185492326526804981 35769861139905611887967)
                  ·
                    rfl

theorem cell22_313477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_313477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313477 prefixEnd_313477 := by exact prefixLift 313477
  have htrace : WordTrace (prefixWord ++ tailWord_313477) baseStart_313477 baseEnd_313477 := by
    simpa [prefixWord, tailWord_313477, baseEnd_313477] using wordTrace_append hprefix tailTrace_313477
  have hstable : (prefixWord ++ tailWord_313477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313477).length < 2 ^ (prefixWord ++ tailWord_313477).sum := by decide
  have hdescent : baseEnd_313477 < baseStart_313477 := by decide
  rcases family_descends (prefixWord ++ tailWord_313477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313505 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 8]
def baseStart_313505 : Nat := 118140960795 + 313505 * 2 ^ 59
def prefixEnd_313505 : Nat := 4983230072969 + 3 ^ 40 * 313505 * 2
def baseEnd_313505 : Nat := 35773056130644698654605

theorem tailTrace_313505 : CollatzResearch.WordTrace tailWord_313505 prefixEnd_313505 35773056130644698654605 := by
  unfold tailWord_313505
  simp only [CollatzResearch.WordTrace]
  refine ⟨11434466729232402236381969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7622977819488268157587979 11434466729232402236381969)
  ·
    refine ⟨8575850046924301677286477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11434466729232402236381969 8575850046924301677286477)
    ·
      refine ⟨3215943767596613128982429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8575850046924301677286477 3215943767596613128982429)
      ·
        refine ⟨1205978912848729923368411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3215943767596613128982429 1205978912848729923368411)
        ·
          refine ⟨1808968369273094885052617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205978912848729923368411 1808968369273094885052617)
          ·
            refine ⟨1356726276954821163789463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808968369273094885052617 1356726276954821163789463)
            ·
              refine ⟨2035089415432231745684195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356726276954821163789463 2035089415432231745684195)
              ·
                refine ⟨3052634123148347618526293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035089415432231745684195 3052634123148347618526293)
                ·
                  refine ⟨35773056130644698654605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3052634123148347618526293 35773056130644698654605)
                  ·
                    rfl

theorem cell22_313505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_313505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313505 prefixEnd_313505 := by exact prefixLift 313505
  have htrace : WordTrace (prefixWord ++ tailWord_313505) baseStart_313505 baseEnd_313505 := by
    simpa [prefixWord, tailWord_313505, baseEnd_313505] using wordTrace_append hprefix tailTrace_313505
  have hstable : (prefixWord ++ tailWord_313505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313505).length < 2 ^ (prefixWord ++ tailWord_313505).sum := by decide
  have hdescent : baseEnd_313505 < baseStart_313505 := by decide
  rcases family_descends (prefixWord ++ tailWord_313505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313535 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 4, 4]
def baseStart_313535 : Nat := 118140960795 + 313535 * 2 ^ 59
def prefixEnd_313535 : Nat := 4983230072969 + 3 ^ 40 * 313535 * 2
def baseEnd_313535 : Nat := 107329438005024017713723

theorem tailTrace_313535 : CollatzResearch.WordTrace tailWord_313535 prefixEnd_313535 107329438005024017713723 := by
  unfold tailWord_313535
  simp only [CollatzResearch.WordTrace]
  refine ⟨11435560919123717359974059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7623707279415811573316039 11435560919123717359974059)
  ·
    refine ⟨17153341378685576039961089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11435560919123717359974059 17153341378685576039961089)
    ·
      refine ⟨12865006034014182029970817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17153341378685576039961089 12865006034014182029970817)
      ·
        refine ⟨9648754525510636522478113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12865006034014182029970817 9648754525510636522478113)
        ·
          refine ⟨7236565894132977391858585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9648754525510636522478113 7236565894132977391858585)
          ·
            refine ⟨5427424420599733043893939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7236565894132977391858585 5427424420599733043893939)
            ·
              refine ⟨8141136630899599565840909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427424420599733043893939 8141136630899599565840909)
              ·
                refine ⟨3052926236587349837190341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8141136630899599565840909 3052926236587349837190341)
                ·
                  refine ⟨572423669360128094473189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3052926236587349837190341 572423669360128094473189)
                  ·
                    refine ⟨107329438005024017713723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 572423669360128094473189 107329438005024017713723)
                    ·
                      rfl

theorem cell22_313535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_313535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313535 prefixEnd_313535 := by exact prefixLift 313535
  have htrace : WordTrace (prefixWord ++ tailWord_313535) baseStart_313535 baseEnd_313535 := by
    simpa [prefixWord, tailWord_313535, baseEnd_313535] using wordTrace_append hprefix tailTrace_313535
  have hstable : (prefixWord ++ tailWord_313535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313535).length < 2 ^ (prefixWord ++ tailWord_313535).sum := by decide
  have hdescent : baseEnd_313535 < baseStart_313535 := by decide
  rcases family_descends (prefixWord ++ tailWord_313535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313554 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_313554 : Nat := 118140960795 + 313554 * 2 ^ 59
def prefixEnd_313554 : Nat := 4983230072969 + 3 ^ 40 * 313554 * 2
def baseEnd_313554 : Nat := 107335942093314301488665

theorem tailTrace_313554 : CollatzResearch.WordTrace tailWord_313554 prefixEnd_313554 107335942093314301488665 := by
  unfold tailWord_313554
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859063476513720901228929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7624169270703255736610477 2859063476513720901228929)
  ·
    refine ⟨2144297607385290675921697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2859063476513720901228929 2144297607385290675921697)
    ·
      refine ⟨1608223205538968006941273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2144297607385290675921697 1608223205538968006941273)
      ·
        refine ⟨1206167404154226005205955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1608223205538968006941273 1206167404154226005205955)
        ·
          refine ⟨1809251106231339007808933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206167404154226005205955 1809251106231339007808933)
          ·
            refine ⟨339234582418376063964175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1809251106231339007808933 339234582418376063964175)
            ·
              refine ⟨508851873627564095946263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339234582418376063964175 508851873627564095946263)
              ·
                refine ⟨763277810441346143919395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508851873627564095946263 763277810441346143919395)
                ·
                  refine ⟨1144916715662019215879093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763277810441346143919395 1144916715662019215879093)
                  ·
                    refine ⟨107335942093314301488665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1144916715662019215879093 107335942093314301488665)
                    ·
                      rfl

theorem cell22_313554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_313554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313554 prefixEnd_313554 := by exact prefixLift 313554
  have htrace : WordTrace (prefixWord ++ tailWord_313554) baseStart_313554 baseEnd_313554 := by
    simpa [prefixWord, tailWord_313554, baseEnd_313554] using wordTrace_append hprefix tailTrace_313554
  have hstable : (prefixWord ++ tailWord_313554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313554).length < 2 ^ (prefixWord ++ tailWord_313554).sum := by decide
  have hdescent : baseEnd_313554 < baseStart_313554 := by decide
  rcases family_descends (prefixWord ++ tailWord_313554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313612 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 5]
def baseStart_313612 : Nat := 118140960795 + 313612 * 2 ^ 59
def prefixEnd_313612 : Nat := 4983230072969 + 3 ^ 40 * 313612 * 2
def baseEnd_313612 : Nat := 35785265559540494512829

theorem tailTrace_313612 : CollatzResearch.WordTrace tailWord_313612 prefixEnd_313612 35785265559540494512829 := by
  unfold tailWord_313612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719184669922379755263545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7625579559896506340351393 5719184669922379755263545)
  ·
    refine ⟨4289388502441784816447659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5719184669922379755263545 4289388502441784816447659)
    ·
      refine ⟨6434082753662677224671489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4289388502441784816447659 6434082753662677224671489)
      ·
        refine ⟨4825562065247007918503617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6434082753662677224671489 4825562065247007918503617)
        ·
          refine ⟨3619171548935255938877713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4825562065247007918503617 3619171548935255938877713)
          ·
            refine ⟨2714378661701441954158285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619171548935255938877713 2714378661701441954158285)
            ·
              refine ⟨1017891998138040732809357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2714378661701441954158285 1017891998138040732809357)
              ·
                refine ⟨381709499301765274803509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1017891998138040732809357 381709499301765274803509)
                ·
                  refine ⟨35785265559540494512829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 381709499301765274803509 35785265559540494512829)
                  ·
                    rfl

theorem cell22_313612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_313612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313612 prefixEnd_313612 := by exact prefixLift 313612
  have htrace : WordTrace (prefixWord ++ tailWord_313612) baseStart_313612 baseEnd_313612 := by
    simpa [prefixWord, tailWord_313612, baseEnd_313612] using wordTrace_append hprefix tailTrace_313612
  have hstable : (prefixWord ++ tailWord_313612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313612).length < 2 ^ (prefixWord ++ tailWord_313612).sum := by decide
  have hdescent : baseEnd_313612 < baseStart_313612 := by decide
  rcases family_descends (prefixWord ++ tailWord_313612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313650 : List Nat := [3, 2, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_313650 : Nat := 118140960795 + 313650 * 2 ^ 59
def prefixEnd_313650 : Nat := 4983230072969 + 3 ^ 40 * 313650 * 2
def baseEnd_313650 : Nat := 107368804855202051088371

theorem tailTrace_313650 : CollatzResearch.WordTrace tailWord_313650 prefixEnd_313650 107368804855202051088371 := by
  unfold tailWord_313650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859938828426773000102601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7626503542471394666940269 2859938828426773000102601)
  ·
    refine ⟨2144954121320079750076951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2859938828426773000102601 2144954121320079750076951)
    ·
      refine ⟨3217431181980119625115427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144954121320079750076951 3217431181980119625115427)
      ·
        refine ⟨4826146772970179437673141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217431181980119625115427 4826146772970179437673141)
        ·
          refine ⟨452451259965954322281857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4826146772970179437673141 452451259965954322281857)
          ·
            refine ⟨339338444974465741711393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452451259965954322281857 339338444974465741711393)
            ·
              refine ⟨254503833730849306283545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339338444974465741711393 254503833730849306283545)
              ·
                refine ⟨190877875298136979712659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254503833730849306283545 190877875298136979712659)
                ·
                  refine ⟨286316812947205469568989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190877875298136979712659 286316812947205469568989)
                  ·
                    refine ⟨107368804855202051088371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286316812947205469568989 107368804855202051088371)
                    ·
                      rfl

theorem cell22_313650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_313650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313650 prefixEnd_313650 := by exact prefixLift 313650
  have htrace : WordTrace (prefixWord ++ tailWord_313650) baseStart_313650 baseEnd_313650 := by
    simpa [prefixWord, tailWord_313650, baseEnd_313650] using wordTrace_append hprefix tailTrace_313650
  have hstable : (prefixWord ++ tailWord_313650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313650).length < 2 ^ (prefixWord ++ tailWord_313650).sum := by decide
  have hdescent : baseEnd_313650 < baseStart_313650 := by decide
  rcases family_descends (prefixWord ++ tailWord_313650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313672 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_313672 : Nat := 118140960795 + 313672 * 2 ^ 59
def prefixEnd_313672 : Nat := 4983230072969 + 3 ^ 40 * 313672 * 2
def baseEnd_313672 : Nat := 107376335904801327038303

theorem tailTrace_313672 : CollatzResearch.WordTrace tailWord_313672 prefixEnd_313672 107376335904801327038303 := by
  unfold tailWord_313672
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720278859813694878855635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7627038479751593171807513 5720278859813694878855635)
  ·
    refine ⟨8580418289720542318283453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5720278859813694878855635 8580418289720542318283453)
    ·
      refine ⟨3217656858645203369356295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8580418289720542318283453 3217656858645203369356295)
      ·
        refine ⟨4826485287967805054034443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217656858645203369356295 4826485287967805054034443)
        ·
          refine ⟨7239727931951707581051665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826485287967805054034443 7239727931951707581051665)
          ·
            refine ⟨5429795948963780685788749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239727931951707581051665 5429795948963780685788749)
            ·
              refine ⟨2036173480861417757170781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5429795948963780685788749 2036173480861417757170781)
              ·
                refine ⟨763565055323031658939043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036173480861417757170781 763565055323031658939043)
                ·
                  refine ⟨1145347582984547488408565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763565055323031658939043 1145347582984547488408565)
                  ·
                    refine ⟨107376335904801327038303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1145347582984547488408565 107376335904801327038303)
                    ·
                      rfl

theorem cell22_313672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_313672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313672 prefixEnd_313672 := by exact prefixLift 313672
  have htrace : WordTrace (prefixWord ++ tailWord_313672) baseStart_313672 baseEnd_313672 := by
    simpa [prefixWord, tailWord_313672, baseEnd_313672] using wordTrace_append hprefix tailTrace_313672
  have hstable : (prefixWord ++ tailWord_313672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313672).length < 2 ^ (prefixWord ++ tailWord_313672).sum := by decide
  have hdescent : baseEnd_313672 < baseStart_313672 := by decide
  rcases family_descends (prefixWord ++ tailWord_313672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313687 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 1, 6]
def baseStart_313687 : Nat := 118140960795 + 313687 * 2 ^ 59
def prefixEnd_313687 : Nat := 4983230072969 + 3 ^ 40 * 313687 * 2
def baseEnd_313687 : Nat := 107381470711346287913257

theorem tailTrace_313687 : CollatzResearch.WordTrace tailWord_313687 prefixEnd_313687 107381470711346287913257 := by
  unfold tailWord_313687
  simp only [CollatzResearch.WordTrace]
  refine ⟨11441104814573047319507315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7627403209715364879671543 11441104814573047319507315)
  ·
    refine ⟨17161657221859570979260973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11441104814573047319507315 17161657221859570979260973)
    ·
      refine ⟨6435621458197339117222865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17161657221859570979260973 6435621458197339117222865)
      ·
        refine ⟨4826716093648004337917149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6435621458197339117222865 4826716093648004337917149)
        ·
          refine ⟨1810018535118001626718931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4826716093648004337917149 1810018535118001626718931)
          ·
            refine ⟨2715027802677002440078397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810018535118001626718931 2715027802677002440078397)
            ·
              refine ⟨1018135426003875915029399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2715027802677002440078397 1018135426003875915029399)
              ·
                refine ⟨1527203139005813872544099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018135426003875915029399 1527203139005813872544099)
                ·
                  refine ⟨2290804708508720808816149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527203139005813872544099 2290804708508720808816149)
                  ·
                    refine ⟨107381470711346287913257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2290804708508720808816149 107381470711346287913257)
                    ·
                      rfl

theorem cell22_313687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_313687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_313687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_313687 prefixEnd_313687 := by exact prefixLift 313687
  have htrace : WordTrace (prefixWord ++ tailWord_313687) baseStart_313687 baseEnd_313687 := by
    simpa [prefixWord, tailWord_313687, baseEnd_313687] using wordTrace_append hprefix tailTrace_313687
  have hstable : (prefixWord ++ tailWord_313687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313687).length < 2 ^ (prefixWord ++ tailWord_313687).sum := by decide
  have hdescent : baseEnd_313687 < baseStart_313687 := by decide
  rcases family_descends (prefixWord ++ tailWord_313687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
