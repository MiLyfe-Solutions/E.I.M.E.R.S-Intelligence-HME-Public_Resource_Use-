import V185TrunkScan20Chunk169

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_1035276 : List Nat := [2, 2, 1, 2, 3, 4, 2, 2, 2]
def baseStart_1035276 : Nat := 118140960795 + 1035276 * 2 ^ 59
def prefixEnd_1035276 : Nat := 4983230072969 + 3 ^ 40 * 1035276 * 2
def baseEnd_1035276 : Nat := 472528176057063743634541

theorem tailTrace_1035276 : CollatzResearch.WordTrace tailWord_1035276 prefixEnd_1035276 472528176057063743634541 := by
  unfold tailWord_1035276
  simp only [CollatzResearch.WordTrace]
  refine ⟨18879808898689668954630841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25173078531586225272841121 18879808898689668954630841)
  ·
    refine ⟨14159856674017251715973131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18879808898689668954630841 14159856674017251715973131)
    ·
      refine ⟨21239785011025877573959697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14159856674017251715973131 21239785011025877573959697)
      ·
        refine ⟨15929838758269408180469773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21239785011025877573959697 15929838758269408180469773)
        ·
          refine ⟨5973689534351028067676165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15929838758269408180469773 5973689534351028067676165)
          ·
            refine ⟨1120066787690817762689281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5973689534351028067676165 1120066787690817762689281)
            ·
              refine ⟨840050090768113322016961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120066787690817762689281 840050090768113322016961)
              ·
                refine ⟨630037568076084991512721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840050090768113322016961 630037568076084991512721)
                ·
                  refine ⟨472528176057063743634541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630037568076084991512721 472528176057063743634541)
                  ·
                    rfl

theorem cell20_1035276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_1035276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035276 prefixEnd_1035276 := by exact prefixLift 1035276
  have htrace : WordTrace (prefixWord ++ tailWord_1035276) baseStart_1035276 baseEnd_1035276 := by
    simpa [prefixWord, tailWord_1035276, baseEnd_1035276] using wordTrace_append hprefix tailTrace_1035276
  have hstable : (prefixWord ++ tailWord_1035276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035276).length < 2 ^ (prefixWord ++ tailWord_1035276).sum := by decide
  have hdescent : baseEnd_1035276 < baseStart_1035276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035287 : List Nat := [1, 1, 3, 5, 1, 1, 3, 5]
def baseStart_1035287 : Nat := 118140960795 + 1035287 * 2 ^ 59
def prefixEnd_1035287 : Nat := 4983230072969 + 3 ^ 40 * 1035287 * 2
def baseEnd_1035287 : Nat := 157511065585598864755943

theorem tailTrace_1035287 : CollatzResearch.WordTrace tailWord_1035287 prefixEnd_1035287 157511065585598864755943 := by
  unfold tailWord_1035287
  simp only [CollatzResearch.WordTrace]
  refine ⟨37760019000339486787912115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25173346000226324525274743 37760019000339486787912115)
  ·
    refine ⟨56640028500509230181868173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37760019000339486787912115 56640028500509230181868173)
    ·
      refine ⟨21240010687690961318200565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56640028500509230181868173 21240010687690961318200565)
      ·
        refine ⟨1991251001971027623581303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21240010687690961318200565 1991251001971027623581303)
        ·
          refine ⟨2986876502956541435371955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991251001971027623581303 2986876502956541435371955)
          ·
            refine ⟨4480314754434812153057933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986876502956541435371955 4480314754434812153057933)
            ·
              refine ⟨1680118032913054557396725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4480314754434812153057933 1680118032913054557396725)
              ·
                refine ⟨157511065585598864755943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1680118032913054557396725 157511065585598864755943)
                ·
                  rfl

theorem cell20_1035287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 5].length) (baseStart_1035287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035287 prefixEnd_1035287 := by exact prefixLift 1035287
  have htrace : WordTrace (prefixWord ++ tailWord_1035287) baseStart_1035287 baseEnd_1035287 := by
    simpa [prefixWord, tailWord_1035287, baseEnd_1035287] using wordTrace_append hprefix tailTrace_1035287
  have hstable : (prefixWord ++ tailWord_1035287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035287).length < 2 ^ (prefixWord ++ tailWord_1035287).sum := by decide
  have hdescent : baseEnd_1035287 < baseStart_1035287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035301 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_1035301 : Nat := 118140960795 + 1035301 * 2 ^ 59
def prefixEnd_1035301 : Nat := 4983230072969 + 3 ^ 40 * 1035301 * 2
def baseEnd_1035301 : Nat := 472539586738274767801105

theorem tailTrace_1035301 : CollatzResearch.WordTrace tailWord_1035301 prefixEnd_1035301 472539586738274767801105 := by
  unfold tailWord_1035301
  simp only [CollatzResearch.WordTrace]
  refine ⟨37760529622288767178921757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25173686414859178119281171 37760529622288767178921757)
  ·
    refine ⟨14160198608358287692095659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37760529622288767178921757 14160198608358287692095659)
    ·
      refine ⟨21240297912537431538143489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14160198608358287692095659 21240297912537431538143489)
      ·
        refine ⟨15930223434403073653607617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21240297912537431538143489 15930223434403073653607617)
        ·
          refine ⟨11947667575802305240205713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15930223434403073653607617 11947667575802305240205713)
          ·
            refine ⟨8960750681851728930154285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11947667575802305240205713 8960750681851728930154285)
            ·
              refine ⟨3360281505694398348807857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8960750681851728930154285 3360281505694398348807857)
              ·
                refine ⟨2520211129270798761605893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360281505694398348807857 2520211129270798761605893)
                ·
                  refine ⟨472539586738274767801105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520211129270798761605893 472539586738274767801105)
                  ·
                    rfl

theorem cell20_1035301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_1035301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035301 prefixEnd_1035301 := by exact prefixLift 1035301
  have htrace : WordTrace (prefixWord ++ tailWord_1035301) baseStart_1035301 baseEnd_1035301 := by
    simpa [prefixWord, tailWord_1035301, baseEnd_1035301] using wordTrace_append hprefix tailTrace_1035301
  have hstable : (prefixWord ++ tailWord_1035301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035301).length < 2 ^ (prefixWord ++ tailWord_1035301).sum := by decide
  have hdescent : baseEnd_1035301 < baseStart_1035301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035315 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_1035315 : Nat := 118140960795 + 1035315 * 2 ^ 59
def prefixEnd_1035315 : Nat := 4983230072969 + 3 ^ 40 * 1035315 * 2
def baseEnd_1035315 : Nat := 472545976719752941334381

theorem tailTrace_1035315 : CollatzResearch.WordTrace tailWord_1035315 prefixEnd_1035315 472545976719752941334381 := by
  unfold tailWord_1035315
  simp only [CollatzResearch.WordTrace]
  refine ⟨37761040244238047569931399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25174026829492031713287599 37761040244238047569931399)
  ·
    refine ⟨56641560366357071354897099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37761040244238047569931399 56641560366357071354897099)
    ·
      refine ⟨84962340549535607032345649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56641560366357071354897099 84962340549535607032345649)
      ·
        refine ⟨63721755412151705274259237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84962340549535607032345649 63721755412151705274259237)
        ·
          refine ⟨11947829139778444738923607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63721755412151705274259237 11947829139778444738923607)
          ·
            refine ⟨17921743709667667108385411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11947829139778444738923607 17921743709667667108385411)
            ·
              refine ⟨26882615564501500662578117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17921743709667667108385411 26882615564501500662578117)
              ·
                refine ⟨5040490418344031374233397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26882615564501500662578117 5040490418344031374233397)
                ·
                  refine ⟨472545976719752941334381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040490418344031374233397 472545976719752941334381)
                  ·
                    rfl

theorem cell20_1035315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_1035315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035315 prefixEnd_1035315 := by exact prefixLift 1035315
  have htrace : WordTrace (prefixWord ++ tailWord_1035315) baseStart_1035315 baseEnd_1035315 := by
    simpa [prefixWord, tailWord_1035315, baseEnd_1035315] using wordTrace_append hprefix tailTrace_1035315
  have hstable : (prefixWord ++ tailWord_1035315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035315).length < 2 ^ (prefixWord ++ tailWord_1035315).sum := by decide
  have hdescent : baseEnd_1035315 < baseStart_1035315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035349 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 3]
def baseStart_1035349 : Nat := 118140960795 + 1035349 * 2 ^ 59
def prefixEnd_1035349 : Nat := 4983230072969 + 3 ^ 40 * 1035349 * 2
def baseEnd_1035349 : Nat := 472561495246199934200909

theorem tailTrace_1035349 : CollatzResearch.WordTrace tailWord_1035349 prefixEnd_1035349 472561495246199934200909 := by
  unfold tailWord_1035349
  simp only [CollatzResearch.WordTrace]
  refine ⟨37762280326114871376669101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25174853550743247584446067 37762280326114871376669101)
  ·
    refine ⟨14160855122293076766250913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37762280326114871376669101 14160855122293076766250913)
    ·
      refine ⟨10620641341719807574688185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14160855122293076766250913 10620641341719807574688185)
      ·
        refine ⟨7965481006289855681016139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10620641341719807574688185 7965481006289855681016139)
        ·
          refine ⟨11948221509434783521524209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7965481006289855681016139 11948221509434783521524209)
          ·
            refine ⟨8961166132076087641143157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11948221509434783521524209 8961166132076087641143157)
            ·
              refine ⟨840109324882133216357171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8961166132076087641143157 840109324882133216357171)
              ·
                refine ⟨1260163987323199824535757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840109324882133216357171 1260163987323199824535757)
                ·
                  refine ⟨472561495246199934200909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260163987323199824535757 472561495246199934200909)
                  ·
                    rfl

theorem cell20_1035349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_1035349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035349 prefixEnd_1035349 := by exact prefixLift 1035349
  have htrace : WordTrace (prefixWord ++ tailWord_1035349) baseStart_1035349 baseEnd_1035349 := by
    simpa [prefixWord, tailWord_1035349, baseEnd_1035349] using wordTrace_append hprefix tailTrace_1035349
  have hstable : (prefixWord ++ tailWord_1035349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035349).length < 2 ^ (prefixWord ++ tailWord_1035349).sum := by decide
  have hdescent : baseEnd_1035349 < baseStart_1035349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035370 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1035370 : Nat := 118140960795 + 1035370 * 2 ^ 59
def prefixEnd_1035370 : Nat := 4983230072969 + 3 ^ 40 * 1035370 * 2
def baseEnd_1035370 : Nat := 472571080218417194500823

theorem tailTrace_1035370 : CollatzResearch.WordTrace tailWord_1035370 prefixEnd_1035370 472571080218417194500823 := by
  unfold tailWord_1035370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9440761564759697990795891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25175364172692527975455709 9440761564759697990795891)
  ·
    refine ⟨14161142347139546986193837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9440761564759697990795891 14161142347139546986193837)
    ·
      refine ⟨5310428380177330119822689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14161142347139546986193837 5310428380177330119822689)
      ·
        refine ⟨3982821285132997589867017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5310428380177330119822689 3982821285132997589867017)
        ·
          refine ⟨2987115963849748192400263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3982821285132997589867017 2987115963849748192400263)
          ·
            refine ⟨4480673945774622288600395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987115963849748192400263 4480673945774622288600395)
            ·
              refine ⟨6721010918661933432900593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480673945774622288600395 6721010918661933432900593)
              ·
                refine ⟨5040758188996450074675445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6721010918661933432900593 5040758188996450074675445)
                ·
                  refine ⟨472571080218417194500823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040758188996450074675445 472571080218417194500823)
                  ·
                    rfl

theorem cell20_1035370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1035370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035370 prefixEnd_1035370 := by exact prefixLift 1035370
  have htrace : WordTrace (prefixWord ++ tailWord_1035370) baseStart_1035370 baseEnd_1035370 := by
    simpa [prefixWord, tailWord_1035370, baseEnd_1035370] using wordTrace_append hprefix tailTrace_1035370
  have hstable : (prefixWord ++ tailWord_1035370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035370).length < 2 ^ (prefixWord ++ tailWord_1035370).sum := by decide
  have hdescent : baseEnd_1035370 < baseStart_1035370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035373 : List Nat := [1, 5, 1, 1, 2, 2, 3, 3, 2]
def baseStart_1035373 : Nat := 118140960795 + 1035373 * 2 ^ 59
def prefixEnd_1035373 : Nat := 4983230072969 + 3 ^ 40 * 1035373 * 2
def baseEnd_1035373 : Nat := 472572449500162517400811

theorem tailTrace_1035373 : CollatzResearch.WordTrace tailWord_1035373 prefixEnd_1035373 472572449500162517400811 := by
  unfold tailWord_1035373
  simp only [CollatzResearch.WordTrace]
  refine ⟨37763155678027923475542773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25175437118685282317028515 37763155678027923475542773)
  ·
    refine ⟨3540295844815117825832135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37763155678027923475542773 3540295844815117825832135)
    ·
      refine ⟨5310443767222676738748203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3540295844815117825832135 5310443767222676738748203)
      ·
        refine ⟨7965665650834015108122305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5310443767222676738748203 7965665650834015108122305)
        ·
          refine ⟨5974249238125511331091729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7965665650834015108122305 5974249238125511331091729)
          ·
            refine ⟨4480686928594133498318797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5974249238125511331091729 4480686928594133498318797)
            ·
              refine ⟨1680257598222800061869549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4480686928594133498318797 1680257598222800061869549)
              ·
                refine ⟨630096599333550023201081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1680257598222800061869549 630096599333550023201081)
                ·
                  refine ⟨472572449500162517400811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630096599333550023201081 472572449500162517400811)
                  ·
                    rfl

theorem cell20_1035373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_1035373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035373 prefixEnd_1035373 := by exact prefixLift 1035373
  have htrace : WordTrace (prefixWord ++ tailWord_1035373) baseStart_1035373 baseEnd_1035373 := by
    simpa [prefixWord, tailWord_1035373, baseEnd_1035373] using wordTrace_append hprefix tailTrace_1035373
  have hstable : (prefixWord ++ tailWord_1035373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035373).length < 2 ^ (prefixWord ++ tailWord_1035373).sum := by decide
  have hdescent : baseEnd_1035373 < baseStart_1035373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035436 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_1035436 : Nat := 118140960795 + 1035436 * 2 ^ 59
def prefixEnd_1035436 : Nat := 4983230072969 + 3 ^ 40 * 1035436 * 2
def baseEnd_1035436 : Nat := 472601204416814298300553

theorem tailTrace_1035436 : CollatzResearch.WordTrace tailWord_1035436 prefixEnd_1035436 472601204416814298300553 := by
  unfold tailWord_1035436
  simp only [CollatzResearch.WordTrace]
  refine ⟨18882726738399842617543081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25176968984533123490057441 18882726738399842617543081)
  ·
    refine ⟨14162045053799881963157311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18882726738399842617543081 14162045053799881963157311)
    ·
      refine ⟨21243067580699822944735967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14162045053799881963157311 21243067580699822944735967)
      ·
        refine ⟨31864601371049734417103951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21243067580699822944735967 31864601371049734417103951)
        ·
          refine ⟨47796902056574601625655927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31864601371049734417103951 47796902056574601625655927)
          ·
            refine ⟨71695353084861902438483891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47796902056574601625655927 71695353084861902438483891)
            ·
              refine ⟨107543029627292853657725837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71695353084861902438483891 107543029627292853657725837)
              ·
                refine ⟨40328636110234820121647189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107543029627292853657725837 40328636110234820121647189)
                ·
                  refine ⟨472601204416814298300553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40328636110234820121647189 472601204416814298300553)
                  ·
                    rfl

theorem cell20_1035436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_1035436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035436 prefixEnd_1035436 := by exact prefixLift 1035436
  have htrace : WordTrace (prefixWord ++ tailWord_1035436) baseStart_1035436 baseEnd_1035436 := by
    simpa [prefixWord, tailWord_1035436, baseEnd_1035436] using wordTrace_append hprefix tailTrace_1035436
  have hstable : (prefixWord ++ tailWord_1035436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035436).length < 2 ^ (prefixWord ++ tailWord_1035436).sum := by decide
  have hdescent : baseEnd_1035436 < baseStart_1035436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035449 : List Nat := [1, 2, 1, 4, 1, 3, 4, 2, 2]
def baseStart_1035449 : Nat := 118140960795 + 1035449 * 2 ^ 59
def prefixEnd_1035449 : Nat := 4983230072969 + 3 ^ 40 * 1035449 * 2
def baseEnd_1035449 : Nat := 472607137971044030867167

theorem tailTrace_1035449 : CollatzResearch.WordTrace tailWord_1035449 prefixEnd_1035449 472607137971044030867167 := by
  unfold tailWord_1035449
  simp only [CollatzResearch.WordTrace]
  refine ⟨37765927625752588455309401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25177285083835058970206267 37765927625752588455309401)
  ·
    refine ⟨28324445719314441341482051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37765927625752588455309401 28324445719314441341482051)
    ·
      refine ⟨42486668578971662012223077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28324445719314441341482051 42486668578971662012223077)
      ·
        refine ⟨7966250358557186627291827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42486668578971662012223077 7966250358557186627291827)
        ·
          refine ⟨11949375537835779940937741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966250358557186627291827 11949375537835779940937741)
          ·
            refine ⟨4481015826688417477851653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11949375537835779940937741 4481015826688417477851653)
            ·
              refine ⟨840190467504078277097185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4481015826688417477851653 840190467504078277097185)
              ·
                refine ⟨630142850628058707822889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840190467504078277097185 630142850628058707822889)
                ·
                  refine ⟨472607137971044030867167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630142850628058707822889 472607137971044030867167)
                  ·
                    rfl

theorem cell20_1035449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_1035449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035449 prefixEnd_1035449 := by exact prefixLift 1035449
  have htrace : WordTrace (prefixWord ++ tailWord_1035449) baseStart_1035449 baseEnd_1035449 := by
    simpa [prefixWord, tailWord_1035449, baseEnd_1035449] using wordTrace_append hprefix tailTrace_1035449
  have hstable : (prefixWord ++ tailWord_1035449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035449).length < 2 ^ (prefixWord ++ tailWord_1035449).sum := by decide
  have hdescent : baseEnd_1035449 < baseStart_1035449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035456 : List Nat := [2, 1, 1, 2, 7, 1, 1, 5]
def baseStart_1035456 : Nat := 118140960795 + 1035456 * 2 ^ 59
def prefixEnd_1035456 : Nat := 4983230072969 + 3 ^ 40 * 1035456 * 2
def baseEnd_1035456 : Nat := 157536777653927705877935

theorem tailTrace_1035456 : CollatzResearch.WordTrace tailWord_1035456 prefixEnd_1035456 157536777653927705877935 := by
  unfold tailWord_1035456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18883091468363614325407111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25177455291151485767209481 18883091468363614325407111)
  ·
    refine ⟨28324637202545421488110667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18883091468363614325407111 28324637202545421488110667)
    ·
      refine ⟨42486955803818132232166001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28324637202545421488110667 42486955803818132232166001)
      ·
        refine ⟨31865216852863599174124501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42486955803818132232166001 31865216852863599174124501)
        ·
          refine ⟨746841019988990605643543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31865216852863599174124501 746841019988990605643543)
          ·
            refine ⟨1120261529983485908465315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746841019988990605643543 1120261529983485908465315)
            ·
              refine ⟨1680392294975228862697973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120261529983485908465315 1680392294975228862697973)
              ·
                refine ⟨157536777653927705877935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1680392294975228862697973 157536777653927705877935)
                ·
                  rfl

theorem cell20_1035456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_1035456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035456 prefixEnd_1035456 := by exact prefixLift 1035456
  have htrace : WordTrace (prefixWord ++ tailWord_1035456) baseStart_1035456 baseEnd_1035456 := by
    simpa [prefixWord, tailWord_1035456, baseEnd_1035456] using wordTrace_append hprefix tailTrace_1035456
  have hstable : (prefixWord ++ tailWord_1035456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035456).length < 2 ^ (prefixWord ++ tailWord_1035456).sum := by decide
  have hdescent : baseEnd_1035456 < baseStart_1035456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035470 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1035470 : Nat := 118140960795 + 1035470 * 2 ^ 59
def prefixEnd_1035470 : Nat := 4983230072969 + 3 ^ 40 * 1035470 * 2
def baseEnd_1035470 : Nat := 472616722943261291167081

theorem tailTrace_1035470 : CollatzResearch.WordTrace tailWord_1035470 prefixEnd_1035470 472616722943261291167081 := by
  unfold tailWord_1035470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4720836694834563630227983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25177795705784339361215909 4720836694834563630227983)
  ·
    refine ⟨7081255042251845445341975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4720836694834563630227983 7081255042251845445341975)
    ·
      refine ⟨10621882563377768168012963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7081255042251845445341975 10621882563377768168012963)
      ·
        refine ⟨15932823845066652252019445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10621882563377768168012963 15932823845066652252019445)
        ·
          refine ⟨1493702235474998648626823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15932823845066652252019445 1493702235474998648626823)
          ·
            refine ⟨2240553353212497972940235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493702235474998648626823 2240553353212497972940235)
            ·
              refine ⟨3360830029818746959410353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240553353212497972940235 3360830029818746959410353)
              ·
                refine ⟨2520622522364060219557765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3360830029818746959410353 2520622522364060219557765)
                ·
                  refine ⟨472616722943261291167081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520622522364060219557765 472616722943261291167081)
                  ·
                    rfl

theorem cell20_1035470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1035470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035470 prefixEnd_1035470 := by exact prefixLift 1035470
  have htrace : WordTrace (prefixWord ++ tailWord_1035470) baseStart_1035470 baseEnd_1035470 := by
    simpa [prefixWord, tailWord_1035470, baseEnd_1035470] using wordTrace_append hprefix tailTrace_1035470
  have hstable : (prefixWord ++ tailWord_1035470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035470).length < 2 ^ (prefixWord ++ tailWord_1035470).sum := by decide
  have hdescent : baseEnd_1035470 < baseStart_1035470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035498 : List Nat := [3, 1, 3, 1, 1, 4, 7]
def baseStart_1035498 : Nat := 118140960795 + 1035498 * 2 ^ 59
def prefixEnd_1035498 : Nat := 4983230072969 + 3 ^ 40 * 1035498 * 2
def baseEnd_1035498 : Nat := 52514389211801959803737

theorem tailTrace_1035498 : CollatzResearch.WordTrace tailWord_1035498 prefixEnd_1035498 52514389211801959803737 := by
  unfold tailWord_1035498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9441928700643767455960787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25178476535050046549228765 9441928700643767455960787)
  ·
    refine ⟨14162893050965651183941181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9441928700643767455960787 14162893050965651183941181)
    ·
      refine ⟨5311084894112119193977943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14162893050965651183941181 5311084894112119193977943)
      ·
        refine ⟨7966627341168178790966915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5311084894112119193977943 7966627341168178790966915)
        ·
          refine ⟨11949941011752268186450373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7966627341168178790966915 11949941011752268186450373)
          ·
            refine ⟨2240613939703550284959445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11949941011752268186450373 2240613939703550284959445)
            ·
              refine ⟨52514389211801959803737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2240613939703550284959445 52514389211801959803737)
              ·
                rfl

theorem cell20_1035498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 7].length) (baseStart_1035498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035498 prefixEnd_1035498 := by exact prefixLift 1035498
  have htrace : WordTrace (prefixWord ++ tailWord_1035498) baseStart_1035498 baseEnd_1035498 := by
    simpa [prefixWord, tailWord_1035498, baseEnd_1035498] using wordTrace_append hprefix tailTrace_1035498
  have hstable : (prefixWord ++ tailWord_1035498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035498).length < 2 ^ (prefixWord ++ tailWord_1035498).sum := by decide
  have hdescent : baseEnd_1035498 < baseStart_1035498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035501 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1035501 : Nat := 118140960795 + 1035501 * 2 ^ 59
def prefixEnd_1035501 : Nat := 4983230072969 + 3 ^ 40 * 1035501 * 2
def baseEnd_1035501 : Nat := 472630872187962961133621

theorem tailTrace_1035501 : CollatzResearch.WordTrace tailWord_1035501 prefixEnd_1035501 472630872187962961133621 := by
  unfold tailWord_1035501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37767824221564201336202357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25178549481042800890801571 37767824221564201336202357)
  ·
    refine ⟨3540733520771643875268971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37767824221564201336202357 3540733520771643875268971)
    ·
      refine ⟨5311100281157465812903457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3540733520771643875268971 5311100281157465812903457)
      ·
        refine ⟨3983325210868099359677593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5311100281157465812903457 3983325210868099359677593)
        ·
          refine ⟨2987493908151074519758195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3983325210868099359677593 2987493908151074519758195)
          ·
            refine ⟨4481240862226611779637293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987493908151074519758195 4481240862226611779637293)
            ·
              refine ⟨1680465323334979417363985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4481240862226611779637293 1680465323334979417363985)
              ·
                refine ⟨1260348992501234563022989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1680465323334979417363985 1260348992501234563022989)
                ·
                  refine ⟨472630872187962961133621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260348992501234563022989 472630872187962961133621)
                  ·
                    rfl

theorem cell20_1035501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1035501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035501 prefixEnd_1035501 := by exact prefixLift 1035501
  have htrace : WordTrace (prefixWord ++ tailWord_1035501) baseStart_1035501 baseEnd_1035501 := by
    simpa [prefixWord, tailWord_1035501, baseEnd_1035501] using wordTrace_append hprefix tailTrace_1035501
  have hstable : (prefixWord ++ tailWord_1035501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035501).length < 2 ^ (prefixWord ++ tailWord_1035501).sum := by decide
  have hdescent : baseEnd_1035501 < baseStart_1035501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035518 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_1035518 : Nat := 118140960795 + 1035518 * 2 ^ 59
def prefixEnd_1035518 : Nat := 4983230072969 + 3 ^ 40 * 1035518 * 2
def baseEnd_1035518 : Nat := 472638631451186457566885

theorem tailTrace_1035518 : CollatzResearch.WordTrace tailWord_1035518 prefixEnd_1035518 472638631451186457566885 := by
  unfold tailWord_1035518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721055532812826654946401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25178962841668408826380805 4721055532812826654946401)
  ·
    refine ⟨3540791649609619991209801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4721055532812826654946401 3540791649609619991209801)
    ·
      refine ⟨2655593737207214993407351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3540791649609619991209801 2655593737207214993407351)
      ·
        refine ⟨3983390605810822490111027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655593737207214993407351 3983390605810822490111027)
        ·
          refine ⟨5975085908716233735166541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983390605810822490111027 5975085908716233735166541)
          ·
            refine ⟨2240657215768587650687453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5975085908716233735166541 2240657215768587650687453)
            ·
              refine ⟨840246455913220369007795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2240657215768587650687453 840246455913220369007795)
              ·
                refine ⟨1260369683869830553511693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840246455913220369007795 1260369683869830553511693)
                ·
                  refine ⟨472638631451186457566885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260369683869830553511693 472638631451186457566885)
                  ·
                    rfl

theorem cell20_1035518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_1035518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035518 prefixEnd_1035518 := by exact prefixLift 1035518
  have htrace : WordTrace (prefixWord ++ tailWord_1035518) baseStart_1035518 baseEnd_1035518 := by
    simpa [prefixWord, tailWord_1035518, baseEnd_1035518] using wordTrace_append hprefix tailTrace_1035518
  have hstable : (prefixWord ++ tailWord_1035518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035518).length < 2 ^ (prefixWord ++ tailWord_1035518).sum := by decide
  have hdescent : baseEnd_1035518 < baseStart_1035518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035538 : List Nat := [3, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_1035538 : Nat := 118140960795 + 1035538 * 2 ^ 59
def prefixEnd_1035538 : Nat := 4983230072969 + 3 ^ 40 * 1035538 * 2
def baseEnd_1035538 : Nat := 472647759996155276900137

theorem tailTrace_1035538 : CollatzResearch.WordTrace tailWord_1035538 prefixEnd_1035538 472647759996155276900137 := by
  unfold tailWord_1035538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9442293430607539163824817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25179449148286771103532845 9442293430607539163824817)
  ·
    refine ⟨7081720072955654372868613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9442293430607539163824817 7081720072955654372868613)
    ·
      refine ⟨1327822513679185194912865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7081720072955654372868613 1327822513679185194912865)
      ·
        refine ⟨995866885259388896184649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1327822513679185194912865 995866885259388896184649)
        ·
          refine ⟨746900163944541672138487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 995866885259388896184649 746900163944541672138487)
          ·
            refine ⟨1120350245916812508207731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746900163944541672138487 1120350245916812508207731)
            ·
              refine ⟨1680525368875218762311597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120350245916812508207731 1680525368875218762311597)
              ·
                refine ⟨630197013328207035866849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1680525368875218762311597 630197013328207035866849)
                ·
                  refine ⟨472647759996155276900137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630197013328207035866849 472647759996155276900137)
                  ·
                    rfl

theorem cell20_1035538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_1035538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035538 prefixEnd_1035538 := by exact prefixLift 1035538
  have htrace : WordTrace (prefixWord ++ tailWord_1035538) baseStart_1035538 baseEnd_1035538 := by
    simpa [prefixWord, tailWord_1035538, baseEnd_1035538] using wordTrace_append hprefix tailTrace_1035538
  have hstable : (prefixWord ++ tailWord_1035538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035538).length < 2 ^ (prefixWord ++ tailWord_1035538).sum := by decide
  have hdescent : baseEnd_1035538 < baseStart_1035538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035543 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_1035543 : Nat := 118140960795 + 1035543 * 2 ^ 59
def prefixEnd_1035543 : Nat := 4983230072969 + 3 ^ 40 * 1035543 * 2
def baseEnd_1035543 : Nat := 472650042132397481733449

theorem tailTrace_1035543 : CollatzResearch.WordTrace tailWord_1035543 prefixEnd_1035543 472650042132397481733449 := by
  unfold tailWord_1035543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37769356087412042509231283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25179570724941361672820855 37769356087412042509231283)
  ·
    refine ⟨56654034131118063763846925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37769356087412042509231283 56654034131118063763846925)
    ·
      refine ⟨21245262799169273911442597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56654034131118063763846925 21245262799169273911442597)
      ·
        refine ⟨3983486774844238858395487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21245262799169273911442597 3983486774844238858395487)
        ·
          refine ⟨5975230162266358287593231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3983486774844238858395487 5975230162266358287593231)
          ·
            refine ⟨8962845243399537431389847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5975230162266358287593231 8962845243399537431389847)
            ·
              refine ⟨13444267865099306147084771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8962845243399537431389847 13444267865099306147084771)
              ·
                refine ⟨20166401797648959220627157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13444267865099306147084771 20166401797648959220627157)
                ·
                  refine ⟨472650042132397481733449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20166401797648959220627157 472650042132397481733449)
                  ·
                    rfl

theorem cell20_1035543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_1035543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035543 prefixEnd_1035543 := by exact prefixLift 1035543
  have htrace : WordTrace (prefixWord ++ tailWord_1035543) baseStart_1035543 baseEnd_1035543 := by
    simpa [prefixWord, tailWord_1035543, baseEnd_1035543] using wordTrace_append hprefix tailTrace_1035543
  have hstable : (prefixWord ++ tailWord_1035543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035543).length < 2 ^ (prefixWord ++ tailWord_1035543).sum := by decide
  have hdescent : baseEnd_1035543 < baseStart_1035543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035560 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1035560 : Nat := 118140960795 + 1035560 * 2 ^ 59
def prefixEnd_1035560 : Nat := 4983230072969 + 3 ^ 40 * 1035560 * 2
def baseEnd_1035560 : Nat := 472657801395620978166713

theorem tailTrace_1035560 : CollatzResearch.WordTrace tailWord_1035560 prefixEnd_1035560 472657801395620978166713 := by
  unfold tailWord_1035560
  simp only [CollatzResearch.WordTrace]
  refine ⟨18884988064175227206300067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25179984085566969608400089 18884988064175227206300067)
  ·
    refine ⟨28327482096262840809450101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18884988064175227206300067 28327482096262840809450101)
    ·
      refine ⟨2655701446524641325885947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28327482096262840809450101 2655701446524641325885947)
      ·
        refine ⟨3983552169786961988828921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655701446524641325885947 3983552169786961988828921)
        ·
          refine ⟨2987664127340221491621691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3983552169786961988828921 2987664127340221491621691)
          ·
            refine ⟨4481496191010332237432537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987664127340221491621691 4481496191010332237432537)
            ·
              refine ⟨3361122143257749178074403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4481496191010332237432537 3361122143257749178074403)
              ·
                refine ⟨5041683214886623767111605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3361122143257749178074403 5041683214886623767111605)
                ·
                  refine ⟨472657801395620978166713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5041683214886623767111605 472657801395620978166713)
                  ·
                    rfl

theorem cell20_1035560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1035560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035560 prefixEnd_1035560 := by exact prefixLift 1035560
  have htrace : WordTrace (prefixWord ++ tailWord_1035560) baseStart_1035560 baseEnd_1035560 := by
    simpa [prefixWord, tailWord_1035560, baseEnd_1035560] using wordTrace_append hprefix tailTrace_1035560
  have hstable : (prefixWord ++ tailWord_1035560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035560).length < 2 ^ (prefixWord ++ tailWord_1035560).sum := by decide
  have hdescent : baseEnd_1035560 < baseStart_1035560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035577 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 3]
def baseStart_1035577 : Nat := 118140960795 + 1035577 * 2 ^ 59
def prefixEnd_1035577 : Nat := 4983230072969 + 3 ^ 40 * 1035577 * 2
def baseEnd_1035577 : Nat := 472665560658844474599977

theorem tailTrace_1035577 : CollatzResearch.WordTrace tailWord_1035577 prefixEnd_1035577 472665560658844474599977 := by
  unfold tailWord_1035577
  simp only [CollatzResearch.WordTrace]
  refine ⟨37770596169288866315968985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25180397446192577543979323 37770596169288866315968985)
  ·
    refine ⟨28327947126966649736976739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37770596169288866315968985 28327947126966649736976739)
    ·
      refine ⟨42491920690449974605465109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28327947126966649736976739 42491920690449974605465109)
      ·
        refine ⟨1991808782364842559631177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42491920690449974605465109 1991808782364842559631177)
        ·
          refine ⟨1493856586773631919723383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991808782364842559631177 1493856586773631919723383)
          ·
            refine ⟨2240784880160447879585075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493856586773631919723383 2240784880160447879585075)
            ·
              refine ⟨3361177320240671819377613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2240784880160447879585075 3361177320240671819377613)
              ·
                refine ⟨1260441495090251932266605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3361177320240671819377613 1260441495090251932266605)
                ·
                  refine ⟨472665560658844474599977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260441495090251932266605 472665560658844474599977)
                  ·
                    rfl

theorem cell20_1035577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_1035577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035577 prefixEnd_1035577 := by exact prefixLift 1035577
  have htrace : WordTrace (prefixWord ++ tailWord_1035577) baseStart_1035577 baseEnd_1035577 := by
    simpa [prefixWord, tailWord_1035577, baseEnd_1035577] using wordTrace_append hprefix tailTrace_1035577
  have hstable : (prefixWord ++ tailWord_1035577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035577).length < 2 ^ (prefixWord ++ tailWord_1035577).sum := by decide
  have hdescent : baseEnd_1035577 < baseStart_1035577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035629 : List Nat := [1, 5, 1, 1, 1, 5, 1, 5]
def baseStart_1035629 : Nat := 118140960795 + 1035629 * 2 ^ 59
def prefixEnd_1035629 : Nat := 4983230072969 + 3 ^ 40 * 1035629 * 2
def baseEnd_1035629 : Nat := 157563098291921134955477

theorem tailTrace_1035629 : CollatzResearch.WordTrace tailWord_1035629 prefixEnd_1035629 157563098291921134955477 := by
  unfold tailWord_1035629
  simp only [CollatzResearch.WordTrace]
  refine ⟨37772492765100479196861941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25181661843400319464574627 37772492765100479196861941)
  ·
    refine ⟨3541171196728169924705807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37772492765100479196861941 3541171196728169924705807)
    ·
      refine ⟨5311756795092254887058711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3541171196728169924705807 5311756795092254887058711)
      ·
        refine ⟨7967635192638382330588067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5311756795092254887058711 7967635192638382330588067)
        ·
          refine ⟨11951452788957573495882101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7967635192638382330588067 11951452788957573495882101)
          ·
            refine ⟨1120448698964772515238947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11951452788957573495882101 1120448698964772515238947)
            ·
              refine ⟨1680673048447158772858421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120448698964772515238947 1680673048447158772858421)
              ·
                refine ⟨157563098291921134955477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1680673048447158772858421 157563098291921134955477)
                ·
                  rfl

theorem cell20_1035629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 5].length) (baseStart_1035629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035629 prefixEnd_1035629 := by exact prefixLift 1035629
  have htrace : WordTrace (prefixWord ++ tailWord_1035629) baseStart_1035629 baseEnd_1035629 := by
    simpa [prefixWord, tailWord_1035629, baseEnd_1035629] using wordTrace_append hprefix tailTrace_1035629
  have hstable : (prefixWord ++ tailWord_1035629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035629).length < 2 ^ (prefixWord ++ tailWord_1035629).sum := by decide
  have hdescent : baseEnd_1035629 < baseStart_1035629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035660 : List Nat := [2, 2, 1, 2, 1, 3, 4, 3, 2]
def baseStart_1035660 : Nat := 118140960795 + 1035660 * 2 ^ 59
def prefixEnd_1035660 : Nat := 4983230072969 + 3 ^ 40 * 1035660 * 2
def baseEnd_1035660 : Nat := 472703444120465074832971

theorem tailTrace_1035660 : CollatzResearch.WordTrace tailWord_1035660 prefixEnd_1035660 472703444120465074832971 := by
  unfold tailWord_1035660
  simp only [CollatzResearch.WordTrace]
  refine ⟨18886811713994085745620217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25182415618658780994160289 18886811713994085745620217)
  ·
    refine ⟨14165108785495564309215163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18886811713994085745620217 14165108785495564309215163)
    ·
      refine ⟨21247663178243346463822745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14165108785495564309215163 21247663178243346463822745)
      ·
        refine ⟨15935747383682509847867059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21247663178243346463822745 15935747383682509847867059)
        ·
          refine ⟨23903621075523764771800589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15935747383682509847867059 23903621075523764771800589)
          ·
            refine ⟨8963857903321411789425221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23903621075523764771800589 8963857903321411789425221)
            ·
              refine ⟨1680723356872764710517229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8963857903321411789425221 1680723356872764710517229)
              ·
                refine ⟨630271258827286766443961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1680723356872764710517229 630271258827286766443961)
                ·
                  refine ⟨472703444120465074832971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630271258827286766443961 472703444120465074832971)
                  ·
                    rfl

theorem cell20_1035660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_1035660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035660 prefixEnd_1035660 := by exact prefixLift 1035660
  have htrace : WordTrace (prefixWord ++ tailWord_1035660) baseStart_1035660 baseEnd_1035660 := by
    simpa [prefixWord, tailWord_1035660, baseEnd_1035660] using wordTrace_append hprefix tailTrace_1035660
  have hstable : (prefixWord ++ tailWord_1035660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035660).length < 2 ^ (prefixWord ++ tailWord_1035660).sum := by decide
  have hdescent : baseEnd_1035660 < baseStart_1035660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035695 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 3]
def baseStart_1035695 : Nat := 118140960795 + 1035695 * 2 ^ 59
def prefixEnd_1035695 : Nat := 4983230072969 + 3 ^ 40 * 1035695 * 2
def baseEnd_1035695 : Nat := 472719419074160508666161

theorem tailTrace_1035695 : CollatzResearch.WordTrace tailWord_1035695 prefixEnd_1035695 472719419074160508666161 := by
  unfold tailWord_1035695
  simp only [CollatzResearch.WordTrace]
  refine ⟨37774899982861372468764539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25183266655240914979176359 37774899982861372468764539)
  ·
    refine ⟨56662349974292058703146809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37774899982861372468764539 56662349974292058703146809)
    ·
      refine ⟨42496762480719044027360107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56662349974292058703146809 42496762480719044027360107)
      ·
        refine ⟨63745143721078566041040161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42496762480719044027360107 63745143721078566041040161)
        ·
          refine ⟨47808857790808924530780121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63745143721078566041040161 47808857790808924530780121)
          ·
            refine ⟨35856643343106693398085091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47808857790808924530780121 35856643343106693398085091)
            ·
              refine ⟨53784965014660040097127637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35856643343106693398085091 53784965014660040097127637)
              ·
                refine ⟨1260585117531094689776429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53784965014660040097127637 1260585117531094689776429)
                ·
                  refine ⟨472719419074160508666161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260585117531094689776429 472719419074160508666161)
                  ·
                    rfl

theorem cell20_1035695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_1035695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035695 prefixEnd_1035695 := by exact prefixLift 1035695
  have htrace : WordTrace (prefixWord ++ tailWord_1035695) baseStart_1035695 baseEnd_1035695 := by
    simpa [prefixWord, tailWord_1035695, baseEnd_1035695] using wordTrace_append hprefix tailTrace_1035695
  have hstable : (prefixWord ++ tailWord_1035695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035695).length < 2 ^ (prefixWord ++ tailWord_1035695).sum := by decide
  have hdescent : baseEnd_1035695 < baseStart_1035695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035732 : List Nat := [2, 4, 1, 2, 3, 1, 3, 2, 2]
def baseStart_1035732 : Nat := 118140960795 + 1035732 * 2 ^ 59
def prefixEnd_1035732 : Nat := 4983230072969 + 3 ^ 40 * 1035732 * 2
def baseEnd_1035732 : Nat := 472736306882352824432677

theorem tailTrace_1035732 : CollatzResearch.WordTrace tailWord_1035732 prefixEnd_1035732 472736306882352824432677 := by
  unfold tailWord_1035732
  simp only [CollatzResearch.WordTrace]
  refine ⟨18888124741863663893930725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25184166322484885191907633 18888124741863663893930725)
  ·
    refine ⟨3541523389099436980112011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18888124741863663893930725 3541523389099436980112011)
    ·
      refine ⟨5312285083649155470168017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3541523389099436980112011 5312285083649155470168017)
      ·
        refine ⟨3984213812736866602626013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5312285083649155470168017 3984213812736866602626013)
        ·
          refine ⟨1494080179776324975984755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3984213812736866602626013 1494080179776324975984755)
          ·
            refine ⟨2241120269664487463977133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494080179776324975984755 2241120269664487463977133)
            ·
              refine ⟨840420101124182798991425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2241120269664487463977133 840420101124182798991425)
              ·
                refine ⟨630315075843137099243569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840420101124182798991425 630315075843137099243569)
                ·
                  refine ⟨472736306882352824432677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630315075843137099243569 472736306882352824432677)
                  ·
                    rfl

theorem cell20_1035732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_1035732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035732 prefixEnd_1035732 := by exact prefixLift 1035732
  have htrace : WordTrace (prefixWord ++ tailWord_1035732) baseStart_1035732 baseEnd_1035732 := by
    simpa [prefixWord, tailWord_1035732, baseEnd_1035732] using wordTrace_append hprefix tailTrace_1035732
  have hstable : (prefixWord ++ tailWord_1035732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035732).length < 2 ^ (prefixWord ++ tailWord_1035732).sum := by decide
  have hdescent : baseEnd_1035732 < baseStart_1035732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035733 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_1035733 : Nat := 118140960795 + 1035733 * 2 ^ 59
def prefixEnd_1035733 : Nat := 4983230072969 + 3 ^ 40 * 1035733 * 2
def baseEnd_1035733 : Nat := 472736763309601265399339

theorem tailTrace_1035733 : CollatzResearch.WordTrace tailWord_1035733 prefixEnd_1035733 472736763309601265399339 := by
  unfold tailWord_1035733
  simp only [CollatzResearch.WordTrace]
  refine ⟨37776285956723704958647853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25184190637815803305765235 37776285956723704958647853)
  ·
    refine ⟨14166107233771389359492945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37776285956723704958647853 14166107233771389359492945)
    ·
      refine ⟨10624580425328542019619709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14166107233771389359492945 10624580425328542019619709)
      ·
        refine ⟨3984217659498203257357391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10624580425328542019619709 3984217659498203257357391)
        ·
          refine ⟨5976326489247304886036087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984217659498203257357391 5976326489247304886036087)
          ·
            refine ⟨8964489733870957329054131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5976326489247304886036087 8964489733870957329054131)
            ·
              refine ⟨13446734600806435993581197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8964489733870957329054131 13446734600806435993581197)
              ·
                refine ⟨5042525475302413497592949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13446734600806435993581197 5042525475302413497592949)
                ·
                  refine ⟨472736763309601265399339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5042525475302413497592949 472736763309601265399339)
                  ·
                    rfl

theorem cell20_1035733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_1035733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035733 prefixEnd_1035733 := by exact prefixLift 1035733
  have htrace : WordTrace (prefixWord ++ tailWord_1035733) baseStart_1035733 baseEnd_1035733 := by
    simpa [prefixWord, tailWord_1035733, baseEnd_1035733] using wordTrace_append hprefix tailTrace_1035733
  have hstable : (prefixWord ++ tailWord_1035733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035733).length < 2 ^ (prefixWord ++ tailWord_1035733).sum := by decide
  have hdescent : baseEnd_1035733 < baseStart_1035733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035861 : List Nat := [1, 3, 2, 2, 1, 1, 1, 9]
def baseStart_1035861 : Nat := 118140960795 + 1035861 * 2 ^ 59
def prefixEnd_1035861 : Nat := 4983230072969 + 3 ^ 40 * 1035861 * 2
def baseEnd_1035861 : Nat := 157598395332467236377383

theorem tailTrace_1035861 : CollatzResearch.WordTrace tailWord_1035861 prefixEnd_1035861 157598395332467236377383 := by
  unfold tailWord_1035861
  simp only [CollatzResearch.WordTrace]
  refine ⟨37780954500259982819307437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25187303000173321879538291 37780954500259982819307437)
  ·
    refine ⟨14167857937597493557240289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37780954500259982819307437 14167857937597493557240289)
    ·
      refine ⟨10625893453198120167930217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14167857937597493557240289 10625893453198120167930217)
      ·
        refine ⟨7969420089898590125947663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10625893453198120167930217 7969420089898590125947663)
        ·
          refine ⟨11954130134847885188921495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969420089898590125947663 11954130134847885188921495)
          ·
            refine ⟨17931195202271827783382243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11954130134847885188921495 17931195202271827783382243)
            ·
              refine ⟨26896792803407741675073365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17931195202271827783382243 26896792803407741675073365)
              ·
                refine ⟨157598395332467236377383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26896792803407741675073365 157598395332467236377383)
                ·
                  rfl

theorem cell20_1035861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_1035861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035861 prefixEnd_1035861 := by exact prefixLift 1035861
  have htrace : WordTrace (prefixWord ++ tailWord_1035861) baseStart_1035861 baseEnd_1035861 := by
    simpa [prefixWord, tailWord_1035861, baseEnd_1035861] using wordTrace_append hprefix tailTrace_1035861
  have hstable : (prefixWord ++ tailWord_1035861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035861).length < 2 ^ (prefixWord ++ tailWord_1035861).sum := by decide
  have hdescent : baseEnd_1035861 < baseStart_1035861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035888 : List Nat := [2, 1, 1, 1, 6, 1, 3, 3, 2]
def baseStart_1035888 : Nat := 118140960795 + 1035888 * 2 ^ 59
def prefixEnd_1035888 : Nat := 4983230072969 + 3 ^ 40 * 1035888 * 2
def baseEnd_1035888 : Nat := 472807509533109615232039

theorem tailTrace_1035888 : CollatzResearch.WordTrace tailWord_1035888 prefixEnd_1035888 472807509533109615232039 := by
  unfold tailWord_1035888
  simp only [CollatzResearch.WordTrace]
  refine ⟨18890969635581083215270159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25187959514108110953693545 18890969635581083215270159)
  ·
    refine ⟨28336454453371624822905239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18890969635581083215270159 28336454453371624822905239)
    ·
      refine ⟨42504681680057437234357859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28336454453371624822905239 42504681680057437234357859)
      ·
        refine ⟨63757022520086155851536789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42504681680057437234357859 63757022520086155851536789)
        ·
          refine ⟨2988610430629038555540787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63757022520086155851536789 2988610430629038555540787)
          ·
            refine ⟨4482915645943557833311181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988610430629038555540787 4482915645943557833311181)
            ·
              refine ⟨1681093367228834187491693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4482915645943557833311181 1681093367228834187491693)
              ·
                refine ⟨630410012710812820309385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1681093367228834187491693 630410012710812820309385)
                ·
                  refine ⟨472807509533109615232039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630410012710812820309385 472807509533109615232039)
                  ·
                    rfl

theorem cell20_1035888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_1035888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035888 prefixEnd_1035888 := by exact prefixLift 1035888
  have htrace : WordTrace (prefixWord ++ tailWord_1035888) baseStart_1035888 baseEnd_1035888 := by
    simpa [prefixWord, tailWord_1035888, baseEnd_1035888] using wordTrace_append hprefix tailTrace_1035888
  have hstable : (prefixWord ++ tailWord_1035888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035888).length < 2 ^ (prefixWord ++ tailWord_1035888).sum := by decide
  have hdescent : baseEnd_1035888 < baseStart_1035888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035905 : List Nat := [1, 2, 4, 2, 1, 3, 3, 2, 2]
def baseStart_1035905 : Nat := 118140960795 + 1035905 * 2 ^ 59
def prefixEnd_1035905 : Nat := 4983230072969 + 3 ^ 40 * 1035905 * 2
def baseEnd_1035905 : Nat := 472815268796333111665303

theorem tailTrace_1035905 : CollatzResearch.WordTrace tailWord_1035905 prefixEnd_1035905 472815268796333111665303 := by
  unfold tailWord_1035905
  simp only [CollatzResearch.WordTrace]
  refine ⟨37782559312100578333909169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25188372874733718889272779 37782559312100578333909169)
  ·
    refine ⟨28336919484075433750431877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37782559312100578333909169 28336919484075433750431877)
    ·
      refine ⟨5313172403264143828205977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28336919484075433750431877 5313172403264143828205977)
      ·
        refine ⟨3984879302448107871154483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5313172403264143828205977 3984879302448107871154483)
        ·
          refine ⟨5977318953672161806731725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3984879302448107871154483 5977318953672161806731725)
          ·
            refine ⟨2241494607627060677524397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5977318953672161806731725 2241494607627060677524397)
            ·
              refine ⟨840560477860147754071649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2241494607627060677524397 840560477860147754071649)
              ·
                refine ⟨630420358395110815553737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840560477860147754071649 630420358395110815553737)
                ·
                  refine ⟨472815268796333111665303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630420358395110815553737 472815268796333111665303)
                  ·
                    rfl

theorem cell20_1035905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_1035905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035905 prefixEnd_1035905 := by exact prefixLift 1035905
  have htrace : WordTrace (prefixWord ++ tailWord_1035905) baseStart_1035905 baseEnd_1035905 := by
    simpa [prefixWord, tailWord_1035905, baseEnd_1035905] using wordTrace_append hprefix tailTrace_1035905
  have hstable : (prefixWord ++ tailWord_1035905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035905).length < 2 ^ (prefixWord ++ tailWord_1035905).sum := by decide
  have hdescent : baseEnd_1035905 < baseStart_1035905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035957 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 3]
def baseStart_1035957 : Nat := 118140960795 + 1035957 * 2 ^ 59
def prefixEnd_1035957 : Nat := 4983230072969 + 3 ^ 40 * 1035957 * 2
def baseEnd_1035957 : Nat := 472839003013252041931757

theorem tailTrace_1035957 : CollatzResearch.WordTrace tailWord_1035957 prefixEnd_1035957 472839003013252041931757 := by
  unfold tailWord_1035957
  simp only [CollatzResearch.WordTrace]
  refine ⟨37784455907912191214802125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25189637271941460809868083 37784455907912191214802125)
  ·
    refine ⟨14169170965467071705550797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37784455907912191214802125 14169170965467071705550797)
    ·
      refine ⟨5313439112050151889581549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14169170965467071705550797 5313439112050151889581549)
      ·
        refine ⟨1992539667018806958593081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5313439112050151889581549 1992539667018806958593081)
        ·
          refine ⟨1494404750264105218944811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1992539667018806958593081 1494404750264105218944811)
          ·
            refine ⟨2241607125396157828417217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494404750264105218944811 2241607125396157828417217)
            ·
              refine ⟨1681205344047118371312913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2241607125396157828417217 1681205344047118371312913)
              ·
                refine ⟨1260904008035338778484685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1681205344047118371312913 1260904008035338778484685)
                ·
                  refine ⟨472839003013252041931757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260904008035338778484685 472839003013252041931757)
                  ·
                    rfl

theorem cell20_1035957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_1035957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035957 prefixEnd_1035957 := by exact prefixLift 1035957
  have htrace : WordTrace (prefixWord ++ tailWord_1035957) baseStart_1035957 baseEnd_1035957 := by
    simpa [prefixWord, tailWord_1035957, baseEnd_1035957] using wordTrace_append hprefix tailTrace_1035957
  have hstable : (prefixWord ++ tailWord_1035957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035957).length < 2 ^ (prefixWord ++ tailWord_1035957).sum := by decide
  have hdescent : baseEnd_1035957 < baseStart_1035957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035961 : List Nat := [1, 2, 1, 4, 1, 1, 3, 4, 3]
def baseStart_1035961 : Nat := 118140960795 + 1035961 * 2 ^ 59
def prefixEnd_1035961 : Nat := 4983230072969 + 3 ^ 40 * 1035961 * 2
def baseEnd_1035961 : Nat := 472840828722245805798407

theorem tailTrace_1035961 : CollatzResearch.WordTrace tailWord_1035961 prefixEnd_1035961 472840828722245805798407 := by
  unfold tailWord_1035961
  simp only [CollatzResearch.WordTrace]
  refine ⟨37784601799897699897947737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25189734533265133265298491 37784601799897699897947737)
  ·
    refine ⟨28338451349923274923460803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37784601799897699897947737 28338451349923274923460803)
    ·
      refine ⟨42507677024884912385191205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28338451349923274923460803 42507677024884912385191205)
      ·
        refine ⟨7970189442165921072223351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42507677024884912385191205 7970189442165921072223351)
        ·
          refine ⟨11955284163248881608335027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970189442165921072223351 11955284163248881608335027)
          ·
            refine ⟨17932926244873322412502541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11955284163248881608335027 17932926244873322412502541)
            ·
              refine ⟨6724847341827495904688453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17932926244873322412502541 6724847341827495904688453)
              ·
                refine ⟨1260908876592655482129085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6724847341827495904688453 1260908876592655482129085)
                ·
                  refine ⟨472840828722245805798407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260908876592655482129085 472840828722245805798407)
                  ·
                    rfl

theorem cell20_1035961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_1035961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035961 prefixEnd_1035961 := by exact prefixLift 1035961
  have htrace : WordTrace (prefixWord ++ tailWord_1035961) baseStart_1035961 baseEnd_1035961 := by
    simpa [prefixWord, tailWord_1035961, baseEnd_1035961] using wordTrace_append hprefix tailTrace_1035961
  have hstable : (prefixWord ++ tailWord_1035961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035961).length < 2 ^ (prefixWord ++ tailWord_1035961).sum := by decide
  have hdescent : baseEnd_1035961 < baseStart_1035961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035964 : List Nat := [2, 2, 2, 3, 1, 3, 1, 4, 2]
def baseStart_1035964 : Nat := 118140960795 + 1035964 * 2 ^ 59
def prefixEnd_1035964 : Nat := 4983230072969 + 3 ^ 40 * 1035964 * 2
def baseEnd_1035964 : Nat := 472842198003991128698395

theorem tailTrace_1035964 : CollatzResearch.WordTrace tailWord_1035964 prefixEnd_1035964 472842198003991128698395 := by
  unfold tailWord_1035964
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892355609443415705153473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25189807479257887606871297 18892355609443415705153473)
  ·
    refine ⟨14169266707082561778865105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18892355609443415705153473 14169266707082561778865105)
    ·
      refine ⟨10626950030311921334148829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14169266707082561778865105 10626950030311921334148829)
      ·
        refine ⟨3985106261366970500305811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10626950030311921334148829 3985106261366970500305811)
        ·
          refine ⟨5977659392050455750458717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3985106261366970500305811 5977659392050455750458717)
          ·
            refine ⟨2241622272018920906422019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5977659392050455750458717 2241622272018920906422019)
            ·
              refine ⟨3362433408028381359633029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2241622272018920906422019 3362433408028381359633029)
              ·
                refine ⟨630456264005321504931193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3362433408028381359633029 630456264005321504931193)
                ·
                  refine ⟨472842198003991128698395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630456264005321504931193 472842198003991128698395)
                  ·
                    rfl

theorem cell20_1035964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_1035964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035964 prefixEnd_1035964 := by exact prefixLift 1035964
  have htrace : WordTrace (prefixWord ++ tailWord_1035964) baseStart_1035964 baseEnd_1035964 := by
    simpa [prefixWord, tailWord_1035964, baseEnd_1035964] using wordTrace_append hprefix tailTrace_1035964
  have hstable : (prefixWord ++ tailWord_1035964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035964).length < 2 ^ (prefixWord ++ tailWord_1035964).sum := by decide
  have hdescent : baseEnd_1035964 < baseStart_1035964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035968 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1035968 : Nat := 118140960795 + 1035968 * 2 ^ 59
def prefixEnd_1035968 : Nat := 4983230072969 + 3 ^ 40 * 1035968 * 2
def baseEnd_1035968 : Nat := 472844023712984892565045

theorem tailTrace_1035968 : CollatzResearch.WordTrace tailWord_1035968 prefixEnd_1035968 472844023712984892565045 := by
  unfold tailWord_1035968
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892428555436170046726279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25189904740581560062301705 18892428555436170046726279)
  ·
    refine ⟨28338642833154255070089419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18892428555436170046726279 28338642833154255070089419)
    ·
      refine ⟨42507964249731382605134129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28338642833154255070089419 42507964249731382605134129)
      ·
        refine ⟨31880973187298536953850597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42507964249731382605134129 31880973187298536953850597)
        ·
          refine ⟨5977682472618475678846987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31880973187298536953850597 5977682472618475678846987)
          ·
            refine ⟨8966523708927713518270481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977682472618475678846987 8966523708927713518270481)
            ·
              refine ⟨6724892781695785138702861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8966523708927713518270481 6724892781695785138702861)
              ·
                refine ⟨2521834793135919427013573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6724892781695785138702861 2521834793135919427013573)
                ·
                  refine ⟨472844023712984892565045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2521834793135919427013573 472844023712984892565045)
                  ·
                    rfl

theorem cell20_1035968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1035968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035968 prefixEnd_1035968 := by exact prefixLift 1035968
  have htrace : WordTrace (prefixWord ++ tailWord_1035968) baseStart_1035968 baseEnd_1035968 := by
    simpa [prefixWord, tailWord_1035968, baseEnd_1035968] using wordTrace_append hprefix tailTrace_1035968
  have hstable : (prefixWord ++ tailWord_1035968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035968).length < 2 ^ (prefixWord ++ tailWord_1035968).sum := by decide
  have hdescent : baseEnd_1035968 < baseStart_1035968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035974 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1035974 : Nat := 118140960795 + 1035974 * 2 ^ 59
def prefixEnd_1035974 : Nat := 4983230072969 + 3 ^ 40 * 1035974 * 2
def baseEnd_1035974 : Nat := 472846762276475538365021

theorem tailTrace_1035974 : CollatzResearch.WordTrace tailWord_1035974 prefixEnd_1035974 472846762276475538365021 := by
  unfold tailWord_1035974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180783623401581347442843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25190050632567068745447317 1180783623401581347442843)
  ·
    refine ⟨1771175435102372021164265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1180783623401581347442843 1771175435102372021164265)
    ·
      refine ⟨1328381576326779015873199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1771175435102372021164265 1328381576326779015873199)
      ·
        refine ⟨1992572364490168523809799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1328381576326779015873199 1992572364490168523809799)
        ·
          refine ⟨2988858546735252785714699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1992572364490168523809799 2988858546735252785714699)
          ·
            refine ⟨4483287820102879178572049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988858546735252785714699 4483287820102879178572049)
            ·
              refine ⟨3362465865077159383929037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4483287820102879178572049 3362465865077159383929037)
              ·
                refine ⟨1260924699403934768973389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3362465865077159383929037 1260924699403934768973389)
                ·
                  refine ⟨472846762276475538365021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260924699403934768973389 472846762276475538365021)
                  ·
                    rfl

theorem cell20_1035974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1035974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035974 prefixEnd_1035974 := by exact prefixLift 1035974
  have htrace : WordTrace (prefixWord ++ tailWord_1035974) baseStart_1035974 baseEnd_1035974 := by
    simpa [prefixWord, tailWord_1035974, baseEnd_1035974] using wordTrace_append hprefix tailTrace_1035974
  have hstable : (prefixWord ++ tailWord_1035974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035974).length < 2 ^ (prefixWord ++ tailWord_1035974).sum := by decide
  have hdescent : baseEnd_1035974 < baseStart_1035974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035992 : List Nat := [2, 1, 2, 2, 3, 1, 5, 4]
def baseStart_1035992 : Nat := 118140960795 + 1035992 * 2 ^ 59
def prefixEnd_1035992 : Nat := 4983230072969 + 3 ^ 40 * 1035992 * 2
def baseEnd_1035992 : Nat := 157618325988982491921649

theorem tailTrace_1035992 : CollatzResearch.WordTrace tailWord_1035992 prefixEnd_1035992 157618325988982491921649 := by
  unfold tailWord_1035992
  simp only [CollatzResearch.WordTrace]
  refine ⟨18892866231392696096163115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25190488308523594794884153 18892866231392696096163115)
  ·
    refine ⟨28339299347089044144244673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18892866231392696096163115 28339299347089044144244673)
    ·
      refine ⟨21254474510316783108183505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28339299347089044144244673 21254474510316783108183505)
      ·
        refine ⟨15940855882737587331137629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21254474510316783108183505 15940855882737587331137629)
        ·
          refine ⟨5977820956026595249176611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15940855882737587331137629 5977820956026595249176611)
          ·
            refine ⟨8966731434039892873764917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5977820956026595249176611 8966731434039892873764917)
            ·
              refine ⟨840631071941239956915461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8966731434039892873764917 840631071941239956915461)
              ·
                refine ⟨157618325988982491921649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 840631071941239956915461 157618325988982491921649)
                ·
                  rfl

theorem cell20_1035992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_1035992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035992 prefixEnd_1035992 := by exact prefixLift 1035992
  have htrace : WordTrace (prefixWord ++ tailWord_1035992) baseStart_1035992 baseEnd_1035992 := by
    simpa [prefixWord, tailWord_1035992, baseEnd_1035992] using wordTrace_append hprefix tailTrace_1035992
  have hstable : (prefixWord ++ tailWord_1035992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035992).length < 2 ^ (prefixWord ++ tailWord_1035992).sum := by decide
  have hdescent : baseEnd_1035992 < baseStart_1035992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036023 : List Nat := [1, 1, 3, 1, 1, 1, 6, 4, 2]
def baseStart_1036023 : Nat := 118140960795 + 1036023 * 2 ^ 59
def prefixEnd_1036023 : Nat := 4983230072969 + 3 ^ 40 * 1036023 * 2
def baseEnd_1036023 : Nat := 472869127211649145731487

theorem tailTrace_1036023 : CollatzResearch.WordTrace tailWord_1036023 prefixEnd_1036023 472869127211649145731487 := by
  unfold tailWord_1036023
  simp only [CollatzResearch.WordTrace]
  refine ⟨37786863125673084486704723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25191242083782056324469815 37786863125673084486704723)
  ·
    refine ⟨56680294688509626730057085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37786863125673084486704723 56680294688509626730057085)
    ·
      refine ⟨21255110508191110023771407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56680294688509626730057085 21255110508191110023771407)
      ·
        refine ⟨31882665762286665035657111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21255110508191110023771407 31882665762286665035657111)
        ·
          refine ⟨47823998643429997553485667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31882665762286665035657111 47823998643429997553485667)
          ·
            refine ⟨71735997965144996330228501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47823998643429997553485667 71735997965144996330228501)
            ·
              refine ⟨3362624904616171702979461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71735997965144996330228501 3362624904616171702979461)
              ·
                refine ⟨630492169615532194308649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3362624904616171702979461 630492169615532194308649)
                ·
                  refine ⟨472869127211649145731487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630492169615532194308649 472869127211649145731487)
                  ·
                    rfl

theorem cell20_1036023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 2].length) (baseStart_1036023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036023 prefixEnd_1036023 := by exact prefixLift 1036023
  have htrace : WordTrace (prefixWord ++ tailWord_1036023) baseStart_1036023 baseEnd_1036023 := by
    simpa [prefixWord, tailWord_1036023, baseEnd_1036023] using wordTrace_append hprefix tailTrace_1036023
  have hstable : (prefixWord ++ tailWord_1036023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036023).length < 2 ^ (prefixWord ++ tailWord_1036023).sum := by decide
  have hdescent : baseEnd_1036023 < baseStart_1036023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036044 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1036044 : Nat := 118140960795 + 1036044 * 2 ^ 59
def prefixEnd_1036044 : Nat := 4983230072969 + 3 ^ 40 * 1036044 * 2
def baseEnd_1036044 : Nat := 472878712183866406031401

theorem tailTrace_1036044 : CollatzResearch.WordTrace tailWord_1036044 prefixEnd_1036044 472878712183866406031401 := by
  unfold tailWord_1036044
  simp only [CollatzResearch.WordTrace]
  refine ⟨18893814529298502536609593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25191752705731336715479457 18893814529298502536609593)
  ·
    refine ⟨14170360896973876902457195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18893814529298502536609593 14170360896973876902457195)
    ·
      refine ⟨21255541345460815353685793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14170360896973876902457195 21255541345460815353685793)
      ·
        refine ⟨15941656009095611515264345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21255541345460815353685793 15941656009095611515264345)
        ·
          refine ⟨11956242006821708636448259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15941656009095611515264345 11956242006821708636448259)
          ·
            refine ⟨17934363010232562954672389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956242006821708636448259 17934363010232562954672389)
            ·
              refine ⟨3362693064418605554001073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17934363010232562954672389 3362693064418605554001073)
              ·
                refine ⟨2522019798313954165500805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3362693064418605554001073 2522019798313954165500805)
                ·
                  refine ⟨472878712183866406031401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522019798313954165500805 472878712183866406031401)
                  ·
                    rfl

theorem cell20_1036044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1036044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036044 prefixEnd_1036044 := by exact prefixLift 1036044
  have htrace : WordTrace (prefixWord ++ tailWord_1036044) baseStart_1036044 baseEnd_1036044 := by
    simpa [prefixWord, tailWord_1036044, baseEnd_1036044] using wordTrace_append hprefix tailTrace_1036044
  have hstable : (prefixWord ++ tailWord_1036044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036044).length < 2 ^ (prefixWord ++ tailWord_1036044).sum := by decide
  have hdescent : baseEnd_1036044 < baseStart_1036044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036068 : List Nat := [2, 3, 1, 3, 2, 3, 6]
def baseStart_1036068 : Nat := 118140960795 + 1036068 * 2 ^ 59
def prefixEnd_1036068 : Nat := 4983230072969 + 3 ^ 40 * 1036068 * 2
def baseEnd_1036068 : Nat := 52543296270869887692367

theorem tailTrace_1036068 : CollatzResearch.WordTrace tailWord_1036068 prefixEnd_1036068 52543296270869887692367 := by
  unfold tailWord_1036068
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894252205255028586046429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25192336273673371448061905 18894252205255028586046429)
  ·
    refine ⟨7085344576970635719767411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18894252205255028586046429 7085344576970635719767411)
    ·
      refine ⟨10628016865455953579651117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7085344576970635719767411 10628016865455953579651117)
      ·
        refine ⟨3985506324545982592369169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10628016865455953579651117 3985506324545982592369169)
        ·
          refine ⟨2989129743409486944276877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3985506324545982592369169 2989129743409486944276877)
          ·
            refine ⟨1120923653778557604103829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2989129743409486944276877 1120923653778557604103829)
            ·
              refine ⟨52543296270869887692367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1120923653778557604103829 52543296270869887692367)
              ·
                rfl

theorem cell20_1036068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 6].length) (baseStart_1036068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036068 prefixEnd_1036068 := by exact prefixLift 1036068
  have htrace : WordTrace (prefixWord ++ tailWord_1036068) baseStart_1036068 baseEnd_1036068 := by
    simpa [prefixWord, tailWord_1036068, baseEnd_1036068] using wordTrace_append hprefix tailTrace_1036068
  have hstable : (prefixWord ++ tailWord_1036068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036068).length < 2 ^ (prefixWord ++ tailWord_1036068).sum := by decide
  have hdescent : baseEnd_1036068 < baseStart_1036068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036092 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_1036092 : Nat := 118140960795 + 1036092 * 2 ^ 59
def prefixEnd_1036092 : Nat := 4983230072969 + 3 ^ 40 * 1036092 * 2
def baseEnd_1036092 : Nat := 472900620691791572431205

theorem tailTrace_1036092 : CollatzResearch.WordTrace tailWord_1036092 prefixEnd_1036092 472900620691791572431205 := by
  unfold tailWord_1036092
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894689881211554635483265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25192919841615406180644353 18894689881211554635483265)
  ·
    refine ⟨14171017410908665976612449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18894689881211554635483265 14171017410908665976612449)
    ·
      refine ⟨10628263058181499482459337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14171017410908665976612449 10628263058181499482459337)
      ·
        refine ⟨7971197293636124611844503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10628263058181499482459337 7971197293636124611844503)
        ·
          refine ⟨11956795940454186917766755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7971197293636124611844503 11956795940454186917766755)
          ·
            refine ⟨17935193910681280376650133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956795940454186917766755 17935193910681280376650133)
            ·
              refine ⟨840712214563185017655475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17935193910681280376650133 840712214563185017655475)
              ·
                refine ⟨1261068321844777526483213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840712214563185017655475 1261068321844777526483213)
                ·
                  refine ⟨472900620691791572431205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261068321844777526483213 472900620691791572431205)
                  ·
                    rfl

theorem cell20_1036092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_1036092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036092 prefixEnd_1036092 := by exact prefixLift 1036092
  have htrace : WordTrace (prefixWord ++ tailWord_1036092) baseStart_1036092 baseEnd_1036092 := by
    simpa [prefixWord, tailWord_1036092, baseEnd_1036092] using wordTrace_append hprefix tailTrace_1036092
  have hstable : (prefixWord ++ tailWord_1036092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036092).length < 2 ^ (prefixWord ++ tailWord_1036092).sum := by decide
  have hdescent : baseEnd_1036092 < baseStart_1036092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036130 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1036130 : Nat := 118140960795 + 1036130 * 2 ^ 59
def prefixEnd_1036130 : Nat := 4983230072969 + 3 ^ 40 * 1036130 * 2
def baseEnd_1036130 : Nat := 472917964927232329164383

theorem tailTrace_1036130 : CollatzResearch.WordTrace tailWord_1036130 prefixEnd_1036130 472917964927232329164383 := by
  unfold tailWord_1036130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447691434071360440212461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25193843824190294507233229 9447691434071360440212461)
  ·
    refine ⟨3542884287776760165079673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9447691434071360440212461 3542884287776760165079673)
    ·
      refine ⟨2657163215832570123809755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3542884287776760165079673 2657163215832570123809755)
      ·
        refine ⟨3985744823748855185714633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657163215832570123809755 3985744823748855185714633)
        ·
          refine ⟨2989308617811641389285975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3985744823748855185714633 2989308617811641389285975)
          ·
            refine ⟨4483962926717462083928963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989308617811641389285975 4483962926717462083928963)
            ·
              refine ⟨6725944390076193125893445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4483962926717462083928963 6725944390076193125893445)
              ·
                refine ⟨1261114573139286211105021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6725944390076193125893445 1261114573139286211105021)
                ·
                  refine ⟨472917964927232329164383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261114573139286211105021 472917964927232329164383)
                  ·
                    rfl

theorem cell20_1036130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1036130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036130 prefixEnd_1036130 := by exact prefixLift 1036130
  have htrace : WordTrace (prefixWord ++ tailWord_1036130) baseStart_1036130 baseEnd_1036130 := by
    simpa [prefixWord, tailWord_1036130, baseEnd_1036130] using wordTrace_append hprefix tailTrace_1036130
  have hstable : (prefixWord ++ tailWord_1036130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036130).length < 2 ^ (prefixWord ++ tailWord_1036130).sum := by decide
  have hdescent : baseEnd_1036130 < baseStart_1036130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036172 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1036172 : Nat := 118140960795 + 1036172 * 2 ^ 59
def prefixEnd_1036172 : Nat := 4983230072969 + 3 ^ 40 * 1036172 * 2
def baseEnd_1036172 : Nat := 472937134871666849764211

theorem tailTrace_1036172 : CollatzResearch.WordTrace tailWord_1036172 prefixEnd_1036172 472937134871666849764211 := by
  unfold tailWord_1036172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896148801066641466939385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25194865068088855289252513 18896148801066641466939385)
  ·
    refine ⟨14172111600799981100204539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18896148801066641466939385 14172111600799981100204539)
    ·
      refine ⟨21258167401199971650306809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14172111600799981100204539 21258167401199971650306809)
      ·
        refine ⟨15943625550899978737730107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21258167401199971650306809 15943625550899978737730107)
        ·
          refine ⟨23915438326349968106595161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15943625550899978737730107 23915438326349968106595161)
          ·
            refine ⟨17936578744762476079946371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23915438326349968106595161 17936578744762476079946371)
            ·
              refine ⟨26904868117143714119919557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17936578744762476079946371 26904868117143714119919557)
              ·
                refine ⟨5044662771964446397484917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26904868117143714119919557 5044662771964446397484917)
                ·
                  refine ⟨472937134871666849764211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5044662771964446397484917 472937134871666849764211)
                  ·
                    rfl

theorem cell20_1036172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1036172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036172 prefixEnd_1036172 := by exact prefixLift 1036172
  have htrace : WordTrace (prefixWord ++ tailWord_1036172) baseStart_1036172 baseEnd_1036172 := by
    simpa [prefixWord, tailWord_1036172, baseEnd_1036172] using wordTrace_append hprefix tailTrace_1036172
  have hstable : (prefixWord ++ tailWord_1036172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036172).length < 2 ^ (prefixWord ++ tailWord_1036172).sum := by decide
  have hdescent : baseEnd_1036172 < baseStart_1036172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036189 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1036189 : Nat := 118140960795 + 1036189 * 2 ^ 59
def prefixEnd_1036189 : Nat := 4983230072969 + 3 ^ 40 * 1036189 * 2
def baseEnd_1036189 : Nat := 472944894134890346197475

theorem tailTrace_1036189 : CollatzResearch.WordTrace tailWord_1036189 prefixEnd_1036189 472944894134890346197475 := by
  unfold tailWord_1036189
  simp only [CollatzResearch.WordTrace]
  refine ⟨37792917643071694837247621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25195278428714463224831747 37792917643071694837247621)
  ·
    refine ⟨7086172058075942781983929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37792917643071694837247621 7086172058075942781983929)
    ·
      refine ⟨5314629043556957086487947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7086172058075942781983929 5314629043556957086487947)
      ·
        refine ⟨7971943565335435629731921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314629043556957086487947 7971943565335435629731921)
        ·
          refine ⟨5978957674001576722298941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7971943565335435629731921 5978957674001576722298941)
          ·
            refine ⟨2242109127750591270862103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5978957674001576722298941 2242109127750591270862103)
            ·
              refine ⟨3363163691625886906293155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2242109127750591270862103 3363163691625886906293155)
              ·
                refine ⟨5044745537438830359439733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363163691625886906293155 5044745537438830359439733)
                ·
                  refine ⟨472944894134890346197475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5044745537438830359439733 472944894134890346197475)
                  ·
                    rfl

theorem cell20_1036189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1036189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036189 prefixEnd_1036189 := by exact prefixLift 1036189
  have htrace : WordTrace (prefixWord ++ tailWord_1036189) baseStart_1036189 baseEnd_1036189 := by
    simpa [prefixWord, tailWord_1036189, baseEnd_1036189] using wordTrace_append hprefix tailTrace_1036189
  have hstable : (prefixWord ++ tailWord_1036189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036189).length < 2 ^ (prefixWord ++ tailWord_1036189).sum := by decide
  have hdescent : baseEnd_1036189 < baseStart_1036189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036196 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1036196 : Nat := 118140960795 + 1036196 * 2 ^ 59
def prefixEnd_1036196 : Nat := 4983230072969 + 3 ^ 40 * 1036196 * 2
def baseEnd_1036196 : Nat := 472948089125629432964113

theorem tailTrace_1036196 : CollatzResearch.WordTrace tailWord_1036196 prefixEnd_1036196 472948089125629432964113 := by
  unfold tailWord_1036196
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896586477023167516376221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25195448636030890021834961 18896586477023167516376221)
  ·
    refine ⟨7086219928883687818641083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18896586477023167516376221 7086219928883687818641083)
    ·
      refine ⟨10629329893325531727961625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086219928883687818641083 10629329893325531727961625)
      ·
        refine ⟨7971997419994148795971219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10629329893325531727961625 7971997419994148795971219)
        ·
          refine ⟨11957996129991223193956829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7971997419994148795971219 11957996129991223193956829)
          ·
            refine ⟨4484248548746708697733811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11957996129991223193956829 4484248548746708697733811)
            ·
              refine ⟨6726372823120063046600717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484248548746708697733811 6726372823120063046600717)
              ·
                refine ⟨2522389808670023642475269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6726372823120063046600717 2522389808670023642475269)
                ·
                  refine ⟨472948089125629432964113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522389808670023642475269 472948089125629432964113)
                  ·
                    rfl

theorem cell20_1036196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1036196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036196 prefixEnd_1036196 := by exact prefixLift 1036196
  have htrace : WordTrace (prefixWord ++ tailWord_1036196) baseStart_1036196 baseEnd_1036196 := by
    simpa [prefixWord, tailWord_1036196, baseEnd_1036196] using wordTrace_append hprefix tailTrace_1036196
  have hstable : (prefixWord ++ tailWord_1036196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036196).length < 2 ^ (prefixWord ++ tailWord_1036196).sum := by decide
  have hdescent : baseEnd_1036196 < baseStart_1036196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036248 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_1036248 : Nat := 118140960795 + 1036248 * 2 ^ 59
def prefixEnd_1036248 : Nat := 4983230072969 + 3 ^ 40 * 1036248 * 2
def baseEnd_1036248 : Nat := 472971823342548363230567

theorem tailTrace_1036248 : CollatzResearch.WordTrace tailWord_1036248 prefixEnd_1036248 472971823342548363230567 := by
  unfold tailWord_1036248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18897534774928973956822699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25196713033238631942430265 18897534774928973956822699)
  ·
    refine ⟨28346302162393460935234049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18897534774928973956822699 28346302162393460935234049)
    ·
      refine ⟨21259726621795095701425537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28346302162393460935234049 21259726621795095701425537)
      ·
        refine ⟨15944794966346321776069153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21259726621795095701425537 15944794966346321776069153)
        ·
          refine ⟨11958596224759741332051865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15944794966346321776069153 11958596224759741332051865)
          ·
            refine ⟨8968947168569805999038899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11958596224759741332051865 8968947168569805999038899)
            ·
              refine ⟨13453420752854708998558349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8968947168569805999038899 13453420752854708998558349)
              ·
                refine ⟨5045032782320515874459381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13453420752854708998558349 5045032782320515874459381)
                ·
                  refine ⟨472971823342548363230567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5045032782320515874459381 472971823342548363230567)
                  ·
                    rfl

theorem cell20_1036248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_1036248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036248 prefixEnd_1036248 := by exact prefixLift 1036248
  have htrace : WordTrace (prefixWord ++ tailWord_1036248) baseStart_1036248 baseEnd_1036248 := by
    simpa [prefixWord, tailWord_1036248, baseEnd_1036248] using wordTrace_append hprefix tailTrace_1036248
  have hstable : (prefixWord ++ tailWord_1036248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036248).length < 2 ^ (prefixWord ++ tailWord_1036248).sum := by decide
  have hdescent : baseEnd_1036248 < baseStart_1036248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036289 : List Nat := [1, 2, 4, 1, 2, 1, 2, 5, 2]
def baseStart_1036289 : Nat := 118140960795 + 1036289 * 2 ^ 59
def prefixEnd_1036289 : Nat := 4983230072969 + 3 ^ 40 * 1036289 * 2
def baseEnd_1036289 : Nat := 472990536859734442863733

theorem tailTrace_1036289 : CollatzResearch.WordTrace tailWord_1036289 prefixEnd_1036289 472990536859734442863733 := by
  unfold tailWord_1036289
  simp only [CollatzResearch.WordTrace]
  refine ⟨37796564942709411915887921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25197709961806274610591947 37796564942709411915887921)
  ·
    refine ⟨28347423707032058936915941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37796564942709411915887921 28347423707032058936915941)
    ·
      refine ⟨5315141945068511050671739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28347423707032058936915941 5315141945068511050671739)
      ·
        refine ⟨7972712917602766576007609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315141945068511050671739 7972712917602766576007609)
        ·
          refine ⟨5979534688202074932005707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7972712917602766576007609 5979534688202074932005707)
          ·
            refine ⟨8969302032303112398008561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979534688202074932005707 8969302032303112398008561)
            ·
              refine ⟨6726976524227334298506421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8969302032303112398008561 6726976524227334298506421)
              ·
                refine ⟨630654049146312590484977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6726976524227334298506421 630654049146312590484977)
                ·
                  refine ⟨472990536859734442863733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630654049146312590484977 472990536859734442863733)
                  ·
                    rfl

theorem cell20_1036289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_1036289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036289 prefixEnd_1036289 := by exact prefixLift 1036289
  have htrace : WordTrace (prefixWord ++ tailWord_1036289) baseStart_1036289 baseEnd_1036289 := by
    simpa [prefixWord, tailWord_1036289, baseEnd_1036289] using wordTrace_append hprefix tailTrace_1036289
  have hstable : (prefixWord ++ tailWord_1036289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036289).length < 2 ^ (prefixWord ++ tailWord_1036289).sum := by decide
  have hdescent : baseEnd_1036289 < baseStart_1036289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036344 : List Nat := [2, 1, 2, 1, 6, 1, 2, 3, 2]
def baseStart_1036344 : Nat := 118140960795 + 1036344 * 2 ^ 59
def prefixEnd_1036344 : Nat := 4983230072969 + 3 ^ 40 * 1036344 * 2
def baseEnd_1036344 : Nat := 473015640358398696030175

theorem tailTrace_1036344 : CollatzResearch.WordTrace tailWord_1036344 prefixEnd_1036344 473015640358398696030175 := by
  unfold tailWord_1036344
  simp only [CollatzResearch.WordTrace]
  refine ⟨18899285478755078154570043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25199047305006770872760057 18899285478755078154570043)
  ·
    refine ⟨28348928218132617231855065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18899285478755078154570043 28348928218132617231855065)
    ·
      refine ⟨21261696163599462923891299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28348928218132617231855065 21261696163599462923891299)
      ·
        refine ⟨31892544245399194385836949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21261696163599462923891299 31892544245399194385836949)
        ·
          refine ⟨1494963011503087236836107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31892544245399194385836949 1494963011503087236836107)
          ·
            refine ⟨2242444517254630855254161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494963011503087236836107 2242444517254630855254161)
            ·
              refine ⟨1681833387940973141440621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242444517254630855254161 1681833387940973141440621)
              ·
                refine ⟨630687520477864928040233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1681833387940973141440621 630687520477864928040233)
                ·
                  refine ⟨473015640358398696030175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630687520477864928040233 473015640358398696030175)
                  ·
                    rfl

theorem cell20_1036344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_1036344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036344 prefixEnd_1036344 := by exact prefixLift 1036344
  have htrace : WordTrace (prefixWord ++ tailWord_1036344) baseStart_1036344 baseEnd_1036344 := by
    simpa [prefixWord, tailWord_1036344, baseEnd_1036344] using wordTrace_append hprefix tailTrace_1036344
  have hstable : (prefixWord ++ tailWord_1036344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036344).length < 2 ^ (prefixWord ++ tailWord_1036344).sum := by decide
  have hdescent : baseEnd_1036344 < baseStart_1036344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036358 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1036358 : Nat := 118140960795 + 1036358 * 2 ^ 59
def prefixEnd_1036358 : Nat := 4983230072969 + 3 ^ 40 * 1036358 * 2
def baseEnd_1036358 : Nat := 473022030339876869563451

theorem tailTrace_1036358 : CollatzResearch.WordTrace tailWord_1036358 prefixEnd_1036358 473022030339876869563451 := by
  unfold tailWord_1036358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1181221299358107396879679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25199387719639624466766485 1181221299358107396879679)
  ·
    refine ⟨1771831949037161095319519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1181221299358107396879679 1771831949037161095319519)
    ·
      refine ⟨2657747923555741642979279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771831949037161095319519 2657747923555741642979279)
      ·
        refine ⟨3986621885333612464468919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657747923555741642979279 3986621885333612464468919)
        ·
          refine ⟨5979932828000418696703379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3986621885333612464468919 5979932828000418696703379)
          ·
            refine ⟨8969899242000628045055069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979932828000418696703379 8969899242000628045055069)
            ·
              refine ⟨3363712215750235516895651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8969899242000628045055069 3363712215750235516895651)
              ·
                refine ⟨5045568323625353275343477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3363712215750235516895651 5045568323625353275343477)
                ·
                  refine ⟨473022030339876869563451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5045568323625353275343477 473022030339876869563451)
                  ·
                    rfl

theorem cell20_1036358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1036358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036358 prefixEnd_1036358 := by exact prefixLift 1036358
  have htrace : WordTrace (prefixWord ++ tailWord_1036358) baseStart_1036358 baseEnd_1036358 := by
    simpa [prefixWord, tailWord_1036358, baseEnd_1036358] using wordTrace_append hprefix tailTrace_1036358
  have hstable : (prefixWord ++ tailWord_1036358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036358).length < 2 ^ (prefixWord ++ tailWord_1036358).sum := by decide
  have hdescent : baseEnd_1036358 < baseStart_1036358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036365 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1036365 : Nat := 118140960795 + 1036365 * 2 ^ 59
def prefixEnd_1036365 : Nat := 4983230072969 + 3 ^ 40 * 1036365 * 2
def baseEnd_1036365 : Nat := 473025225330615956330089

theorem tailTrace_1036365 : CollatzResearch.WordTrace tailWord_1036365 prefixEnd_1036365 473025225330615956330089 := by
  unfold tailWord_1036365
  simp only [CollatzResearch.WordTrace]
  refine ⟨37799336890434076895654549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25199557926956051263769699 37799336890434076895654549)
  ·
    refine ⟨1771843916739097354483807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37799336890434076895654549 1771843916739097354483807)
    ·
      refine ⟨2657765875108646031725711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771843916739097354483807 2657765875108646031725711)
      ·
        refine ⟨3986648812662969047588567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657765875108646031725711 3986648812662969047588567)
        ·
          refine ⟨5979973218994453571382851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3986648812662969047588567 5979973218994453571382851)
          ·
            refine ⟨8969959828491680357074277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979973218994453571382851 8969959828491680357074277)
            ·
              refine ⟨1681867467842190066951427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8969959828491680357074277 1681867467842190066951427)
              ·
                refine ⟨2522801201763285100427141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1681867467842190066951427 2522801201763285100427141)
                ·
                  refine ⟨473025225330615956330089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2522801201763285100427141 473025225330615956330089)
                  ·
                    rfl

theorem cell20_1036365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1036365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036365 prefixEnd_1036365 := by exact prefixLift 1036365
  have htrace : WordTrace (prefixWord ++ tailWord_1036365) baseStart_1036365 baseEnd_1036365 := by
    simpa [prefixWord, tailWord_1036365, baseEnd_1036365] using wordTrace_append hprefix tailTrace_1036365
  have hstable : (prefixWord ++ tailWord_1036365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036365).length < 2 ^ (prefixWord ++ tailWord_1036365).sum := by decide
  have hdescent : baseEnd_1036365 < baseStart_1036365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036400 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1036400 : Nat := 118140960795 + 1036400 * 2 ^ 59
def prefixEnd_1036400 : Nat := 4983230072969 + 3 ^ 40 * 1036400 * 2
def baseEnd_1036400 : Nat := 473041200284311390163279

theorem tailTrace_1036400 : CollatzResearch.WordTrace tailWord_1036400 prefixEnd_1036400 473041200284311390163279 := by
  unfold tailWord_1036400
  simp only [CollatzResearch.WordTrace]
  refine ⟨18900306722653638936589327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25200408963538185248785769 18900306722653638936589327)
  ·
    refine ⟨28350460083980458404883991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18900306722653638936589327 28350460083980458404883991)
    ·
      refine ⟨42525690125970687607325987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28350460083980458404883991 42525690125970687607325987)
      ·
        refine ⟨63788535188956031410988981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42525690125970687607325987 63788535188956031410988981)
        ·
          refine ⟨5980175173964627944780217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63788535188956031410988981 5980175173964627944780217)
          ·
            refine ⟨4485131380473470958585163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5980175173964627944780217 4485131380473470958585163)
            ·
              refine ⟨6727697070710206437877745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485131380473470958585163 6727697070710206437877745)
              ·
                refine ⟨5045772803032654828408309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727697070710206437877745 5045772803032654828408309)
                ·
                  refine ⟨473041200284311390163279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5045772803032654828408309 473041200284311390163279)
                  ·
                    rfl

theorem cell20_1036400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1036400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036400 prefixEnd_1036400 := by exact prefixLift 1036400
  have htrace : WordTrace (prefixWord ++ tailWord_1036400) baseStart_1036400 baseEnd_1036400 := by
    simpa [prefixWord, tailWord_1036400, baseEnd_1036400] using wordTrace_append hprefix tailTrace_1036400
  have hstable : (prefixWord ++ tailWord_1036400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036400).length < 2 ^ (prefixWord ++ tailWord_1036400).sum := by decide
  have hdescent : baseEnd_1036400 < baseStart_1036400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036420 : List Nat := [2, 3, 2, 1, 2, 1, 5, 2, 2]
def baseStart_1036420 : Nat := 118140960795 + 1036420 * 2 ^ 59
def prefixEnd_1036420 : Nat := 4983230072969 + 3 ^ 40 * 1036420 * 2
def baseEnd_1036420 : Nat := 473050328829280209496531

theorem tailTrace_1036420 : CollatzResearch.WordTrace tailWord_1036420 prefixEnd_1036420 473050328829280209496531 := by
  unfold tailWord_1036420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18900671452617410644453357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25200895270156547525937809 18900671452617410644453357)
  ·
    refine ⟨7087751794731528991670009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18900671452617410644453357 7087751794731528991670009)
    ·
      refine ⟨5315813846048646743752507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7087751794731528991670009 5315813846048646743752507)
      ·
        refine ⟨7973720769072970115628761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315813846048646743752507 7973720769072970115628761)
        ·
          refine ⟨5980290576804727586721571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7973720769072970115628761 5980290576804727586721571)
          ·
            refine ⟨8970435865207091380082357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980290576804727586721571 8970435865207091380082357)
            ·
              refine ⟨840978362363164816882721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8970435865207091380082357 840978362363164816882721)
              ·
                refine ⟨630733771772373612662041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 840978362363164816882721 630733771772373612662041)
                ·
                  refine ⟨473050328829280209496531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630733771772373612662041 473050328829280209496531)
                  ·
                    rfl

theorem cell20_1036420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_1036420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036420 prefixEnd_1036420 := by exact prefixLift 1036420
  have htrace : WordTrace (prefixWord ++ tailWord_1036420) baseStart_1036420 baseEnd_1036420 := by
    simpa [prefixWord, tailWord_1036420, baseEnd_1036420] using wordTrace_append hprefix tailTrace_1036420
  have hstable : (prefixWord ++ tailWord_1036420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036420).length < 2 ^ (prefixWord ++ tailWord_1036420).sum := by decide
  have hdescent : baseEnd_1036420 < baseStart_1036420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036430 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1036430 : Nat := 118140960795 + 1036430 * 2 ^ 59
def prefixEnd_1036430 : Nat := 4983230072969 + 3 ^ 40 * 1036430 * 2
def baseEnd_1036430 : Nat := 473054893101764619163157

theorem tailTrace_1036430 : CollatzResearch.WordTrace tailWord_1036430 prefixEnd_1036430 473054893101764619163157 := by
  unfold tailWord_1036430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4725213454399824124596343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25201138423465728664513829 4725213454399824124596343)
  ·
    refine ⟨7087820181599736186894515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4725213454399824124596343 7087820181599736186894515)
    ·
      refine ⟨10631730272399604280341773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7087820181599736186894515 10631730272399604280341773)
      ·
        refine ⟨3986898852149851605128165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10631730272399604280341773 3986898852149851605128165)
        ·
          refine ⟨747543534778097175961531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3986898852149851605128165 747543534778097175961531)
          ·
            refine ⟨1121315302167145763942297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747543534778097175961531 1121315302167145763942297)
            ·
              refine ⟨840986476625359322956723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121315302167145763942297 840986476625359322956723)
              ·
                refine ⟨1261479714938038984435085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840986476625359322956723 1261479714938038984435085)
                ·
                  refine ⟨473054893101764619163157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261479714938038984435085 473054893101764619163157)
                  ·
                    rfl

theorem cell20_1036430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1036430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036430 prefixEnd_1036430 := by exact prefixLift 1036430
  have htrace : WordTrace (prefixWord ++ tailWord_1036430) baseStart_1036430 baseEnd_1036430 := by
    simpa [prefixWord, tailWord_1036430, baseEnd_1036430] using wordTrace_append hprefix tailTrace_1036430
  have hstable : (prefixWord ++ tailWord_1036430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036430).length < 2 ^ (prefixWord ++ tailWord_1036430).sum := by decide
  have hdescent : baseEnd_1036430 < baseStart_1036430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036469 : List Nat := [1, 3, 3, 4, 9]
def baseStart_1036469 : Nat := 118140960795 + 1036469 * 2 ^ 59
def prefixEnd_1036469 : Nat := 4983230072969 + 3 ^ 40 * 1036469 * 2
def baseEnd_1036469 : Nat := 5840403626721652060037

theorem tailTrace_1036469 : CollatzResearch.WordTrace tailWord_1036469 prefixEnd_1036469 5840403626721652060037 := by
  unfold tailWord_1036469
  simp only [CollatzResearch.WordTrace]
  refine ⟨37803130082057302657440461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25202086721371535104960307 37803130082057302657440461)
  ·
    refine ⟨14176173780771488496540173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37803130082057302657440461 14176173780771488496540173)
    ·
      refine ⟨5316065167789308186202565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14176173780771488496540173 5316065167789308186202565)
      ·
        refine ⟨996762218960495284912981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5316065167789308186202565 996762218960495284912981)
        ·
          refine ⟨5840403626721652060037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 996762218960495284912981 5840403626721652060037)
          ·
            rfl

theorem cell20_1036469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 9].length) (baseStart_1036469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036469 prefixEnd_1036469 := by exact prefixLift 1036469
  have htrace : WordTrace (prefixWord ++ tailWord_1036469) baseStart_1036469 baseEnd_1036469 := by
    simpa [prefixWord, tailWord_1036469, baseEnd_1036469] using wordTrace_append hprefix tailTrace_1036469
  have hstable : (prefixWord ++ tailWord_1036469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036469).length < 2 ^ (prefixWord ++ tailWord_1036469).sum := by decide
  have hdescent : baseEnd_1036469 < baseStart_1036469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036482 : List Nat := [3, 5, 1, 1, 1, 3, 1, 5]
def baseStart_1036482 : Nat := 118140960795 + 1036482 * 2 ^ 59
def prefixEnd_1036482 : Nat := 4983230072969 + 3 ^ 40 * 1036482 * 2
def baseEnd_1036482 : Nat := 157692875772894516476537

theorem tailTrace_1036482 : CollatzResearch.WordTrace tailWord_1036482 prefixEnd_1036482 157692875772894516476537 := by
  unfold tailWord_1036482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9450901057752551469415925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25202402820673470585109133 9450901057752551469415925)
  ·
    refine ⟨886021974164301700257743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9450901057752551469415925 886021974164301700257743)
    ·
      refine ⟨1329032961246452550386615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 886021974164301700257743 1329032961246452550386615)
      ·
        refine ⟨1993549441869678825579923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329032961246452550386615 1993549441869678825579923)
        ·
          refine ⟨2990324162804518238369885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993549441869678825579923 2990324162804518238369885)
          ·
            refine ⟨1121371561051694339388707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2990324162804518238369885 1121371561051694339388707)
            ·
              refine ⟨1682057341577541509083061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121371561051694339388707 1682057341577541509083061)
              ·
                refine ⟨157692875772894516476537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1682057341577541509083061 157692875772894516476537)
                ·
                  rfl

theorem cell20_1036482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_1036482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036482 prefixEnd_1036482 := by exact prefixLift 1036482
  have htrace : WordTrace (prefixWord ++ tailWord_1036482) baseStart_1036482 baseEnd_1036482 := by
    simpa [prefixWord, tailWord_1036482, baseEnd_1036482] using wordTrace_append hprefix tailTrace_1036482
  have hstable : (prefixWord ++ tailWord_1036482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036482).length < 2 ^ (prefixWord ++ tailWord_1036482).sum := by decide
  have hdescent : baseEnd_1036482 < baseStart_1036482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036517 : List Nat := [1, 3, 1, 4, 2, 1, 1, 5, 2]
def baseStart_1036517 : Nat := 118140960795 + 1036517 * 2 ^ 59
def prefixEnd_1036517 : Nat := 4983230072969 + 3 ^ 40 * 1036517 * 2
def baseEnd_1036517 : Nat := 473094602272378983262801

theorem tailTrace_1036517 : CollatzResearch.WordTrace tailWord_1036517 prefixEnd_1036517 473094602272378983262801 := by
  unfold tailWord_1036517
  simp only [CollatzResearch.WordTrace]
  refine ⟨37804880785883406855187805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25203253857255604570125203 37804880785883406855187805)
  ·
    refine ⟨14176830294706277570695427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37804880785883406855187805 14176830294706277570695427)
    ·
      refine ⟨21265245442059416356043141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14176830294706277570695427 21265245442059416356043141)
      ·
        refine ⟨3987233520386140566758089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21265245442059416356043141 3987233520386140566758089)
        ·
          refine ⟨2990425140289605425068567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3987233520386140566758089 2990425140289605425068567)
          ·
            refine ⟨4485637710434408137602851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990425140289605425068567 4485637710434408137602851)
            ·
              refine ⟨6728456565651612206404277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485637710434408137602851 6728456565651612206404277)
              ·
                refine ⟨630792803029838644350401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6728456565651612206404277 630792803029838644350401)
                ·
                  refine ⟨473094602272378983262801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630792803029838644350401 473094602272378983262801)
                  ·
                    rfl

theorem cell20_1036517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_1036517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036517 prefixEnd_1036517 := by exact prefixLift 1036517
  have htrace : WordTrace (prefixWord ++ tailWord_1036517) baseStart_1036517 baseEnd_1036517 := by
    simpa [prefixWord, tailWord_1036517, baseEnd_1036517] using wordTrace_append hprefix tailTrace_1036517
  have hstable : (prefixWord ++ tailWord_1036517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036517).length < 2 ^ (prefixWord ++ tailWord_1036517).sum := by decide
  have hdescent : baseEnd_1036517 < baseStart_1036517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036538 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 4]
def baseStart_1036538 : Nat := 118140960795 + 1036538 * 2 ^ 59
def prefixEnd_1036538 : Nat := 4983230072969 + 3 ^ 40 * 1036538 * 2
def baseEnd_1036538 : Nat := 473104187244596243562715

theorem tailTrace_1036538 : CollatzResearch.WordTrace tailWord_1036538 prefixEnd_1036538 473104187244596243562715 := by
  unfold tailWord_1036538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451411679701831860425567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25203764479204884961134845 9451411679701831860425567)
  ·
    refine ⟨14177117519552747790638351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9451411679701831860425567 14177117519552747790638351)
    ·
      refine ⟨21265676279329121685957527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14177117519552747790638351 21265676279329121685957527)
      ·
        refine ⟨31898514418993682528936291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21265676279329121685957527 31898514418993682528936291)
        ·
          refine ⟨47847771628490523793404437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31898514418993682528936291 47847771628490523793404437)
          ·
            refine ⟨2242864295085493302815833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47847771628490523793404437 2242864295085493302815833)
            ·
              refine ⟨1682148221314119977111875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2242864295085493302815833 1682148221314119977111875)
              ·
                refine ⟨2523222331971179965667813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682148221314119977111875 2523222331971179965667813)
                ·
                  refine ⟨473104187244596243562715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523222331971179965667813 473104187244596243562715)
                  ·
                    rfl

theorem cell20_1036538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_1036538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036538 prefixEnd_1036538 := by exact prefixLift 1036538
  have htrace : WordTrace (prefixWord ++ tailWord_1036538) baseStart_1036538 baseEnd_1036538 := by
    simpa [prefixWord, tailWord_1036538, baseEnd_1036538] using wordTrace_append hprefix tailTrace_1036538
  have hstable : (prefixWord ++ tailWord_1036538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036538).length < 2 ^ (prefixWord ++ tailWord_1036538).sum := by decide
  have hdescent : baseEnd_1036538 < baseStart_1036538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036589 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 4]
def baseStart_1036589 : Nat := 118140960795 + 1036589 * 2 ^ 59
def prefixEnd_1036589 : Nat := 4983230072969 + 3 ^ 40 * 1036589 * 2
def baseEnd_1036589 : Nat := 473127465034266732862507

theorem tailTrace_1036589 : CollatzResearch.WordTrace tailWord_1036589 prefixEnd_1036589 473127465034266732862507 := by
  unfold tailWord_1036589
  simp only [CollatzResearch.WordTrace]
  refine ⟨37807506841622563151808821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25205004561081708767872547 37807506841622563151808821)
  ·
    refine ⟨3544453766402115295482077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37807506841622563151808821 3544453766402115295482077)
    ·
      refine ⟨1329170162400793235805779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3544453766402115295482077 1329170162400793235805779)
      ·
        refine ⟨1993755243601189853708669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1329170162400793235805779 1993755243601189853708669)
        ·
          refine ⟨747658216350446195140751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1993755243601189853708669 747658216350446195140751)
          ·
            refine ⟨1121487324525669292711127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747658216350446195140751 1121487324525669292711127)
            ·
              refine ⟨1682230986788503939066691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121487324525669292711127 1682230986788503939066691)
              ·
                refine ⟨2523346480182755908600037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682230986788503939066691 2523346480182755908600037)
                ·
                  refine ⟨473127465034266732862507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523346480182755908600037 473127465034266732862507)
                  ·
                    rfl

theorem cell20_1036589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_1036589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036589 prefixEnd_1036589 := by exact prefixLift 1036589
  have htrace : WordTrace (prefixWord ++ tailWord_1036589) baseStart_1036589 baseEnd_1036589 := by
    simpa [prefixWord, tailWord_1036589, baseEnd_1036589] using wordTrace_append hprefix tailTrace_1036589
  have hstable : (prefixWord ++ tailWord_1036589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036589).length < 2 ^ (prefixWord ++ tailWord_1036589).sum := by decide
  have hdescent : baseEnd_1036589 < baseStart_1036589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036593 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 4]
def baseStart_1036593 : Nat := 118140960795 + 1036593 * 2 ^ 59
def prefixEnd_1036593 : Nat := 4983230072969 + 3 ^ 40 * 1036593 * 2
def baseEnd_1036593 : Nat := 473129290743260496729157

theorem tailTrace_1036593 : CollatzResearch.WordTrace tailWord_1036593 prefixEnd_1036593 473129290743260496729157 := by
  unfold tailWord_1036593
  simp only [CollatzResearch.WordTrace]
  refine ⟨37807652733608071834954433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25205101822405381223302955 37807652733608071834954433)
  ·
    refine ⟨28355739550206053876215825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37807652733608071834954433 28355739550206053876215825)
    ·
      refine ⟨21266804662654540407161869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28355739550206053876215825 21266804662654540407161869)
      ·
        refine ⟨7975051748495452652685701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21266804662654540407161869 7975051748495452652685701)
        ·
          refine ⟨1495322202842897372378569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7975051748495452652685701 1495322202842897372378569)
          ·
            refine ⟨1121491652132173029283927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495322202842897372378569 1121491652132173029283927)
            ·
              refine ⟨1682237478198259543925891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121491652132173029283927 1682237478198259543925891)
              ·
                refine ⟨2523356217297389315888837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682237478198259543925891 2523356217297389315888837)
                ·
                  refine ⟨473129290743260496729157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523356217297389315888837 473129290743260496729157)
                  ·
                    rfl

theorem cell20_1036593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 4].length) (baseStart_1036593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036593 prefixEnd_1036593 := by exact prefixLift 1036593
  have htrace : WordTrace (prefixWord ++ tailWord_1036593) baseStart_1036593 baseEnd_1036593 := by
    simpa [prefixWord, tailWord_1036593, baseEnd_1036593] using wordTrace_append hprefix tailTrace_1036593
  have hstable : (prefixWord ++ tailWord_1036593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036593).length < 2 ^ (prefixWord ++ tailWord_1036593).sum := by decide
  have hdescent : baseEnd_1036593 < baseStart_1036593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036645 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 3]
def baseStart_1036645 : Nat := 118140960795 + 1036645 * 2 ^ 59
def prefixEnd_1036645 : Nat := 4983230072969 + 3 ^ 40 * 1036645 * 2
def baseEnd_1036645 : Nat := 473153024960179426995611

theorem tailTrace_1036645 : CollatzResearch.WordTrace tailWord_1036645 prefixEnd_1036645 473153024960179426995611 := by
  unfold tailWord_1036645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37809549329419684715847389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25206366219613123143898259 37809549329419684715847389)
  ·
    refine ⟨14178580998532381768442771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37809549329419684715847389 14178580998532381768442771)
    ·
      refine ⟨21267871497798572652664157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14178580998532381768442771 21267871497798572652664157)
      ·
        refine ⟨7975451811674464744749059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21267871497798572652664157 7975451811674464744749059)
        ·
          refine ⟨11963177717511697117123589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975451811674464744749059 11963177717511697117123589)
          ·
            refine ⟨2243095822033443209460673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11963177717511697117123589 2243095822033443209460673)
            ·
              refine ⟨1682321866525082407095505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243095822033443209460673 1682321866525082407095505)
              ·
                refine ⟨1261741399893811805321629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1682321866525082407095505 1261741399893811805321629)
                ·
                  refine ⟨473153024960179426995611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261741399893811805321629 473153024960179426995611)
                  ·
                    rfl

theorem cell20_1036645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_1036645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036645 prefixEnd_1036645 := by exact prefixLift 1036645
  have htrace : WordTrace (prefixWord ++ tailWord_1036645) baseStart_1036645 baseEnd_1036645 := by
    simpa [prefixWord, tailWord_1036645, baseEnd_1036645] using wordTrace_append hprefix tailTrace_1036645
  have hstable : (prefixWord ++ tailWord_1036645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036645).length < 2 ^ (prefixWord ++ tailWord_1036645).sum := by decide
  have hdescent : baseEnd_1036645 < baseStart_1036645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036648 : List Nat := [2, 1, 4, 2, 2, 1, 4, 2, 2]
def baseStart_1036648 : Nat := 118140960795 + 1036648 * 2 ^ 59
def prefixEnd_1036648 : Nat := 4983230072969 + 3 ^ 40 * 1036648 * 2
def baseEnd_1036648 : Nat := 473154394241924749895599

theorem tailTrace_1036648 : CollatzResearch.WordTrace tailWord_1036648 prefixEnd_1036648 473154394241924749895599 := by
  unfold tailWord_1036648
  simp only [CollatzResearch.WordTrace]
  refine ⟨18904829374204408114103299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25206439165605877485471065 18904829374204408114103299)
  ·
    refine ⟨28357244061306612171154949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18904829374204408114103299 28357244061306612171154949)
    ·
      refine ⟨5316983261494989782091553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28357244061306612171154949 5316983261494989782091553)
      ·
        refine ⟨3987737446121242336568665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5316983261494989782091553 3987737446121242336568665)
        ·
          refine ⟨2990803084590931752426499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3987737446121242336568665 2990803084590931752426499)
          ·
            refine ⟨4486204626886397628639749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2990803084590931752426499 4486204626886397628639749)
            ·
              refine ⟨841163367541199555369953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4486204626886397628639749 841163367541199555369953)
              ·
                refine ⟨630872525655899666527465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841163367541199555369953 630872525655899666527465)
                ·
                  refine ⟨473154394241924749895599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630872525655899666527465 473154394241924749895599)
                  ·
                    rfl

theorem cell20_1036648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_1036648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036648 prefixEnd_1036648 := by exact prefixLift 1036648
  have htrace : WordTrace (prefixWord ++ tailWord_1036648) baseStart_1036648 baseEnd_1036648 := by
    simpa [prefixWord, tailWord_1036648, baseEnd_1036648] using wordTrace_append hprefix tailTrace_1036648
  have hstable : (prefixWord ++ tailWord_1036648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036648).length < 2 ^ (prefixWord ++ tailWord_1036648).sum := by decide
  have hdescent : baseEnd_1036648 < baseStart_1036648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036686 : List Nat := [4, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_1036686 : Nat := 118140960795 + 1036686 * 2 ^ 59
def prefixEnd_1036686 : Nat := 4983230072969 + 3 ^ 40 * 1036686 * 2
def baseEnd_1036686 : Nat := 473171738477365506628777

theorem tailTrace_1036686 : CollatzResearch.WordTrace tailWord_1036686 prefixEnd_1036686 473171738477365506628777 := by
  unfold tailWord_1036686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4726380590283893589761239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25207363148180765812059941 4726380590283893589761239)
  ·
    refine ⟨7089570885425840384641859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4726380590283893589761239 7089570885425840384641859)
    ·
      refine ⟨10634356328138760576962789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7089570885425840384641859 10634356328138760576962789)
      ·
        refine ⟨1993941811526017608180523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10634356328138760576962789 1993941811526017608180523)
        ·
          refine ⟨2990912717289026412270785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1993941811526017608180523 2990912717289026412270785)
          ·
            refine ⟨2243184537966769809203089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2990912717289026412270785 2243184537966769809203089)
            ·
              refine ⟨1682388403475077356902317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2243184537966769809203089 1682388403475077356902317)
              ·
                refine ⟨630895651303154008838369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1682388403475077356902317 630895651303154008838369)
                ·
                  refine ⟨473171738477365506628777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630895651303154008838369 473171738477365506628777)
                  ·
                    rfl

theorem cell20_1036686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_1036686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036686 prefixEnd_1036686 := by exact prefixLift 1036686
  have htrace : WordTrace (prefixWord ++ tailWord_1036686) baseStart_1036686 baseEnd_1036686 := by
    simpa [prefixWord, tailWord_1036686, baseEnd_1036686] using wordTrace_append hprefix tailTrace_1036686
  have hstable : (prefixWord ++ tailWord_1036686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036686).length < 2 ^ (prefixWord ++ tailWord_1036686).sum := by decide
  have hdescent : baseEnd_1036686 < baseStart_1036686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036704 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_1036704 : Nat := 118140960795 + 1036704 * 2 ^ 59
def prefixEnd_1036704 : Nat := 4983230072969 + 3 ^ 40 * 1036704 * 2
def baseEnd_1036704 : Nat := 473179954167837444028703

theorem tailTrace_1036704 : CollatzResearch.WordTrace tailWord_1036704 prefixEnd_1036704 473179954167837444028703 := by
  unfold tailWord_1036704
  simp only [CollatzResearch.WordTrace]
  refine ⟨18905850618102968896122583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25207800824137291861496777 18905850618102968896122583)
  ·
    refine ⟨28358775927154453344183875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18905850618102968896122583 28358775927154453344183875)
    ·
      refine ⟨42538163890731680016275813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28358775927154453344183875 42538163890731680016275813)
      ·
        refine ⟨7975905729512190003051715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42538163890731680016275813 7975905729512190003051715)
        ·
          refine ⟨11963858594268285004577573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975905729512190003051715 11963858594268285004577573)
          ·
            refine ⟨2243223486425303438358295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11963858594268285004577573 2243223486425303438358295)
            ·
              refine ⟨3364835229637955157537443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243223486425303438358295 3364835229637955157537443)
              ·
                refine ⟨5047252844456932736306165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364835229637955157537443 5047252844456932736306165)
                ·
                  refine ⟨473179954167837444028703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5047252844456932736306165 473179954167837444028703)
                  ·
                    rfl

theorem cell20_1036704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_1036704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036704 prefixEnd_1036704 := by exact prefixLift 1036704
  have htrace : WordTrace (prefixWord ++ tailWord_1036704) baseStart_1036704 baseEnd_1036704 := by
    simpa [prefixWord, tailWord_1036704, baseEnd_1036704] using wordTrace_append hprefix tailTrace_1036704
  have hstable : (prefixWord ++ tailWord_1036704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036704).length < 2 ^ (prefixWord ++ tailWord_1036704).sum := by decide
  have hdescent : baseEnd_1036704 < baseStart_1036704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036717 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1036717 : Nat := 118140960795 + 1036717 * 2 ^ 59
def prefixEnd_1036717 : Nat := 4983230072969 + 3 ^ 40 * 1036717 * 2
def baseEnd_1036717 : Nat := 473185887722067176595317

theorem tailTrace_1036717 : CollatzResearch.WordTrace tailWord_1036717 prefixEnd_1036717 473185887722067176595317 := by
  unfold tailWord_1036717
  simp only [CollatzResearch.WordTrace]
  refine ⟨37812175385158841012468405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25208116923439227341645603 37812175385158841012468405)
  ·
    refine ⟨3544891442358641344918913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37812175385158841012468405 3544891442358641344918913)
    ·
      refine ⟨2658668581768981008689185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3544891442358641344918913 2658668581768981008689185)
      ·
        refine ⟨1994001436326735756516889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2658668581768981008689185 1994001436326735756516889)
        ·
          refine ⟨1495501077245051817387667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1994001436326735756516889 1495501077245051817387667)
          ·
            refine ⟨2243251615867577726081501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1495501077245051817387667 2243251615867577726081501)
            ·
              refine ⟨841219355950341647280563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2243251615867577726081501 841219355950341647280563)
              ·
                refine ⟨1261829033925512470920845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841219355950341647280563 1261829033925512470920845)
                ·
                  refine ⟨473185887722067176595317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261829033925512470920845 473185887722067176595317)
                  ·
                    rfl

theorem cell20_1036717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1036717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036717 prefixEnd_1036717 := by exact prefixLift 1036717
  have htrace : WordTrace (prefixWord ++ tailWord_1036717) baseStart_1036717 baseEnd_1036717 := by
    simpa [prefixWord, tailWord_1036717, baseEnd_1036717] using wordTrace_append hprefix tailTrace_1036717
  have hstable : (prefixWord ++ tailWord_1036717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036717).length < 2 ^ (prefixWord ++ tailWord_1036717).sum := by decide
  have hdescent : baseEnd_1036717 < baseStart_1036717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036737 : List Nat := [1, 2, 7, 1, 2, 1, 1, 3, 2]
def baseStart_1036737 : Nat := 118140960795 + 1036737 * 2 ^ 59
def prefixEnd_1036737 : Nat := 4983230072969 + 3 ^ 40 * 1036737 * 2
def baseEnd_1036737 : Nat := 473195016267035995928569

theorem tailTrace_1036737 : CollatzResearch.WordTrace tailWord_1036737 prefixEnd_1036737 473195016267035995928569 := by
  unfold tailWord_1036737
  simp only [CollatzResearch.WordTrace]
  refine ⟨37812904845086384428196465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25208603230057589618797643 37812904845086384428196465)
  ·
    refine ⟨28359678633814788321147349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37812904845086384428196465 28359678633814788321147349)
    ·
      refine ⟨664679967980034101276891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28359678633814788321147349 664679967980034101276891)
      ·
        refine ⟨997019951970051151915337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664679967980034101276891 997019951970051151915337)
        ·
          refine ⟨747764963977538363936503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997019951970051151915337 747764963977538363936503)
          ·
            refine ⟨1121647445966307545904755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747764963977538363936503 1121647445966307545904755)
            ·
              refine ⟨1682471168949461318857133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121647445966307545904755 1682471168949461318857133)
              ·
                refine ⟨630926688356047994571425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1682471168949461318857133 630926688356047994571425)
                ·
                  refine ⟨473195016267035995928569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 630926688356047994571425 473195016267035995928569)
                  ·
                    rfl

theorem cell20_1036737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 2].length) (baseStart_1036737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036737 prefixEnd_1036737 := by exact prefixLift 1036737
  have htrace : WordTrace (prefixWord ++ tailWord_1036737) baseStart_1036737 baseEnd_1036737 := by
    simpa [prefixWord, tailWord_1036737, baseEnd_1036737] using wordTrace_append hprefix tailTrace_1036737
  have hstable : (prefixWord ++ tailWord_1036737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036737).length < 2 ^ (prefixWord ++ tailWord_1036737).sum := by decide
  have hdescent : baseEnd_1036737 < baseStart_1036737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036776 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_1036776 : Nat := 118140960795 + 1036776 * 2 ^ 59
def prefixEnd_1036776 : Nat := 4983230072969 + 3 ^ 40 * 1036776 * 2
def baseEnd_1036776 : Nat := 473212816929725193628409

theorem tailTrace_1036776 : CollatzResearch.WordTrace tailWord_1036776 prefixEnd_1036776 473212816929725193628409 := by
  unfold tailWord_1036776
  simp only [CollatzResearch.WordTrace]
  refine ⟨18907163645972547044433091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25209551527963396059244121 18907163645972547044433091)
  ·
    refine ⟨28360745468958820566649637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18907163645972547044433091 28360745468958820566649637)
    ·
      refine ⟨5317639775429778856246807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28360745468958820566649637 5317639775429778856246807)
      ·
        refine ⟨7976459663144668284370211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317639775429778856246807 7976459663144668284370211)
        ·
          refine ⟨11964689494717002426555317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976459663144668284370211 11964689494717002426555317)
          ·
            refine ⟨1121689640129718977489561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11964689494717002426555317 1121689640129718977489561)
            ·
              refine ⟨841267230097289233117171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1121689640129718977489561 841267230097289233117171)
              ·
                refine ⟨1261900845145933849675757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841267230097289233117171 1261900845145933849675757)
                ·
                  refine ⟨473212816929725193628409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261900845145933849675757 473212816929725193628409)
                  ·
                    rfl

theorem cell20_1036776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_1036776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036776 prefixEnd_1036776 := by exact prefixLift 1036776
  have htrace : WordTrace (prefixWord ++ tailWord_1036776) baseStart_1036776 baseEnd_1036776 := by
    simpa [prefixWord, tailWord_1036776, baseEnd_1036776] using wordTrace_append hprefix tailTrace_1036776
  have hstable : (prefixWord ++ tailWord_1036776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036776).length < 2 ^ (prefixWord ++ tailWord_1036776).sum := by decide
  have hdescent : baseEnd_1036776 < baseStart_1036776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036780 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1036780 : Nat := 118140960795 + 1036780 * 2 ^ 59
def prefixEnd_1036780 : Nat := 4983230072969 + 3 ^ 40 * 1036780 * 2
def baseEnd_1036780 : Nat := 473214642638718957495059

theorem tailTrace_1036780 : CollatzResearch.WordTrace tailWord_1036780 prefixEnd_1036780 473214642638718957495059 := by
  unfold tailWord_1036780
  simp only [CollatzResearch.WordTrace]
  refine ⟨18907236591965301386005897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25209648789287068514674529 18907236591965301386005897)
  ·
    refine ⟨14180427443973976039504423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18907236591965301386005897 14180427443973976039504423)
    ·
      refine ⟨21270641165960964059256635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14180427443973976039504423 21270641165960964059256635)
      ·
        refine ⟨31905961748941446088884953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21270641165960964059256635 31905961748941446088884953)
        ·
          refine ⟨23929471311706084566663715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31905961748941446088884953 23929471311706084566663715)
          ·
            refine ⟨35894206967559126849995573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23929471311706084566663715 35894206967559126849995573)
            ·
              refine ⟨3365081903208668142187085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35894206967559126849995573 3365081903208668142187085)
              ·
                refine ⟨1261905713703250553320157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3365081903208668142187085 1261905713703250553320157)
                ·
                  refine ⟨473214642638718957495059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1261905713703250553320157 473214642638718957495059)
                  ·
                    rfl

theorem cell20_1036780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1036780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036780 prefixEnd_1036780 := by exact prefixLift 1036780
  have htrace : WordTrace (prefixWord ++ tailWord_1036780) baseStart_1036780 baseEnd_1036780 := by
    simpa [prefixWord, tailWord_1036780, baseEnd_1036780] using wordTrace_append hprefix tailTrace_1036780
  have hstable : (prefixWord ++ tailWord_1036780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036780).length < 2 ^ (prefixWord ++ tailWord_1036780).sum := by decide
  have hdescent : baseEnd_1036780 < baseStart_1036780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036842 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_1036842 : Nat := 118140960795 + 1036842 * 2 ^ 59
def prefixEnd_1036842 : Nat := 4983230072969 + 3 ^ 40 * 1036842 * 2
def baseEnd_1036842 : Nat := 473242941128122297428139

theorem tailTrace_1036842 : CollatzResearch.WordTrace tailWord_1036842 prefixEnd_1036842 473242941128122297428139 := by
  unfold tailWord_1036842
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454183627426496840192195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25211156339803991573845853 9454183627426496840192195)
  ·
    refine ⟨14181275441139745260288293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9454183627426496840192195 14181275441139745260288293)
    ·
      refine ⟨2658989145213702236304055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14181275441139745260288293 2658989145213702236304055)
      ·
        refine ⟨3988483717820553354456083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658989145213702236304055 3988483717820553354456083)
        ·
          refine ⟨5982725576730830031684125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988483717820553354456083 5982725576730830031684125)
          ·
            refine ⟨2243522091274061261881547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5982725576730830031684125 2243522091274061261881547)
            ·
              refine ⟨3365283136911091892822321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243522091274061261881547 3365283136911091892822321)
              ·
                refine ⟨2523962352683318919616741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3365283136911091892822321 2523962352683318919616741)
                ·
                  refine ⟨473242941128122297428139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2523962352683318919616741 473242941128122297428139)
                  ·
                    rfl

theorem cell20_1036842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_1036842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036842 prefixEnd_1036842 := by exact prefixLift 1036842
  have htrace : WordTrace (prefixWord ++ tailWord_1036842) baseStart_1036842 baseEnd_1036842 := by
    simpa [prefixWord, tailWord_1036842, baseEnd_1036842] using wordTrace_append hprefix tailTrace_1036842
  have hstable : (prefixWord ++ tailWord_1036842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036842).length < 2 ^ (prefixWord ++ tailWord_1036842).sum := by decide
  have hdescent : baseEnd_1036842 < baseStart_1036842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036914 : List Nat := [3, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_1036914 : Nat := 118140960795 + 1036914 * 2 ^ 59
def prefixEnd_1036914 : Nat := 4983230072969 + 3 ^ 40 * 1036914 * 2
def baseEnd_1036914 : Nat := 473275803890010047027845

theorem tailTrace_1036914 : CollatzResearch.WordTrace tailWord_1036914 prefixEnd_1036914 473275803890010047027845 := by
  unfold tailWord_1036914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454840141361285914347449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25212907043630095771593197 9454840141361285914347449)
  ·
    refine ⟨7091130106020964435760587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9454840141361285914347449 7091130106020964435760587)
    ·
      refine ⟨10636695159031446653640881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7091130106020964435760587 10636695159031446653640881)
      ·
        refine ⟨7977521369273584990230661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10636695159031446653640881 7977521369273584990230661)
        ·
          refine ⟨1495785256738797185668249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7977521369273584990230661 1495785256738797185668249)
          ·
            refine ⟨1121838942554097889251187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495785256738797185668249 1121838942554097889251187)
            ·
              refine ⟨1682758413831146833876781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121838942554097889251187 1682758413831146833876781)
              ·
                refine ⟨631034405186680062703793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1682758413831146833876781 631034405186680062703793)
                ·
                  refine ⟨473275803890010047027845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631034405186680062703793 473275803890010047027845)
                  ·
                    rfl

theorem cell20_1036914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_1036914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036914 prefixEnd_1036914 := by exact prefixLift 1036914
  have htrace : WordTrace (prefixWord ++ tailWord_1036914) baseStart_1036914 baseEnd_1036914 := by
    simpa [prefixWord, tailWord_1036914, baseEnd_1036914] using wordTrace_append hprefix tailTrace_1036914
  have hstable : (prefixWord ++ tailWord_1036914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036914).length < 2 ^ (prefixWord ++ tailWord_1036914).sum := by decide
  have hdescent : baseEnd_1036914 < baseStart_1036914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036925 : List Nat := [1, 4, 1, 1, 5, 2, 6]
def baseStart_1036925 : Nat := 118140960795 + 1036925 * 2 ^ 59
def prefixEnd_1036925 : Nat := 4983230072969 + 3 ^ 40 * 1036925 * 2
def baseEnd_1036925 : Nat := 52586758287749210851237

theorem tailTrace_1036925 : CollatzResearch.WordTrace tailWord_1036925 prefixEnd_1036925 52586758287749210851237 := by
  unfold tailWord_1036925
  simp only [CollatzResearch.WordTrace]
  refine ⟨37819761768405292536040229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25213174512270195024026819 37819761768405292536040229)
  ·
    refine ⟨7091205331575992350507543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37819761768405292536040229 7091205331575992350507543)
    ·
      refine ⟨10636807997363988525761315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7091205331575992350507543 10636807997363988525761315)
      ·
        refine ⟨15955211996045982788641973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10636807997363988525761315 15955211996045982788641973)
        ·
          refine ⟨1495801124629310886435185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15955211996045982788641973 1495801124629310886435185)
          ·
            refine ⟨1121850843471983164826389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1495801124629310886435185 1121850843471983164826389)
            ·
              refine ⟨52586758287749210851237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1121850843471983164826389 52586758287749210851237)
              ·
                rfl

theorem cell20_1036925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 6].length) (baseStart_1036925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036925 prefixEnd_1036925 := by exact prefixLift 1036925
  have htrace : WordTrace (prefixWord ++ tailWord_1036925) baseStart_1036925 baseEnd_1036925 := by
    simpa [prefixWord, tailWord_1036925, baseEnd_1036925] using wordTrace_append hprefix tailTrace_1036925
  have hstable : (prefixWord ++ tailWord_1036925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036925).length < 2 ^ (prefixWord ++ tailWord_1036925).sum := by decide
  have hdescent : baseEnd_1036925 < baseStart_1036925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036932 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1036932 : Nat := 118140960795 + 1036932 * 2 ^ 59
def prefixEnd_1036932 : Nat := 4983230072969 + 3 ^ 40 * 1036932 * 2
def baseEnd_1036932 : Nat := 473284019580481984427771

theorem tailTrace_1036932 : CollatzResearch.WordTrace tailWord_1036932 prefixEnd_1036932 473284019580481984427771 := by
  unfold tailWord_1036932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18910008539689966365772525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25213344719586621821030033 18910008539689966365772525)
  ·
    refine ⟨7091253202383737387164697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18910008539689966365772525 7091253202383737387164697)
    ·
      refine ⟨5318439901787803040373523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7091253202383737387164697 5318439901787803040373523)
      ·
        refine ⟨7977659852681704560560285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318439901787803040373523 7977659852681704560560285)
        ·
          refine ⟨2991622444755639210210107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7977659852681704560560285 2991622444755639210210107)
          ·
            refine ⟨4487433667133458815315161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991622444755639210210107 4487433667133458815315161)
            ·
              refine ⟨3365575250350094111486371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487433667133458815315161 3365575250350094111486371)
              ·
                refine ⟨5048362875525141167229557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365575250350094111486371 5048362875525141167229557)
                ·
                  refine ⟨473284019580481984427771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5048362875525141167229557 473284019580481984427771)
                  ·
                    rfl

theorem cell20_1036932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1036932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036932 prefixEnd_1036932 := by exact prefixLift 1036932
  have htrace : WordTrace (prefixWord ++ tailWord_1036932) baseStart_1036932 baseEnd_1036932 := by
    simpa [prefixWord, tailWord_1036932, baseEnd_1036932] using wordTrace_append hprefix tailTrace_1036932
  have hstable : (prefixWord ++ tailWord_1036932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036932).length < 2 ^ (prefixWord ++ tailWord_1036932).sum := by decide
  have hdescent : baseEnd_1036932 < baseStart_1036932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1036935 : List Nat := [1, 1, 4, 2, 1, 2, 5, 2, 2]
def baseStart_1036935 : Nat := 118140960795 + 1036935 * 2 ^ 59
def prefixEnd_1036935 : Nat := 4983230072969 + 3 ^ 40 * 1036935 * 2
def baseEnd_1036935 : Nat := 473285388862227307327759

theorem tailTrace_1036935 : CollatzResearch.WordTrace tailWord_1036935 prefixEnd_1036935 473285388862227307327759 := by
  unfold tailWord_1036935
  simp only [CollatzResearch.WordTrace]
  refine ⟨37820126498369064243904259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25213417665579376162602839 37820126498369064243904259)
  ·
    refine ⟨56730189747553596365856389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37820126498369064243904259 56730189747553596365856389)
    ·
      refine ⟨10636910577666299318598073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56730189747553596365856389 10636910577666299318598073)
      ·
        refine ⟨7977682933249724488948555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10636910577666299318598073 7977682933249724488948555)
        ·
          refine ⟨11966524399874586733422833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977682933249724488948555 11966524399874586733422833)
          ·
            refine ⟨8974893299905940050067125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11966524399874586733422833 8974893299905940050067125)
            ·
              refine ⟨841396246866181879693793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8974893299905940050067125 841396246866181879693793)
              ·
                refine ⟨631047185149636409770345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841396246866181879693793 631047185149636409770345)
                ·
                  refine ⟨473285388862227307327759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631047185149636409770345 473285388862227307327759)
                  ·
                    rfl

theorem cell20_1036935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 2].length) (baseStart_1036935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1036935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1036935 prefixEnd_1036935 := by exact prefixLift 1036935
  have htrace : WordTrace (prefixWord ++ tailWord_1036935) baseStart_1036935 baseEnd_1036935 := by
    simpa [prefixWord, tailWord_1036935, baseEnd_1036935] using wordTrace_append hprefix tailTrace_1036935
  have hstable : (prefixWord ++ tailWord_1036935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1036935).length < 2 ^ (prefixWord ++ tailWord_1036935).sum := by decide
  have hdescent : baseEnd_1036935 < baseStart_1036935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1036935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037015 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_1037015 : Nat := 118140960795 + 1037015 * 2 ^ 59
def prefixEnd_1037015 : Nat := 4983230072969 + 3 ^ 40 * 1037015 * 2
def baseEnd_1037015 : Nat := 473321903042102584660765

theorem tailTrace_1037015 : CollatzResearch.WordTrace tailWord_1037015 prefixEnd_1037015 473321903042102584660765 := by
  unfold tailWord_1037015
  simp only [CollatzResearch.WordTrace]
  refine ⟨37823044338079237906816499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25215362892052825271210999 37823044338079237906816499)
  ·
    refine ⟨56734566507118856860224749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37823044338079237906816499 56734566507118856860224749)
    ·
      refine ⟨21275462440169571322584281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56734566507118856860224749 21275462440169571322584281)
      ·
        refine ⟨15956596830127178491938211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21275462440169571322584281 15956596830127178491938211)
        ·
          refine ⟨23934895245190767737907317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15956596830127178491938211 23934895245190767737907317)
          ·
            refine ⟨2243896429236634475428811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23934895245190767737907317 2243896429236634475428811)
            ·
              refine ⟨3365844643854951713143217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2243896429236634475428811 3365844643854951713143217)
              ·
                refine ⟨2524383482891213784857413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3365844643854951713143217 2524383482891213784857413)
                ·
                  refine ⟨473321903042102584660765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2524383482891213784857413 473321903042102584660765)
                  ·
                    rfl

theorem cell20_1037015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_1037015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037015 prefixEnd_1037015 := by exact prefixLift 1037015
  have htrace : WordTrace (prefixWord ++ tailWord_1037015) baseStart_1037015 baseEnd_1037015 := by
    simpa [prefixWord, tailWord_1037015, baseEnd_1037015] using wordTrace_append hprefix tailTrace_1037015
  have hstable : (prefixWord ++ tailWord_1037015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037015).length < 2 ^ (prefixWord ++ tailWord_1037015).sum := by decide
  have hdescent : baseEnd_1037015 < baseStart_1037015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037036 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1037036 : Nat := 118140960795 + 1037036 * 2 ^ 59
def prefixEnd_1037036 : Nat := 4983230072969 + 3 ^ 40 * 1037036 * 2
def baseEnd_1037036 : Nat := 473331488014319844960679

theorem tailTrace_1037036 : CollatzResearch.WordTrace tailWord_1037036 prefixEnd_1037036 473331488014319844960679 := by
  unfold tailWord_1037036
  simp only [CollatzResearch.WordTrace]
  refine ⟨18911905135501579246665481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25215873514002105662220641 18911905135501579246665481)
  ·
    refine ⟨14183928851626184434999111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18911905135501579246665481 14183928851626184434999111)
    ·
      refine ⟨21275893277439276652498667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14183928851626184434999111 21275893277439276652498667)
      ·
        refine ⟨31913839916158914978748001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21275893277439276652498667 31913839916158914978748001)
        ·
          refine ⟨23935379937119186234061001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31913839916158914978748001 23935379937119186234061001)
          ·
            refine ⟨17951534952839389675545751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23935379937119186234061001 17951534952839389675545751)
            ·
              refine ⟨26927302429259084513318627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17951534952839389675545751 26927302429259084513318627)
              ·
                refine ⟨40390953643888626769977941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26927302429259084513318627 40390953643888626769977941)
                ·
                  refine ⟨473331488014319844960679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40390953643888626769977941 473331488014319844960679)
                  ·
                    rfl

theorem cell20_1037036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1037036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037036 prefixEnd_1037036 := by exact prefixLift 1037036
  have htrace : WordTrace (prefixWord ++ tailWord_1037036) baseStart_1037036 baseEnd_1037036 := by
    simpa [prefixWord, tailWord_1037036, baseEnd_1037036] using wordTrace_append hprefix tailTrace_1037036
  have hstable : (prefixWord ++ tailWord_1037036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037036).length < 2 ^ (prefixWord ++ tailWord_1037036).sum := by decide
  have hdescent : baseEnd_1037036 < baseStart_1037036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037046 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1037046 : Nat := 118140960795 + 1037046 * 2 ^ 59
def prefixEnd_1037046 : Nat := 4983230072969 + 3 ^ 40 * 1037046 * 2
def baseEnd_1037046 : Nat := 473336052286804254627305

theorem tailTrace_1037046 : CollatzResearch.WordTrace tailWord_1037046 prefixEnd_1037046 473336052286804254627305 := by
  unfold tailWord_1037046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364010937560433137574687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25216116667311286800796661 2364010937560433137574687)
  ·
    refine ⟨3546016406340649706362031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364010937560433137574687 3546016406340649706362031)
    ·
      refine ⟨5319024609510974559543047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546016406340649706362031 5319024609510974559543047)
      ·
        refine ⟨7978536914266461839314571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319024609510974559543047 7978536914266461839314571)
        ·
          refine ⟨11967805371399692758971857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7978536914266461839314571 11967805371399692758971857)
          ·
            refine ⟨8975854028549769569228893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11967805371399692758971857 8975854028549769569228893)
            ·
              refine ⟨3365945260706163588460835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8975854028549769569228893 3365945260706163588460835)
              ·
                refine ⟨5048917891059245382691253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365945260706163588460835 5048917891059245382691253)
                ·
                  refine ⟨473336052286804254627305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5048917891059245382691253 473336052286804254627305)
                  ·
                    rfl

theorem cell20_1037046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1037046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037046 prefixEnd_1037046 := by exact prefixLift 1037046
  have htrace : WordTrace (prefixWord ++ tailWord_1037046) baseStart_1037046 baseEnd_1037046 := by
    simpa [prefixWord, tailWord_1037046, baseEnd_1037046] using wordTrace_append hprefix tailTrace_1037046
  have hstable : (prefixWord ++ tailWord_1037046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037046).length < 2 ^ (prefixWord ++ tailWord_1037046).sum := by decide
  have hdescent : baseEnd_1037046 < baseStart_1037046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037053 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1037053 : Nat := 118140960795 + 1037053 * 2 ^ 59
def prefixEnd_1037053 : Nat := 4983230072969 + 3 ^ 40 * 1037053 * 2
def baseEnd_1037053 : Nat := 473339247277543341393943

theorem tailTrace_1037053 : CollatzResearch.WordTrace tailWord_1037053 prefixEnd_1037053 473339247277543341393943 := by
  unfold tailWord_1037053
  simp only [CollatzResearch.WordTrace]
  refine ⟨37824430311941570396699813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25216286874627713597799875 37824430311941570396699813)
  ·
    refine ⟨7092080683489044449381215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37824430311941570396699813 7092080683489044449381215)
    ·
      refine ⟨10638121025233566674071823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7092080683489044449381215 10638121025233566674071823)
      ·
        refine ⟨15957181537850350011107735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10638121025233566674071823 15957181537850350011107735)
        ·
          refine ⟨23935772306775525016661603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15957181537850350011107735 23935772306775525016661603)
          ·
            refine ⟨35903658460163287524992405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23935772306775525016661603 35903658460163287524992405)
            ·
              refine ⟨1682983990320154102734019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35903658460163287524992405 1682983990320154102734019)
              ·
                refine ⟨2524475985480231154101029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1682983990320154102734019 2524475985480231154101029)
                ·
                  refine ⟨473339247277543341393943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2524475985480231154101029 473339247277543341393943)
                  ·
                    rfl

theorem cell20_1037053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1037053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037053 prefixEnd_1037053 := by exact prefixLift 1037053
  have htrace : WordTrace (prefixWord ++ tailWord_1037053) baseStart_1037053 baseEnd_1037053 := by
    simpa [prefixWord, tailWord_1037053, baseEnd_1037053] using wordTrace_append hprefix tailTrace_1037053
  have hstable : (prefixWord ++ tailWord_1037053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037053).length < 2 ^ (prefixWord ++ tailWord_1037053).sum := by decide
  have hdescent : baseEnd_1037053 < baseStart_1037053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037060 : List Nat := [2, 3, 2, 2, 1, 1, 2, 7]
def baseStart_1037060 : Nat := 118140960795 + 1037060 * 2 ^ 59
def prefixEnd_1037060 : Nat := 4983230072969 + 3 ^ 40 * 1037060 * 2
def baseEnd_1037060 : Nat := 157780814089427476053527

theorem tailTrace_1037060 : CollatzResearch.WordTrace tailWord_1037060 prefixEnd_1037060 157780814089427476053527 := by
  unfold tailWord_1037060
  simp only [CollatzResearch.WordTrace]
  refine ⟨18912342811458105296102317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25216457081944140394803089 18912342811458105296102317)
  ·
    refine ⟨7092128554296789486038369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18912342811458105296102317 7092128554296789486038369)
    ·
      refine ⟨5319096415722592114528777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7092128554296789486038369 5319096415722592114528777)
      ·
        refine ⟨3989322311791944085896583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5319096415722592114528777 3989322311791944085896583)
        ·
          refine ⟨5983983467687916128844875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989322311791944085896583 5983983467687916128844875)
          ·
            refine ⟨8975975201531874193267313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983983467687916128844875 8975975201531874193267313)
            ·
              refine ⟨6731981401148905644950485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8975975201531874193267313 6731981401148905644950485)
              ·
                refine ⟨157780814089427476053527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6731981401148905644950485 157780814089427476053527)
                ·
                  rfl

theorem cell20_1037060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_1037060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037060 prefixEnd_1037060 := by exact prefixLift 1037060
  have htrace : WordTrace (prefixWord ++ tailWord_1037060) baseStart_1037060 baseEnd_1037060 := by
    simpa [prefixWord, tailWord_1037060, baseEnd_1037060] using wordTrace_append hprefix tailTrace_1037060
  have hstable : (prefixWord ++ tailWord_1037060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037060).length < 2 ^ (prefixWord ++ tailWord_1037060).sum := by decide
  have hdescent : baseEnd_1037060 < baseStart_1037060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037087 : List Nat := [1, 1, 2, 4, 2, 4, 1, 3, 2]
def baseStart_1037087 : Nat := 118140960795 + 1037087 * 2 ^ 59
def prefixEnd_1037087 : Nat := 4983230072969 + 3 ^ 40 * 1037087 * 2
def baseEnd_1037087 : Nat := 473354765803990334260471

theorem tailTrace_1037087 : CollatzResearch.WordTrace tailWord_1037087 prefixEnd_1037087 473354765803990334260471 := by
  unfold tailWord_1037087
  simp only [CollatzResearch.WordTrace]
  refine ⟨37825670393818394203437515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25217113595878929468958343 37825670393818394203437515)
  ·
    refine ⟨56738505590727591305156273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37825670393818394203437515 56738505590727591305156273)
    ·
      refine ⟨42553879193045693478867205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56738505590727591305156273 42553879193045693478867205)
      ·
        refine ⟨7978852348696067527287601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42553879193045693478867205 7978852348696067527287601)
        ·
          refine ⟨5984139261522050645465701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7978852348696067527287601 5984139261522050645465701)
          ·
            refine ⟨1122026111535384496024819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5984139261522050645465701 1122026111535384496024819)
            ·
              refine ⟨1683039167303076744037229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122026111535384496024819 1683039167303076744037229)
              ·
                refine ⟨631139687738653779013961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683039167303076744037229 631139687738653779013961)
                ·
                  refine ⟨473354765803990334260471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631139687738653779013961 473354765803990334260471)
                  ·
                    rfl

theorem cell20_1037087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 2].length) (baseStart_1037087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037087 prefixEnd_1037087 := by exact prefixLift 1037087
  have htrace : WordTrace (prefixWord ++ tailWord_1037087) baseStart_1037087 baseEnd_1037087 := by
    simpa [prefixWord, tailWord_1037087, baseEnd_1037087] using wordTrace_append hprefix tailTrace_1037087
  have hstable : (prefixWord ++ tailWord_1037087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037087).length < 2 ^ (prefixWord ++ tailWord_1037087).sum := by decide
  have hdescent : baseEnd_1037087 < baseStart_1037087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037105 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1037105 : Nat := 118140960795 + 1037105 * 2 ^ 59
def prefixEnd_1037105 : Nat := 4983230072969 + 3 ^ 40 * 1037105 * 2
def baseEnd_1037105 : Nat := 473362981494462271660397

theorem tailTrace_1037105 : CollatzResearch.WordTrace tailWord_1037105 prefixEnd_1037105 473362981494462271660397 := by
  unfold tailWord_1037105
  simp only [CollatzResearch.WordTrace]
  refine ⟨37826326907753183277592769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25217551271835455518395179 37826326907753183277592769)
  ·
    refine ⟨28369745180814887458194577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37826326907753183277592769 28369745180814887458194577)
    ·
      refine ⟨21277308885611165593645933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28369745180814887458194577 21277308885611165593645933)
      ·
        refine ⟨7978990832104187097617225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21277308885611165593645933 7978990832104187097617225)
        ·
          refine ⟨5984243124078140323212919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7978990832104187097617225 5984243124078140323212919)
          ·
            refine ⟨8976364686117210484819379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984243124078140323212919 8976364686117210484819379)
            ·
              refine ⟨13464547029175815727229069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976364686117210484819379 13464547029175815727229069)
              ·
                refine ⟨5049205135940930897710901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13464547029175815727229069 5049205135940930897710901)
                ·
                  refine ⟨473362981494462271660397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5049205135940930897710901 473362981494462271660397)
                  ·
                    rfl

theorem cell20_1037105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1037105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037105 prefixEnd_1037105 := by exact prefixLift 1037105
  have htrace : WordTrace (prefixWord ++ tailWord_1037105) baseStart_1037105 baseEnd_1037105 := by
    simpa [prefixWord, tailWord_1037105, baseEnd_1037105] using wordTrace_append hprefix tailTrace_1037105
  have hstable : (prefixWord ++ tailWord_1037105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037105).length < 2 ^ (prefixWord ++ tailWord_1037105).sum := by decide
  have hdescent : baseEnd_1037105 < baseStart_1037105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037160 : List Nat := [2, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_1037160 : Nat := 118140960795 + 1037160 * 2 ^ 59
def prefixEnd_1037160 : Nat := 4983230072969 + 3 ^ 40 * 1037160 * 2
def baseEnd_1037160 : Nat := 473388084993126524826839

theorem tailTrace_1037160 : CollatzResearch.WordTrace tailWord_1037160 prefixEnd_1037160 473388084993126524826839 := by
  unfold tailWord_1037160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18914166461276963835422467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25218888615035951780563289 18914166461276963835422467)
  ·
    refine ⟨28371249691915445753133701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18914166461276963835422467 28371249691915445753133701)
    ·
      refine ⟨5319609317234146078712569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28371249691915445753133701 5319609317234146078712569)
      ·
        refine ⟨3989706987925609559034427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5319609317234146078712569 3989706987925609559034427)
        ·
          refine ⟨5984560481888414338551641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989706987925609559034427 5984560481888414338551641)
          ·
            refine ⟨4488420361416310753913731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5984560481888414338551641 4488420361416310753913731)
            ·
              refine ⟨6732630542124466130870597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488420361416310753913731 6732630542124466130870597)
              ·
                refine ⟨1262368226648337399538237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6732630542124466130870597 1262368226648337399538237)
                ·
                  refine ⟨473388084993126524826839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262368226648337399538237 473388084993126524826839)
                  ·
                    rfl

theorem cell20_1037160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_1037160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037160 prefixEnd_1037160 := by exact prefixLift 1037160
  have htrace : WordTrace (prefixWord ++ tailWord_1037160) baseStart_1037160 baseEnd_1037160 := by
    simpa [prefixWord, tailWord_1037160, baseEnd_1037160] using wordTrace_append hprefix tailTrace_1037160
  have hstable : (prefixWord ++ tailWord_1037160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037160).length < 2 ^ (prefixWord ++ tailWord_1037160).sum := by decide
  have hdescent : baseEnd_1037160 < baseStart_1037160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037191 : List Nat := [1, 1, 4, 2, 3, 2, 3, 4]
def baseStart_1037191 : Nat := 118140960795 + 1037191 * 2 ^ 59
def prefixEnd_1037191 : Nat := 4983230072969 + 3 ^ 40 * 1037191 * 2
def baseEnd_1037191 : Nat := 157800744745942731597793

theorem tailTrace_1037191 : CollatzResearch.WordTrace tailWord_1037191 prefixEnd_1037191 157800744745942731597793 := by
  unfold tailWord_1037191
  simp only [CollatzResearch.WordTrace]
  refine ⟨37829463585441619965223427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25219642390294413310148951 37829463585441619965223427)
  ·
    refine ⟨56744195378162429947835141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37829463585441619965223427 56744195378162429947835141)
    ·
      refine ⟨10639536633405455615219089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56744195378162429947835141 10639536633405455615219089)
      ·
        refine ⟨7979652475054091711414317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10639536633405455615219089 7979652475054091711414317)
        ·
          refine ⟨2992369678145284391780369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7979652475054091711414317 2992369678145284391780369)
          ·
            refine ⟨2244277258608963293835277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2992369678145284391780369 2244277258608963293835277)
            ·
              refine ⟨841603971978361235188229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2244277258608963293835277 841603971978361235188229)
              ·
                refine ⟨157800744745942731597793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841603971978361235188229 157800744745942731597793)
                ·
                  rfl

theorem cell20_1037191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_1037191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037191 prefixEnd_1037191 := by exact prefixLift 1037191
  have htrace : WordTrace (prefixWord ++ tailWord_1037191) baseStart_1037191 baseEnd_1037191 := by
    simpa [prefixWord, tailWord_1037191, baseEnd_1037191] using wordTrace_append hprefix tailTrace_1037191
  have hstable : (prefixWord ++ tailWord_1037191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037191).length < 2 ^ (prefixWord ++ tailWord_1037191).sum := by decide
  have hdescent : baseEnd_1037191 < baseStart_1037191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037195 : List Nat := [1, 1, 1, 1, 4, 2, 2, 8]
def baseStart_1037195 : Nat := 118140960795 + 1037195 * 2 ^ 59
def prefixEnd_1037195 : Nat := 4983230072969 + 3 ^ 40 * 1037195 * 2
def baseEnd_1037195 : Nat := 157801353315607319553343

theorem tailTrace_1037195 : CollatzResearch.WordTrace tailWord_1037195 prefixEnd_1037195 157801353315607319553343 := by
  unfold tailWord_1037195
  simp only [CollatzResearch.WordTrace]
  refine ⟨37829609477427128648369039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25219739651618085765579359 37829609477427128648369039)
  ·
    refine ⟨56744414216140692972553559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37829609477427128648369039 56744414216140692972553559)
    ·
      refine ⟨85116621324211039458830339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56744414216140692972553559 85116621324211039458830339)
      ·
        refine ⟨127674931986316559188245509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85116621324211039458830339 127674931986316559188245509)
        ·
          refine ⟨23939049747434354847796033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127674931986316559188245509 23939049747434354847796033)
          ·
            refine ⟨17954287310575766135847025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23939049747434354847796033 17954287310575766135847025)
            ·
              refine ⟨13465715482931824601885269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17954287310575766135847025 13465715482931824601885269)
              ·
                refine ⟨157801353315607319553343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13465715482931824601885269 157801353315607319553343)
                ·
                  rfl

theorem cell20_1037195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_1037195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037195 prefixEnd_1037195 := by exact prefixLift 1037195
  have htrace : WordTrace (prefixWord ++ tailWord_1037195) baseStart_1037195 baseEnd_1037195 := by
    simpa [prefixWord, tailWord_1037195, baseEnd_1037195] using wordTrace_append hprefix tailTrace_1037195
  have hstable : (prefixWord ++ tailWord_1037195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037195).length < 2 ^ (prefixWord ++ tailWord_1037195).sum := by decide
  have hdescent : baseEnd_1037195 < baseStart_1037195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037215 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 3]
def baseStart_1037215 : Nat := 118140960795 + 1037215 * 2 ^ 59
def prefixEnd_1037215 : Nat := 4983230072969 + 3 ^ 40 * 1037215 * 2
def baseEnd_1037215 : Nat := 473413188491790777993281

theorem tailTrace_1037215 : CollatzResearch.WordTrace tailWord_1037215 prefixEnd_1037215 473413188491790777993281 := by
  unfold tailWord_1037215
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830338937354672064097099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25220225958236448042731399 37830338937354672064097099)
  ·
    refine ⟨56745508406032008096145649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37830338937354672064097099 56745508406032008096145649)
    ·
      refine ⟨42559131304524006072109237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56745508406032008096145649 42559131304524006072109237)
      ·
        refine ⟨3989918559799125569260241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42559131304524006072109237 3989918559799125569260241)
        ·
          refine ⟨2992438919849344176945181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3989918559799125569260241 2992438919849344176945181)
          ·
            refine ⟨1122164594943504066354443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2992438919849344176945181 1122164594943504066354443)
            ·
              refine ⟨1683246892415256099531665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122164594943504066354443 1683246892415256099531665)
              ·
                refine ⟨1262435169311442074648749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683246892415256099531665 1262435169311442074648749)
                ·
                  refine ⟨473413188491790777993281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262435169311442074648749 473413188491790777993281)
                  ·
                    rfl

theorem cell20_1037215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_1037215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037215 prefixEnd_1037215 := by exact prefixLift 1037215
  have htrace : WordTrace (prefixWord ++ tailWord_1037215) baseStart_1037215 baseEnd_1037215 := by
    simpa [prefixWord, tailWord_1037215, baseEnd_1037215] using wordTrace_append hprefix tailTrace_1037215
  have hstable : (prefixWord ++ tailWord_1037215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037215).length < 2 ^ (prefixWord ++ tailWord_1037215).sum := by decide
  have hdescent : baseEnd_1037215 < baseStart_1037215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037256 : List Nat := [2, 1, 3, 1, 6, 1, 1, 3, 2]
def baseStart_1037256 : Nat := 118140960795 + 1037256 * 2 ^ 59
def prefixEnd_1037256 : Nat := 4983230072969 + 3 ^ 40 * 1037256 * 2
def baseEnd_1037256 : Nat := 473431902008976857626447

theorem tailTrace_1037256 : CollatzResearch.WordTrace tailWord_1037256 prefixEnd_1037256 473431902008976857626447 := by
  unfold tailWord_1037256
  simp only [CollatzResearch.WordTrace]
  refine ⟨18915917165103068033169811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25221222886804090710893081 18915917165103068033169811)
  ·
    refine ⟨28373875747654602049754717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18915917165103068033169811 28373875747654602049754717)
    ·
      refine ⟨10640203405370475768658019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28373875747654602049754717 10640203405370475768658019)
      ·
        refine ⟨15960305108055713652987029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10640203405370475768658019 15960305108055713652987029)
        ·
          refine ⟨748139301940111577483767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15960305108055713652987029 748139301940111577483767)
          ·
            refine ⟨1122208952910167366225651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748139301940111577483767 1122208952910167366225651)
            ·
              refine ⟨1683313429365251049338477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122208952910167366225651 1683313429365251049338477)
              ·
                refine ⟨631242536011969143501929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683313429365251049338477 631242536011969143501929)
                ·
                  refine ⟨473431902008976857626447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631242536011969143501929 473431902008976857626447)
                  ·
                    rfl

theorem cell20_1037256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_1037256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037256 prefixEnd_1037256 := by exact prefixLift 1037256
  have htrace : WordTrace (prefixWord ++ tailWord_1037256) baseStart_1037256 baseEnd_1037256 := by
    simpa [prefixWord, tailWord_1037256, baseEnd_1037256] using wordTrace_append hprefix tailTrace_1037256
  have hstable : (prefixWord ++ tailWord_1037256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037256).length < 2 ^ (prefixWord ++ tailWord_1037256).sum := by decide
  have hdescent : baseEnd_1037256 < baseStart_1037256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037336 : List Nat := [2, 1, 2, 3, 2, 3, 1, 4, 2]
def baseStart_1037336 : Nat := 118140960795 + 1037336 * 2 ^ 59
def prefixEnd_1037336 : Nat := 4983230072969 + 3 ^ 40 * 1037336 * 2
def baseEnd_1037336 : Nat := 473468416188852134959453

theorem tailTrace_1037336 : CollatzResearch.WordTrace tailWord_1037336 prefixEnd_1037336 473468416188852134959453 := by
  unfold tailWord_1037336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18917376084958154864625931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25223168113277539819501241 18917376084958154864625931)
  ·
    refine ⟨28376064127437232296938897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18917376084958154864625931 28376064127437232296938897)
    ·
      refine ⟨21282048095577924222704173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28376064127437232296938897 21282048095577924222704173)
      ·
        refine ⟨7980768035841721583514065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21282048095577924222704173 7980768035841721583514065)
        ·
          refine ⟨5985576026881291187635549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7980768035841721583514065 5985576026881291187635549)
          ·
            refine ⟨2244591010080484195363331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5985576026881291187635549 2244591010080484195363331)
            ·
              refine ⟨3366886515120726293044997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244591010080484195363331 3366886515120726293044997)
              ·
                refine ⟨631291221585136179945937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3366886515120726293044997 631291221585136179945937)
                ·
                  refine ⟨473468416188852134959453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631291221585136179945937 473468416188852134959453)
                  ·
                    rfl

theorem cell20_1037336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_1037336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037336 prefixEnd_1037336 := by exact prefixLift 1037336
  have htrace : WordTrace (prefixWord ++ tailWord_1037336) baseStart_1037336 baseEnd_1037336 := by
    simpa [prefixWord, tailWord_1037336, baseEnd_1037336] using wordTrace_append hprefix tailTrace_1037336
  have hstable : (prefixWord ++ tailWord_1037336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037336).length < 2 ^ (prefixWord ++ tailWord_1037336).sum := by decide
  have hdescent : baseEnd_1037336 < baseStart_1037336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037409 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 3]
def baseStart_1037409 : Nat := 118140960795 + 1037409 * 2 ^ 59
def prefixEnd_1037409 : Nat := 4983230072969 + 3 ^ 40 * 1037409 * 2
def baseEnd_1037409 : Nat := 473501735377988325525821

theorem tailTrace_1037409 : CollatzResearch.WordTrace tailWord_1037409 prefixEnd_1037409 473501735377988325525821 := by
  unfold tailWord_1037409
  simp only [CollatzResearch.WordTrace]
  refine ⟨37837414698651843196659281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25224943132434562131106187 37837414698651843196659281)
  ·
    refine ⟨28378061023988882397494461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37837414698651843196659281 28378061023988882397494461)
    ·
      refine ⟨10641772883995830899060423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28378061023988882397494461 10641772883995830899060423)
      ·
        refine ⟨15962659325993746348590635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10641772883995830899060423 15962659325993746348590635)
        ·
          refine ⟨23943988988990619522885953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15962659325993746348590635 23943988988990619522885953)
          ·
            refine ⟨17957991741742964642164465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23943988988990619522885953 17957991741742964642164465)
            ·
              refine ⟨13468493806307223481623349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17957991741742964642164465 13468493806307223481623349)
              ·
                refine ⟨1262671294341302201402189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13468493806307223481623349 1262671294341302201402189)
                ·
                  refine ⟨473501735377988325525821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262671294341302201402189 473501735377988325525821)
                  ·
                    rfl

theorem cell20_1037409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_1037409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037409 prefixEnd_1037409 := by exact prefixLift 1037409
  have htrace : WordTrace (prefixWord ++ tailWord_1037409) baseStart_1037409 baseEnd_1037409 := by
    simpa [prefixWord, tailWord_1037409, baseEnd_1037409] using wordTrace_append hprefix tailTrace_1037409
  have hstable : (prefixWord ++ tailWord_1037409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037409).length < 2 ^ (prefixWord ++ tailWord_1037409).sum := by decide
  have hdescent : baseEnd_1037409 < baseStart_1037409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037423 : List Nat := [1, 1, 2, 1, 3, 3, 3, 6]
def baseStart_1037423 : Nat := 118140960795 + 1037423 * 2 ^ 59
def prefixEnd_1037423 : Nat := 4983230072969 + 3 ^ 40 * 1037423 * 2
def baseEnd_1037423 : Nat := 157836041786488833019699

theorem tailTrace_1037423 : CollatzResearch.WordTrace tailWord_1037423 prefixEnd_1037423 157836041786488833019699 := by
  unfold tailWord_1037423
  simp only [CollatzResearch.WordTrace]
  refine ⟨37837925320601123587668923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25225283547067415725112615 37837925320601123587668923)
  ·
    refine ⟨56756887980901685381503385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37837925320601123587668923 56756887980901685381503385)
    ·
      refine ⟨42567665985676264036127539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56756887980901685381503385 42567665985676264036127539)
      ·
        refine ⟨63851498978514396054191309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42567665985676264036127539 63851498978514396054191309)
        ·
          refine ⟨23944312116942898520321741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63851498978514396054191309 23944312116942898520321741)
          ·
            refine ⟨8979117043853586945120653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23944312116942898520321741 8979117043853586945120653)
            ·
              refine ⟨3367168891445095104420245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8979117043853586945120653 3367168891445095104420245)
              ·
                refine ⟨157836041786488833019699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3367168891445095104420245 157836041786488833019699)
                ·
                  rfl

theorem cell20_1037423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_1037423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037423 prefixEnd_1037423 := by exact prefixLift 1037423
  have htrace : WordTrace (prefixWord ++ tailWord_1037423) baseStart_1037423 baseEnd_1037423 := by
    simpa [prefixWord, tailWord_1037423, baseEnd_1037423] using wordTrace_append hprefix tailTrace_1037423
  have hstable : (prefixWord ++ tailWord_1037423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037423).length < 2 ^ (prefixWord ++ tailWord_1037423).sum := by decide
  have hdescent : baseEnd_1037423 < baseStart_1037423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037447 : List Nat := [1, 1, 4, 2, 1, 1, 1, 6, 3]
def baseStart_1037447 : Nat := 118140960795 + 1037447 * 2 ^ 59
def prefixEnd_1037447 : Nat := 4983230072969 + 3 ^ 40 * 1037447 * 2
def baseEnd_1037447 : Nat := 473519079613429082258999

theorem tailTrace_1037447 : CollatzResearch.WordTrace tailWord_1037447 prefixEnd_1037447 473519079613429082258999 := by
  unfold tailWord_1037447
  simp only [CollatzResearch.WordTrace]
  refine ⟨37838800672514175686542595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25225867115009450457695063 37838800672514175686542595)
  ·
    refine ⟨56758201008771263529813893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37838800672514175686542595 56758201008771263529813893)
    ·
      refine ⟨10642162689144611911840105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56758201008771263529813893 10642162689144611911840105)
      ·
        refine ⟨7981622016858458933880079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10642162689144611911840105 7981622016858458933880079)
        ·
          refine ⟨11972433025287688400820119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981622016858458933880079 11972433025287688400820119)
          ·
            refine ⟨17958649537931532601230179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11972433025287688400820119 17958649537931532601230179)
            ·
              refine ⟨26937974306897298901845269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17958649537931532601230179 26937974306897298901845269)
              ·
                refine ⟨1262717545635810886023997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26937974306897298901845269 1262717545635810886023997)
                ·
                  refine ⟨473519079613429082258999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262717545635810886023997 473519079613429082258999)
                  ·
                    rfl

theorem cell20_1037447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_1037447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037447 prefixEnd_1037447 := by exact prefixLift 1037447
  have htrace : WordTrace (prefixWord ++ tailWord_1037447) baseStart_1037447 baseEnd_1037447 := by
    simpa [prefixWord, tailWord_1037447, baseEnd_1037447] using wordTrace_append hprefix tailTrace_1037447
  have hstable : (prefixWord ++ tailWord_1037447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037447).length < 2 ^ (prefixWord ++ tailWord_1037447).sum := by decide
  have hdescent : baseEnd_1037447 < baseStart_1037447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037464 : List Nat := [2, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1037464 : Nat := 118140960795 + 1037464 * 2 ^ 59
def prefixEnd_1037464 : Nat := 4983230072969 + 3 ^ 40 * 1037464 * 2
def baseEnd_1037464 : Nat := 473526838876652578692263

theorem tailTrace_1037464 : CollatzResearch.WordTrace tailWord_1037464 prefixEnd_1037464 473526838876652578692263 := by
  unfold tailWord_1037464
  simp only [CollatzResearch.WordTrace]
  refine ⟨18919710356726293794955723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25226280475635058393274297 18919710356726293794955723)
  ·
    refine ⟨28379565535089440692433585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18919710356726293794955723 28379565535089440692433585)
    ·
      refine ⟨21284674151317080519325189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28379565535089440692433585 21284674151317080519325189)
      ·
        refine ⟨3990876403371952597373473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21284674151317080519325189 3990876403371952597373473)
        ·
          refine ⟨2993157302528964448030105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3990876403371952597373473 2993157302528964448030105)
          ·
            refine ⟨2244867976896723336022579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993157302528964448030105 2244867976896723336022579)
            ·
              refine ⟨3367301965345085004033869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244867976896723336022579 3367301965345085004033869)
              ·
                refine ⟨1262738237004406876512701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3367301965345085004033869 1262738237004406876512701)
                ·
                  refine ⟨473526838876652578692263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262738237004406876512701 473526838876652578692263)
                  ·
                    rfl

theorem cell20_1037464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1037464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037464 prefixEnd_1037464 := by exact prefixLift 1037464
  have htrace : WordTrace (prefixWord ++ tailWord_1037464) baseStart_1037464 baseEnd_1037464 := by
    simpa [prefixWord, tailWord_1037464, baseEnd_1037464] using wordTrace_append hprefix tailTrace_1037464
  have hstable : (prefixWord ++ tailWord_1037464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037464).length < 2 ^ (prefixWord ++ tailWord_1037464).sum := by decide
  have hdescent : baseEnd_1037464 < baseStart_1037464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037502 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1037502 : Nat := 118140960795 + 1037502 * 2 ^ 59
def prefixEnd_1037502 : Nat := 4983230072969 + 3 ^ 40 * 1037502 * 2
def baseEnd_1037502 : Nat := 473544183112093335425441

theorem tailTrace_1037502 : CollatzResearch.WordTrace tailWord_1037502 prefixEnd_1037502 473544183112093335425441 := by
  unfold tailWord_1037502
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730100835914365009974345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25227204458209946719863173 4730100835914365009974345)
  ·
    refine ⟨3547575626935773757480759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4730100835914365009974345 3547575626935773757480759)
    ·
      refine ⟨5321363440403660636221139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547575626935773757480759 5321363440403660636221139)
      ·
        refine ⟨7982045160605490954331709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5321363440403660636221139 7982045160605490954331709)
        ·
          refine ⟨2993266935227059107874391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7982045160605490954331709 2993266935227059107874391)
          ·
            refine ⟨4489900402840588661811587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993266935227059107874391 4489900402840588661811587)
            ·
              refine ⟨6734850604260882992717381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489900402840588661811587 6734850604260882992717381)
              ·
                refine ⟨1262784488298915561134509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6734850604260882992717381 1262784488298915561134509)
                ·
                  refine ⟨473544183112093335425441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262784488298915561134509 473544183112093335425441)
                  ·
                    rfl

theorem cell20_1037502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1037502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037502 prefixEnd_1037502 := by exact prefixLift 1037502
  have htrace : WordTrace (prefixWord ++ tailWord_1037502) baseStart_1037502 baseEnd_1037502 := by
    simpa [prefixWord, tailWord_1037502, baseEnd_1037502] using wordTrace_append hprefix tailTrace_1037502
  have hstable : (prefixWord ++ tailWord_1037502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037502).length < 2 ^ (prefixWord ++ tailWord_1037502).sum := by decide
  have hdescent : baseEnd_1037502 < baseStart_1037502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037505 : List Nat := [1, 2, 6, 1, 1, 2, 1, 4, 2]
def baseStart_1037505 : Nat := 118140960795 + 1037505 * 2 ^ 59
def prefixEnd_1037505 : Nat := 4983230072969 + 3 ^ 40 * 1037505 * 2
def baseEnd_1037505 : Nat := 473545552393838658325429

theorem tailTrace_1037505 : CollatzResearch.WordTrace tailWord_1037505 prefixEnd_1037505 473545552393838658325429 := by
  unfold tailWord_1037505
  simp only [CollatzResearch.WordTrace]
  refine ⟨37840916106304051592153969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25227277404202701061435979 37840916106304051592153969)
  ·
    refine ⟨28380687079728038694115477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37840916106304051592153969 28380687079728038694115477)
    ·
      refine ⟨1330344706862251813786663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28380687079728038694115477 1330344706862251813786663)
      ·
        refine ⟨1995517060293377720679995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330344706862251813786663 1995517060293377720679995)
        ·
          refine ⟨2993275590440066581019993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995517060293377720679995 2993275590440066581019993)
          ·
            refine ⟨2244956692830049935764995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993275590440066581019993 2244956692830049935764995)
            ·
              refine ⟨3367435039245074903647493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244956692830049935764995 3367435039245074903647493)
              ·
                refine ⟨631394069858451544433905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3367435039245074903647493 631394069858451544433905)
                ·
                  refine ⟨473545552393838658325429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631394069858451544433905 473545552393838658325429)
                  ·
                    rfl

theorem cell20_1037505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_1037505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037505 prefixEnd_1037505 := by exact prefixLift 1037505
  have htrace : WordTrace (prefixWord ++ tailWord_1037505) baseStart_1037505 baseEnd_1037505 := by
    simpa [prefixWord, tailWord_1037505, baseEnd_1037505] using wordTrace_append hprefix tailTrace_1037505
  have hstable : (prefixWord ++ tailWord_1037505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037505).length < 2 ^ (prefixWord ++ tailWord_1037505).sum := by decide
  have hdescent : baseEnd_1037505 < baseStart_1037505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037543 : List Nat := [1, 1, 5, 3, 2, 1, 2, 3, 2]
def baseStart_1037543 : Nat := 118140960795 + 1037543 * 2 ^ 59
def prefixEnd_1037543 : Nat := 4983230072969 + 3 ^ 40 * 1037543 * 2
def baseEnd_1037543 : Nat := 473562896629279415058607

theorem tailTrace_1037543 : CollatzResearch.WordTrace tailWord_1037543 prefixEnd_1037543 473562896629279415058607 := by
  unfold tailWord_1037543
  simp only [CollatzResearch.WordTrace]
  refine ⟨37842302080166384082037283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25228201386777589388024855 37842302080166384082037283)
  ·
    refine ⟨56763453120249576123055925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37842302080166384082037283 56763453120249576123055925)
    ·
      refine ⟨5321573730023397761536493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56763453120249576123055925 5321573730023397761536493)
      ·
        refine ⟨1995590148758774160576185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5321573730023397761536493 1995590148758774160576185)
        ·
          refine ⟨1496692611569080620432139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1995590148758774160576185 1496692611569080620432139)
          ·
            refine ⟨2245038917353620930648209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496692611569080620432139 2245038917353620930648209)
            ·
              refine ⟨1683779188015215697986157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2245038917353620930648209 1683779188015215697986157)
              ·
                refine ⟨631417195505705886744809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1683779188015215697986157 631417195505705886744809)
                ·
                  refine ⟨473562896629279415058607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631417195505705886744809 473562896629279415058607)
                  ·
                    rfl

theorem cell20_1037543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 2].length) (baseStart_1037543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037543 prefixEnd_1037543 := by exact prefixLift 1037543
  have htrace : WordTrace (prefixWord ++ tailWord_1037543) baseStart_1037543 baseEnd_1037543 := by
    simpa [prefixWord, tailWord_1037543, baseEnd_1037543] using wordTrace_append hprefix tailTrace_1037543
  have hstable : (prefixWord ++ tailWord_1037543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037543).length < 2 ^ (prefixWord ++ tailWord_1037543).sum := by decide
  have hdescent : baseEnd_1037543 < baseStart_1037543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037547 : List Nat := [1, 1, 1, 1, 2, 6, 1, 5, 2]
def baseStart_1037547 : Nat := 118140960795 + 1037547 * 2 ^ 59
def prefixEnd_1037547 : Nat := 4983230072969 + 3 ^ 40 * 1037547 * 2
def baseEnd_1037547 : Nat := 473564722338273178925257

theorem tailTrace_1037547 : CollatzResearch.WordTrace tailWord_1037547 prefixEnd_1037547 473564722338273178925257 := by
  unfold tailWord_1037547
  simp only [CollatzResearch.WordTrace]
  refine ⟨37842447972151892765182895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25228298648101261843455263 37842447972151892765182895)
  ·
    refine ⟨56763671958227839147774343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37842447972151892765182895 56763671958227839147774343)
    ·
      refine ⟨85145507937341758721661515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56763671958227839147774343 85145507937341758721661515)
      ·
        refine ⟨127718261906012638082492273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85145507937341758721661515 127718261906012638082492273)
        ·
          refine ⟨95788696429509478561869205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127718261906012638082492273 95788696429509478561869205)
          ·
            refine ⟨4490095145133256807587619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95788696429509478561869205 4490095145133256807587619)
            ·
              refine ⟨6735142717699885211381429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490095145133256807587619 6735142717699885211381429)
              ·
                refine ⟨631419629784364238567009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6735142717699885211381429 631419629784364238567009)
                ·
                  refine ⟨473564722338273178925257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631419629784364238567009 473564722338273178925257)
                  ·
                    rfl

theorem cell20_1037547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 2].length) (baseStart_1037547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037547 prefixEnd_1037547 := by exact prefixLift 1037547
  have htrace : WordTrace (prefixWord ++ tailWord_1037547) baseStart_1037547 baseEnd_1037547 := by
    simpa [prefixWord, tailWord_1037547, baseEnd_1037547] using wordTrace_append hprefix tailTrace_1037547
  have hstable : (prefixWord ++ tailWord_1037547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037547).length < 2 ^ (prefixWord ++ tailWord_1037547).sum := by decide
  have hdescent : baseEnd_1037547 < baseStart_1037547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037554 : List Nat := [3, 2, 1, 3, 3, 1, 7]
def baseStart_1037554 : Nat := 118140960795 + 1037554 * 2 ^ 59
def prefixEnd_1037554 : Nat := 4983230072969 + 3 ^ 40 * 1037554 * 2
def baseEnd_1037554 : Nat := 52618657481001362854655

theorem tailTrace_1037554 : CollatzResearch.WordTrace tailWord_1037554 prefixEnd_1037554 52618657481001362854655 := by
  unfold tailWord_1037554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9460675820781633240171929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25228468855417688640458477 9460675820781633240171929)
  ·
    refine ⟨7095506865586224930128947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9460675820781633240171929 7095506865586224930128947)
    ·
      refine ⟨10643260298379337395193421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095506865586224930128947 10643260298379337395193421)
      ·
        refine ⟨3991222611892251523197533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10643260298379337395193421 3991222611892251523197533)
        ·
          refine ⟨1496708479459594321199075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3991222611892251523197533 1496708479459594321199075)
          ·
            refine ⟨2245062719189391481798613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496708479459594321199075 2245062719189391481798613)
            ·
              refine ⟨52618657481001362854655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2245062719189391481798613 52618657481001362854655)
              ·
                rfl

theorem cell20_1037554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 7].length) (baseStart_1037554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037554 prefixEnd_1037554 := by exact prefixLift 1037554
  have htrace : WordTrace (prefixWord ++ tailWord_1037554) baseStart_1037554 baseEnd_1037554 := by
    simpa [prefixWord, tailWord_1037554, baseEnd_1037554] using wordTrace_append hprefix tailTrace_1037554
  have hstable : (prefixWord ++ tailWord_1037554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037554).length < 2 ^ (prefixWord ++ tailWord_1037554).sum := by decide
  have hdescent : baseEnd_1037554 < baseStart_1037554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037592 : List Nat := [2, 1, 2, 3, 1, 3, 4, 4]
def baseStart_1037592 : Nat := 118140960795 + 1037592 * 2 ^ 59
def prefixEnd_1037592 : Nat := 4983230072969 + 3 ^ 40 * 1037592 * 2
def baseEnd_1037592 : Nat := 157861753854817674141691

theorem tailTrace_1037592 : CollatzResearch.WordTrace tailWord_1037592 prefixEnd_1037592 157861753854817674141691 := by
  unfold tailWord_1037592
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922044628494432725285515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25229392837992576967047353 18922044628494432725285515)
  ·
    refine ⟨28383066942741649087928273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18922044628494432725285515 28383066942741649087928273)
    ·
      refine ⟨21287300207056236815946205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28383066942741649087928273 21287300207056236815946205)
      ·
        refine ⟨7982737577646088805979827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21287300207056236815946205 7982737577646088805979827)
        ·
          refine ⟨11974106366469133208969741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982737577646088805979827 11974106366469133208969741)
          ·
            refine ⟨4490289887425924953363653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11974106366469133208969741 4490289887425924953363653)
            ·
              refine ⟨841929353892360928755685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4490289887425924953363653 841929353892360928755685)
              ·
                refine ⟨157861753854817674141691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841929353892360928755685 157861753854817674141691)
                ·
                  rfl

theorem cell20_1037592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_1037592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037592 prefixEnd_1037592 := by exact prefixLift 1037592
  have htrace : WordTrace (prefixWord ++ tailWord_1037592) baseStart_1037592 baseEnd_1037592 := by
    simpa [prefixWord, tailWord_1037592, baseEnd_1037592] using wordTrace_append hprefix tailTrace_1037592
  have hstable : (prefixWord ++ tailWord_1037592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037592).length < 2 ^ (prefixWord ++ tailWord_1037592).sum := by decide
  have hdescent : baseEnd_1037592 < baseStart_1037592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037629 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 3]
def baseStart_1037629 : Nat := 118140960795 + 1037629 * 2 ^ 59
def prefixEnd_1037629 : Nat := 4983230072969 + 3 ^ 40 * 1037629 * 2
def baseEnd_1037629 : Nat := 473602149372645338191589

theorem tailTrace_1037629 : CollatzResearch.WordTrace tailWord_1037629 prefixEnd_1037629 473602149372645338191589 := by
  unfold tailWord_1037629
  simp only [CollatzResearch.WordTrace]
  refine ⟨37845438757854820769667941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25230292505236547179778627 37845438757854820769667941)
  ·
    refine ⟨7096019767097778894312739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37845438757854820769667941 7096019767097778894312739)
    ·
      refine ⟨10644029650646668341469109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7096019767097778894312739 10644029650646668341469109)
      ·
        refine ⟨997877779748125157012729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10644029650646668341469109 997877779748125157012729)
        ·
          refine ⟨748408334811093867759547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 997877779748125157012729 748408334811093867759547)
          ·
            refine ⟨1122612502216640801639321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748408334811093867759547 1122612502216640801639321)
            ·
              refine ⟨841959376662480601229491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122612502216640801639321 841959376662480601229491)
              ·
                refine ⟨1262939064993720901844237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841959376662480601229491 1262939064993720901844237)
                ·
                  refine ⟨473602149372645338191589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262939064993720901844237 473602149372645338191589)
                  ·
                    rfl

theorem cell20_1037629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_1037629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037629 prefixEnd_1037629 := by exact prefixLift 1037629
  have htrace : WordTrace (prefixWord ++ tailWord_1037629) baseStart_1037629 baseEnd_1037629 := by
    simpa [prefixWord, tailWord_1037629, baseEnd_1037629] using wordTrace_append hprefix tailTrace_1037629
  have hstable : (prefixWord ++ tailWord_1037629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037629).length < 2 ^ (prefixWord ++ tailWord_1037629).sum := by decide
  have hdescent : baseEnd_1037629 < baseStart_1037629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037630 : List Nat := [4, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1037630 : Nat := 118140960795 + 1037630 * 2 ^ 59
def prefixEnd_1037630 : Nat := 4983230072969 + 3 ^ 40 * 1037630 * 2
def baseEnd_1037630 : Nat := 157867535266631259719417

theorem tailTrace_1037630 : CollatzResearch.WordTrace tailWord_1037630 prefixEnd_1037630 157867535266631259719417 := by
  unfold tailWord_1037630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730684403856399742556793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25230316820567465293636229 4730684403856399742556793)
  ·
    refine ⟨3548013302892299806917595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4730684403856399742556793 3548013302892299806917595)
    ·
      refine ⟨5322019954338449710376393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3548013302892299806917595 5322019954338449710376393)
      ·
        refine ⟨3991514965753837282782295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5322019954338449710376393 3991514965753837282782295)
        ·
          refine ⟨5987272448630755924173443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991514965753837282782295 5987272448630755924173443)
          ·
            refine ⟨8980908672946133886260165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987272448630755924173443 8980908672946133886260165)
            ·
              refine ⟨1683920376177400103673781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8980908672946133886260165 1683920376177400103673781)
              ·
                refine ⟨157867535266631259719417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1683920376177400103673781 157867535266631259719417)
                ·
                  rfl

theorem cell20_1037630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1037630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037630 prefixEnd_1037630 := by exact prefixLift 1037630
  have htrace : WordTrace (prefixWord ++ tailWord_1037630) baseStart_1037630 baseEnd_1037630 := by
    simpa [prefixWord, tailWord_1037630, baseEnd_1037630] using wordTrace_append hprefix tailTrace_1037630
  have hstable : (prefixWord ++ tailWord_1037630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037630).length < 2 ^ (prefixWord ++ tailWord_1037630).sum := by decide
  have hdescent : baseEnd_1037630 < baseStart_1037630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037633 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 3]
def baseStart_1037633 : Nat := 118140960795 + 1037633 * 2 ^ 59
def prefixEnd_1037633 : Nat := 4983230072969 + 3 ^ 40 * 1037633 * 2
def baseEnd_1037633 : Nat := 473603975081639102058239

theorem tailTrace_1037633 : CollatzResearch.WordTrace tailWord_1037633 prefixEnd_1037633 473603975081639102058239 := by
  unfold tailWord_1037633
  simp only [CollatzResearch.WordTrace]
  refine ⟨37845584649840329452813553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25230389766560219635209035 37845584649840329452813553)
  ·
    refine ⟨28384188487380247089610165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37845584649840329452813553 28384188487380247089610165)
    ·
      refine ⟨2661017670691898164650953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28384188487380247089610165 2661017670691898164650953)
      ·
        refine ⟨1995763253018923623488215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661017670691898164650953 1995763253018923623488215)
        ·
          refine ⟨2993644879528385435232323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995763253018923623488215 2993644879528385435232323)
          ·
            refine ⟨4490467319292578152848485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993644879528385435232323 4490467319292578152848485)
            ·
              refine ⟨841962622367358403659091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4490467319292578152848485 841962622367358403659091)
              ·
                refine ⟨1262943933551037605488637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841962622367358403659091 1262943933551037605488637)
                ·
                  refine ⟨473603975081639102058239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1262943933551037605488637 473603975081639102058239)
                  ·
                    rfl

theorem cell20_1037633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_1037633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037633 prefixEnd_1037633 := by exact prefixLift 1037633
  have htrace : WordTrace (prefixWord ++ tailWord_1037633) baseStart_1037633 baseEnd_1037633 := by
    simpa [prefixWord, tailWord_1037633, baseEnd_1037633] using wordTrace_append hprefix tailTrace_1037633
  have hstable : (prefixWord ++ tailWord_1037633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037633).length < 2 ^ (prefixWord ++ tailWord_1037633).sum := by decide
  have hdescent : baseEnd_1037633 < baseStart_1037633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037658 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1037658 : Nat := 118140960795 + 1037658 * 2 ^ 59
def prefixEnd_1037658 : Nat := 4983230072969 + 3 ^ 40 * 1037658 * 2
def baseEnd_1037658 : Nat := 473615385762850126224803

theorem tailTrace_1037658 : CollatzResearch.WordTrace tailWord_1037658 prefixEnd_1037658 473615385762850126224803 := by
  unfold tailWord_1037658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461624118687439680618407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25230997649833172481649085 9461624118687439680618407)
  ·
    refine ⟨14192436178031159520927611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9461624118687439680618407 14192436178031159520927611)
    ·
      refine ⟨21288654267046739281391417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14192436178031159520927611 21288654267046739281391417)
      ·
        refine ⟨15966490700285054461043563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21288654267046739281391417 15966490700285054461043563)
        ·
          refine ⟨23949736050427581691565345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15966490700285054461043563 23949736050427581691565345)
          ·
            refine ⟨17962302037820686268674009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23949736050427581691565345 17962302037820686268674009)
            ·
              refine ⟨13471726528365514701505507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17962302037820686268674009 13471726528365514701505507)
              ·
                refine ⟨20207589792548272052258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471726528365514701505507 20207589792548272052258261)
                ·
                  refine ⟨473615385762850126224803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20207589792548272052258261 473615385762850126224803)
                  ·
                    rfl

theorem cell20_1037658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1037658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037658 prefixEnd_1037658 := by exact prefixLift 1037658
  have htrace : WordTrace (prefixWord ++ tailWord_1037658) baseStart_1037658 baseEnd_1037658 := by
    simpa [prefixWord, tailWord_1037658, baseEnd_1037658] using wordTrace_append hprefix tailTrace_1037658
  have hstable : (prefixWord ++ tailWord_1037658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037658).length < 2 ^ (prefixWord ++ tailWord_1037658).sum := by decide
  have hdescent : baseEnd_1037658 < baseStart_1037658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037674 : List Nat := [3, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_1037674 : Nat := 118140960795 + 1037674 * 2 ^ 59
def prefixEnd_1037674 : Nat := 4983230072969 + 3 ^ 40 * 1037674 * 2
def baseEnd_1037674 : Nat := 473622688598825181691405

theorem tailTrace_1037674 : CollatzResearch.WordTrace tailWord_1037674 prefixEnd_1037674 473622688598825181691405 := by
  unfold tailWord_1037674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461770010672948363764019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25231386695127862303370717 9461770010672948363764019)
  ·
    refine ⟨14192655016009422545646029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9461770010672948363764019 14192655016009422545646029)
    ·
      refine ⟨5322245631003533454617261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14192655016009422545646029 5322245631003533454617261)
      ·
        refine ⟨1995842111626325045481473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5322245631003533454617261 1995842111626325045481473)
        ·
          refine ⟨1496881583719743784111105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1995842111626325045481473 1496881583719743784111105)
          ·
            refine ⟨1122661187789807838083329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496881583719743784111105 1122661187789807838083329)
            ·
              refine ⟨841995890842355878562497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122661187789807838083329 841995890842355878562497)
              ·
                refine ⟨631496918131766908921873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841995890842355878562497 631496918131766908921873)
                ·
                  refine ⟨473622688598825181691405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631496918131766908921873 473622688598825181691405)
                  ·
                    rfl

theorem cell20_1037674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_1037674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037674 prefixEnd_1037674 := by exact prefixLift 1037674
  have htrace : WordTrace (prefixWord ++ tailWord_1037674) baseStart_1037674 baseEnd_1037674 := by
    simpa [prefixWord, tailWord_1037674, baseEnd_1037674] using wordTrace_append hprefix tailTrace_1037674
  have hstable : (prefixWord ++ tailWord_1037674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037674).length < 2 ^ (prefixWord ++ tailWord_1037674).sum := by decide
  have hdescent : baseEnd_1037674 < baseStart_1037674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037682 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1037682 : Nat := 118140960795 + 1037682 * 2 ^ 59
def prefixEnd_1037682 : Nat := 4983230072969 + 3 ^ 40 * 1037682 * 2
def baseEnd_1037682 : Nat := 473626340016812709424705

theorem tailTrace_1037682 : CollatzResearch.WordTrace tailWord_1037682 prefixEnd_1037682 473626340016812709424705 := by
  unfold tailWord_1037682
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461842956665702705336825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25231581217775207214231533 9461842956665702705336825)
  ·
    refine ⟨7096382217499277029002619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9461842956665702705336825 7096382217499277029002619)
    ·
      refine ⟨10644573326248915543503929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7096382217499277029002619 10644573326248915543503929)
      ·
        refine ⟨7983429994686686657627947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10644573326248915543503929 7983429994686686657627947)
        ·
          refine ⟨11975144992030029986441921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7983429994686686657627947 11975144992030029986441921)
          ·
            refine ⟨8981358744022522489831441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11975144992030029986441921 8981358744022522489831441)
            ·
              refine ⟨6736019058016891867373581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8981358744022522489831441 6736019058016891867373581)
              ·
                refine ⟨2526007146756334450265093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6736019058016891867373581 2526007146756334450265093)
                ·
                  refine ⟨473626340016812709424705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526007146756334450265093 473626340016812709424705)
                  ·
                    rfl

theorem cell20_1037682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1037682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037682 prefixEnd_1037682 := by exact prefixLift 1037682
  have htrace : WordTrace (prefixWord ++ tailWord_1037682) baseStart_1037682 baseEnd_1037682 := by
    simpa [prefixWord, tailWord_1037682, baseEnd_1037682] using wordTrace_append hprefix tailTrace_1037682
  have hstable : (prefixWord ++ tailWord_1037682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037682).length < 2 ^ (prefixWord ++ tailWord_1037682).sum := by decide
  have hdescent : baseEnd_1037682 < baseStart_1037682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037685 : List Nat := [1, 3, 4, 1, 3, 2, 1, 5]
def baseStart_1037685 : Nat := 118140960795 + 1037685 * 2 ^ 59
def prefixEnd_1037685 : Nat := 4983230072969 + 3 ^ 40 * 1037685 * 2
def baseEnd_1037685 : Nat := 157875903099519344108231

theorem tailTrace_1037685 : CollatzResearch.WordTrace tailWord_1037685 prefixEnd_1037685 157875903099519344108231 := by
  unfold tailWord_1037685
  simp only [CollatzResearch.WordTrace]
  refine ⟨37847481245651942333706509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25231654163767961555804339 37847481245651942333706509)
  ·
    refine ⟨14192805467119478375139941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37847481245651942333706509 14192805467119478375139941)
    ·
      refine ⟨2661151025084902195338739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14192805467119478375139941 2661151025084902195338739)
      ·
        refine ⟨3991726537627353293008109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661151025084902195338739 3991726537627353293008109)
        ·
          refine ⟨1496897451610257484878041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3991726537627353293008109 1496897451610257484878041)
          ·
            refine ⟨1122673088707693113658531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496897451610257484878041 1122673088707693113658531)
            ·
              refine ⟨1684009633061539670487797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122673088707693113658531 1684009633061539670487797)
              ·
                refine ⟨157875903099519344108231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1684009633061539670487797 157875903099519344108231)
                ·
                  rfl

theorem cell20_1037685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_1037685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037685 prefixEnd_1037685 := by exact prefixLift 1037685
  have htrace : WordTrace (prefixWord ++ tailWord_1037685) baseStart_1037685 baseEnd_1037685 := by
    simpa [prefixWord, tailWord_1037685, baseEnd_1037685] using wordTrace_append hprefix tailTrace_1037685
  have hstable : (prefixWord ++ tailWord_1037685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037685).length < 2 ^ (prefixWord ++ tailWord_1037685).sum := by decide
  have hdescent : baseEnd_1037685 < baseStart_1037685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037689 : List Nat := [1, 2, 1, 3, 2, 1, 5, 5]
def baseStart_1037689 : Nat := 118140960795 + 1037689 * 2 ^ 59
def prefixEnd_1037689 : Nat := 4983230072969 + 3 ^ 40 * 1037689 * 2
def baseEnd_1037689 : Nat := 157876511669183932063781

theorem tailTrace_1037689 : CollatzResearch.WordTrace tailWord_1037689 prefixEnd_1037689 157876511669183932063781 := by
  unfold tailWord_1037689
  simp only [CollatzResearch.WordTrace]
  refine ⟨37847627137637451016852121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25231751425091634011234747 37847627137637451016852121)
  ·
    refine ⟨28385720353228088262639091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37847627137637451016852121 28385720353228088262639091)
    ·
      refine ⟨42578580529842132393958637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28385720353228088262639091 42578580529842132393958637)
      ·
        refine ⟨15966967698690799647734489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42578580529842132393958637 15966967698690799647734489)
        ·
          refine ⟨11975225774018099735800867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15966967698690799647734489 11975225774018099735800867)
          ·
            refine ⟨17962838661027149603701301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11975225774018099735800867 17962838661027149603701301)
            ·
              refine ⟨1684016124471295275346997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17962838661027149603701301 1684016124471295275346997)
              ·
                refine ⟨157876511669183932063781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1684016124471295275346997 157876511669183932063781)
                ·
                  rfl

theorem cell20_1037689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_1037689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037689 prefixEnd_1037689 := by exact prefixLift 1037689
  have htrace : WordTrace (prefixWord ++ tailWord_1037689) baseStart_1037689 baseEnd_1037689 := by
    simpa [prefixWord, tailWord_1037689, baseEnd_1037689] using wordTrace_append hprefix tailTrace_1037689
  have hstable : (prefixWord ++ tailWord_1037689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037689).length < 2 ^ (prefixWord ++ tailWord_1037689).sum := by decide
  have hdescent : baseEnd_1037689 < baseStart_1037689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037716 : List Nat := [2, 4, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1037716 : Nat := 118140960795 + 1037716 * 2 ^ 59
def prefixEnd_1037716 : Nat := 4983230072969 + 3 ^ 40 * 1037716 * 2
def baseEnd_1037716 : Nat := 473641858543259702291233

theorem tailTrace_1037716 : CollatzResearch.WordTrace tailWord_1037716 prefixEnd_1037716 473641858543259702291233 := by
  unfold tailWord_1037716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18924305954269817314042501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25232407939026423085390001 18924305954269817314042501)
  ·
    refine ⟨3548307366425590746382969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18924305954269817314042501 3548307366425590746382969)
    ·
      refine ⟨2661230524819193059787227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3548307366425590746382969 2661230524819193059787227)
      ·
        refine ⟨3991845787228789589680841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661230524819193059787227 3991845787228789589680841)
        ·
          refine ⟨2993884340421592192260631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3991845787228789589680841 2993884340421592192260631)
          ·
            refine ⟨4490826510632388288390947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993884340421592192260631 4490826510632388288390947)
            ·
              refine ⟨6736239765948582432586421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490826510632388288390947 6736239765948582432586421)
              ·
                refine ⟨631522478057679603054977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6736239765948582432586421 631522478057679603054977)
                ·
                  refine ⟨473641858543259702291233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631522478057679603054977 473641858543259702291233)
                  ·
                    rfl

theorem cell20_1037716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1037716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037716 prefixEnd_1037716 := by exact prefixLift 1037716
  have htrace : WordTrace (prefixWord ++ tailWord_1037716) baseStart_1037716 baseEnd_1037716 := by
    simpa [prefixWord, tailWord_1037716, baseEnd_1037716] using wordTrace_append hprefix tailTrace_1037716
  have hstable : (prefixWord ++ tailWord_1037716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037716).length < 2 ^ (prefixWord ++ tailWord_1037716).sum := by decide
  have hdescent : baseEnd_1037716 < baseStart_1037716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037726 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1037726 : Nat := 118140960795 + 1037726 * 2 ^ 59
def prefixEnd_1037726 : Nat := 4983230072969 + 3 ^ 40 * 1037726 * 2
def baseEnd_1037726 : Nat := 473646422815744111957859

theorem tailTrace_1037726 : CollatzResearch.WordTrace tailWord_1037726 prefixEnd_1037726 473646422815744111957859 := by
  unfold tailWord_1037726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731122079812925791993629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25232651092335604223966021 4731122079812925791993629)
  ·
    refine ⟨1774170779929847171997611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4731122079812925791993629 1774170779929847171997611)
    ·
      refine ⟨2661256169894770757996417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774170779929847171997611 2661256169894770757996417)
      ·
        refine ⟨1995942127421078068497313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661256169894770757996417 1995942127421078068497313)
        ·
          refine ⟨1496956595565808551372985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1995942127421078068497313 1496956595565808551372985)
          ·
            refine ⟨1122717446674356413529739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496956595565808551372985 1122717446674356413529739)
            ·
              refine ⟨1684076170011534620294609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122717446674356413529739 1684076170011534620294609)
              ·
                refine ⟨1263057127508650965220957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684076170011534620294609 1263057127508650965220957)
                ·
                  refine ⟨473646422815744111957859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263057127508650965220957 473646422815744111957859)
                  ·
                    rfl

theorem cell20_1037726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1037726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037726 prefixEnd_1037726 := by exact prefixLift 1037726
  have htrace : WordTrace (prefixWord ++ tailWord_1037726) baseStart_1037726 baseEnd_1037726 := by
    simpa [prefixWord, tailWord_1037726, baseEnd_1037726] using wordTrace_append hprefix tailTrace_1037726
  have hstable : (prefixWord ++ tailWord_1037726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037726).length < 2 ^ (prefixWord ++ tailWord_1037726).sum := by decide
  have hdescent : baseEnd_1037726 < baseStart_1037726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037727 : List Nat := [1, 1, 2, 5, 1, 3, 7]
def baseStart_1037727 : Nat := 118140960795 + 1037727 * 2 ^ 59
def prefixEnd_1037727 : Nat := 4983230072969 + 3 ^ 40 * 1037727 * 2
def baseEnd_1037727 : Nat := 52627431026999172547169

theorem tailTrace_1037727 : CollatzResearch.WordTrace tailWord_1037727 prefixEnd_1037727 52627431026999172547169 := by
  unfold tailWord_1037727
  simp only [CollatzResearch.WordTrace]
  refine ⟨37849013111499783506735435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25232675407666522337823623 37849013111499783506735435)
  ·
    refine ⟨56773519667249675260103153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37849013111499783506735435 56773519667249675260103153)
    ·
      refine ⟨42580139750437256445077365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56773519667249675260103153 42580139750437256445077365)
      ·
        refine ⟨3991888101603492791726003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42580139750437256445077365 3991888101603492791726003)
        ·
          refine ⟨5987832152405239187589005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991888101603492791726003 5987832152405239187589005)
          ·
            refine ⟨2245437057151964695345877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5987832152405239187589005 2245437057151964695345877)
            ·
              refine ⟨52627431026999172547169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2245437057151964695345877 52627431026999172547169)
              ·
                rfl

theorem cell20_1037727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_1037727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037727 prefixEnd_1037727 := by exact prefixLift 1037727
  have htrace : WordTrace (prefixWord ++ tailWord_1037727) baseStart_1037727 baseEnd_1037727 := by
    simpa [prefixWord, tailWord_1037727, baseEnd_1037727] using wordTrace_append hprefix tailTrace_1037727
  have hstable : (prefixWord ++ tailWord_1037727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037727).length < 2 ^ (prefixWord ++ tailWord_1037727).sum := by decide
  have hdescent : baseEnd_1037727 < baseStart_1037727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037730 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1037730 : Nat := 118140960795 + 1037730 * 2 ^ 59
def prefixEnd_1037730 : Nat := 4983230072969 + 3 ^ 40 * 1037730 * 2
def baseEnd_1037730 : Nat := 473648248524737875824509

theorem tailTrace_1037730 : CollatzResearch.WordTrace tailWord_1037730 prefixEnd_1037730 473648248524737875824509 := by
  unfold tailWord_1037730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462280632622228754773661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25232748353659276679396429 9462280632622228754773661)
  ·
    refine ⟨3548355237233335783040123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9462280632622228754773661 3548355237233335783040123)
    ·
      refine ⟨5322532855850003674560185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3548355237233335783040123 5322532855850003674560185)
      ·
        refine ⟨3991899641887502755920139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5322532855850003674560185 3991899641887502755920139)
        ·
          refine ⟨5987849462831254133880209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991899641887502755920139 5987849462831254133880209)
          ·
            refine ⟨4490887097123440600410157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987849462831254133880209 4490887097123440600410157)
            ·
              refine ⟨1684082661421290225153809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4490887097123440600410157 1684082661421290225153809)
              ·
                refine ⟨1263061996065967668865357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684082661421290225153809 1263061996065967668865357)
                ·
                  refine ⟨473648248524737875824509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263061996065967668865357 473648248524737875824509)
                  ·
                    rfl

theorem cell20_1037730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1037730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037730 prefixEnd_1037730 := by exact prefixLift 1037730
  have htrace : WordTrace (prefixWord ++ tailWord_1037730) baseStart_1037730 baseEnd_1037730 := by
    simpa [prefixWord, tailWord_1037730, baseEnd_1037730] using wordTrace_append hprefix tailTrace_1037730
  have hstable : (prefixWord ++ tailWord_1037730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037730).length < 2 ^ (prefixWord ++ tailWord_1037730).sum := by decide
  have hdescent : baseEnd_1037730 < baseStart_1037730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037775 : List Nat := [1, 1, 2, 1, 1, 4, 5, 3, 2]
def baseStart_1037775 : Nat := 118140960795 + 1037775 * 2 ^ 59
def prefixEnd_1037775 : Nat := 4983230072969 + 3 ^ 40 * 1037775 * 2
def baseEnd_1037775 : Nat := 473668787750917719324325

theorem tailTrace_1037775 : CollatzResearch.WordTrace tailWord_1037775 prefixEnd_1037775 473668787750917719324325 := by
  unfold tailWord_1037775
  simp only [CollatzResearch.WordTrace]
  refine ⟨37850763815325887704482779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25233842543550591802988519 37850763815325887704482779)
  ·
    refine ⟨56776145722988831556724169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37850763815325887704482779 56776145722988831556724169)
    ·
      refine ⟨42582109292241623667543127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56776145722988831556724169 42582109292241623667543127)
      ·
        refine ⟨63873163938362435501314691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42582109292241623667543127 63873163938362435501314691)
        ·
          refine ⟨95809745907543653251972037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63873163938362435501314691 95809745907543653251972037)
          ·
            refine ⟨17964327357664434984744757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95809745907543653251972037 17964327357664434984744757)
            ·
              refine ⟨1684155689781040779819821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17964327357664434984744757 1684155689781040779819821)
              ·
                refine ⟨631558383667890292432433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1684155689781040779819821 631558383667890292432433)
                ·
                  refine ⟨473668787750917719324325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631558383667890292432433 473668787750917719324325)
                  ·
                    rfl

theorem cell20_1037775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 2].length) (baseStart_1037775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037775 prefixEnd_1037775 := by exact prefixLift 1037775
  have htrace : WordTrace (prefixWord ++ tailWord_1037775) baseStart_1037775 baseEnd_1037775 := by
    simpa [prefixWord, tailWord_1037775, baseEnd_1037775] using wordTrace_append hprefix tailTrace_1037775
  have hstable : (prefixWord ++ tailWord_1037775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037775).length < 2 ^ (prefixWord ++ tailWord_1037775).sum := by decide
  have hdescent : baseEnd_1037775 < baseStart_1037775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037782 : List Nat := [5, 2, 1, 1, 1, 2, 8]
def baseStart_1037782 : Nat := 118140960795 + 1037782 * 2 ^ 59
def prefixEnd_1037782 : Nat := 4983230072969 + 3 ^ 40 * 1037782 * 2
def baseEnd_1037782 : Nat := 52630220304628534010107

theorem tailTrace_1037782 : CollatzResearch.WordTrace tailWord_1037782 prefixEnd_1037782 52630220304628534010107 := by
  unfold tailWord_1037782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365688695393782993749225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25234012750867018599991733 2365688695393782993749225)
  ·
    refine ⟨1774266521545337245311919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2365688695393782993749225 1774266521545337245311919)
    ·
      refine ⟨2661399782318005867967879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1774266521545337245311919 2661399782318005867967879)
      ·
        refine ⟨3992099673477008801951819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661399782318005867967879 3992099673477008801951819)
        ·
          refine ⟨5988149510215513202927729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992099673477008801951819 5988149510215513202927729)
          ·
            refine ⟨4491112132661634902195797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5988149510215513202927729 4491112132661634902195797)
            ·
              refine ⟨52630220304628534010107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4491112132661634902195797 52630220304628534010107)
              ·
                rfl

theorem cell20_1037782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 8].length) (baseStart_1037782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037782 prefixEnd_1037782 := by exact prefixLift 1037782
  have htrace : WordTrace (prefixWord ++ tailWord_1037782) baseStart_1037782 baseEnd_1037782 := by
    simpa [prefixWord, tailWord_1037782, baseEnd_1037782] using wordTrace_append hprefix tailTrace_1037782
  have hstable : (prefixWord ++ tailWord_1037782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037782).length < 2 ^ (prefixWord ++ tailWord_1037782).sum := by decide
  have hdescent : baseEnd_1037782 < baseStart_1037782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037789 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1037789 : Nat := 118140960795 + 1037789 * 2 ^ 59
def prefixEnd_1037789 : Nat := 4983230072969 + 3 ^ 40 * 1037789 * 2
def baseEnd_1037789 : Nat := 473675177732395892857601

theorem tailTrace_1037789 : CollatzResearch.WordTrace tailWord_1037789 prefixEnd_1037789 473675177732395892857601 := by
  unfold tailWord_1037789
  simp only [CollatzResearch.WordTrace]
  refine ⟨37851274437275168095492421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25234182958183445396994947 37851274437275168095492421)
  ·
    refine ⟨7097113956989094017904829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37851274437275168095492421 7097113956989094017904829)
    ·
      refine ⟨2661417733870910256714311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7097113956989094017904829 2661417733870910256714311)
      ·
        refine ⟨3992126600806365385071467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2661417733870910256714311 3992126600806365385071467)
        ·
          refine ⟨5988189901209548077607201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3992126600806365385071467 5988189901209548077607201)
          ·
            refine ⟨4491142425907161058205401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5988189901209548077607201 4491142425907161058205401)
            ·
              refine ⟨3368356819430370793654051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4491142425907161058205401 3368356819430370793654051)
              ·
                refine ⟨5052535229145556190481077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3368356819430370793654051 5052535229145556190481077)
                ·
                  refine ⟨473675177732395892857601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5052535229145556190481077 473675177732395892857601)
                  ·
                    rfl

theorem cell20_1037789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1037789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037789 prefixEnd_1037789 := by exact prefixLift 1037789
  have htrace : WordTrace (prefixWord ++ tailWord_1037789) baseStart_1037789 baseEnd_1037789 := by
    simpa [prefixWord, tailWord_1037789, baseEnd_1037789] using wordTrace_append hprefix tailTrace_1037789
  have hstable : (prefixWord ++ tailWord_1037789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037789).length < 2 ^ (prefixWord ++ tailWord_1037789).sum := by decide
  have hdescent : baseEnd_1037789 < baseStart_1037789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037802 : List Nat := [3, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_1037802 : Nat := 118140960795 + 1037802 * 2 ^ 59
def prefixEnd_1037802 : Nat := 4983230072969 + 3 ^ 40 * 1037802 * 2
def baseEnd_1037802 : Nat := 473681111286625625424215

theorem tailTrace_1037802 : CollatzResearch.WordTrace tailWord_1037802 prefixEnd_1037802 473681111286625625424215 := by
  unfold tailWord_1037802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462937146557017828928915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25234499057485380877143773 9462937146557017828928915)
  ·
    refine ⟨14194405719835526743393373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9462937146557017828928915 14194405719835526743393373)
    ·
      refine ⟨5322902144938322528772515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14194405719835526743393373 5322902144938322528772515)
      ·
        refine ⟨7984353217407483793158773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322902144938322528772515 7984353217407483793158773)
        ·
          refine ⟨748533114131951605608635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7984353217407483793158773 748533114131951605608635)
          ·
            refine ⟨1122799671197927408412953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748533114131951605608635 1122799671197927408412953)
            ·
              refine ⟨842099753398445556309715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1122799671197927408412953 842099753398445556309715)
              ·
                refine ⟨1263149630097668334464573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842099753398445556309715 1263149630097668334464573)
                ·
                  refine ⟨473681111286625625424215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263149630097668334464573 473681111286625625424215)
                  ·
                    rfl

theorem cell20_1037802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_1037802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037802 prefixEnd_1037802 := by exact prefixLift 1037802
  have htrace : WordTrace (prefixWord ++ tailWord_1037802) baseStart_1037802 baseEnd_1037802 := by
    simpa [prefixWord, tailWord_1037802, baseEnd_1037802] using wordTrace_append hprefix tailTrace_1037802
  have hstable : (prefixWord ++ tailWord_1037802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037802).length < 2 ^ (prefixWord ++ tailWord_1037802).sum := by decide
  have hdescent : baseEnd_1037802 < baseStart_1037802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037817 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 6]
def baseStart_1037817 : Nat := 118140960795 + 1037817 * 2 ^ 59
def prefixEnd_1037817 : Nat := 4983230072969 + 3 ^ 40 * 1037817 * 2
def baseEnd_1037817 : Nat := 473687957695352239924153

theorem tailTrace_1037817 : CollatzResearch.WordTrace tailWord_1037817 prefixEnd_1037817 473687957695352239924153 := by
  unfold tailWord_1037817
  simp only [CollatzResearch.WordTrace]
  refine ⟨37852295681173728877511705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25234863787449152585007803 37852295681173728877511705)
  ·
    refine ⟨28389221760880296658133779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37852295681173728877511705 28389221760880296658133779)
    ·
      refine ⟨42583832641320444987200669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28389221760880296658133779 42583832641320444987200669)
      ·
        refine ⟨15968937240495166870200251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42583832641320444987200669 15968937240495166870200251)
        ·
          refine ⟨23953405860742750305300377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15968937240495166870200251 23953405860742750305300377)
          ·
            refine ⟨17965054395557062728975283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23953405860742750305300377 17965054395557062728975283)
            ·
              refine ⟨26947581593335594093462925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17965054395557062728975283 26947581593335594093462925)
              ·
                refine ⟨10105343097500847785048597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26947581593335594093462925 10105343097500847785048597)
                ·
                  refine ⟨473687957695352239924153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10105343097500847785048597 473687957695352239924153)
                  ·
                    rfl

theorem cell20_1037817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_1037817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037817 prefixEnd_1037817 := by exact prefixLift 1037817
  have htrace : WordTrace (prefixWord ++ tailWord_1037817) baseStart_1037817 baseEnd_1037817 := by
    simpa [prefixWord, tailWord_1037817, baseEnd_1037817] using wordTrace_append hprefix tailTrace_1037817
  have hstable : (prefixWord ++ tailWord_1037817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037817).length < 2 ^ (prefixWord ++ tailWord_1037817).sum := by decide
  have hdescent : baseEnd_1037817 < baseStart_1037817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037837 : List Nat := [1, 7, 1, 1, 2, 8]
def baseStart_1037837 : Nat := 118140960795 + 1037837 * 2 ^ 59
def prefixEnd_1037837 : Nat := 4983230072969 + 3 ^ 40 * 1037837 * 2
def baseEnd_1037837 : Nat := 17544336527419298491015

theorem tailTrace_1037837 : CollatzResearch.WordTrace tailWord_1037837 prefixEnd_1037837 17544336527419298491015 := by
  unfold tailWord_1037837
  simp only [CollatzResearch.WordTrace]
  refine ⟨37853025141101272293239765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25235350094067514862159843 37853025141101272293239765)
  ·
    refine ⟨887180276744561069372807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37853025141101272293239765 887180276744561069372807)
    ·
      refine ⟨1330770415116841604059211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 887180276744561069372807 1330770415116841604059211)
      ·
        refine ⟨1996155622675262406088817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1330770415116841604059211 1996155622675262406088817)
        ·
          refine ⟨1497116717006446804566613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996155622675262406088817 1497116717006446804566613)
          ·
            refine ⟨17544336527419298491015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1497116717006446804566613 17544336527419298491015)
            ·
              rfl

theorem cell20_1037837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 8].length) (baseStart_1037837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037837 prefixEnd_1037837 := by exact prefixLift 1037837
  have htrace : WordTrace (prefixWord ++ tailWord_1037837) baseStart_1037837 baseEnd_1037837 := by
    simpa [prefixWord, tailWord_1037837, baseEnd_1037837] using wordTrace_append hprefix tailTrace_1037837
  have hstable : (prefixWord ++ tailWord_1037837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037837).length < 2 ^ (prefixWord ++ tailWord_1037837).sum := by decide
  have hdescent : baseEnd_1037837 < baseStart_1037837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037893 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_1037893 : Nat := 118140960795 + 1037893 * 2 ^ 59
def prefixEnd_1037893 : Nat := 4983230072969 + 3 ^ 40 * 1037893 * 2
def baseEnd_1037893 : Nat := 473722646166233753390509

theorem tailTrace_1037893 : CollatzResearch.WordTrace tailWord_1037893 prefixEnd_1037893 473722646166233753390509 := by
  unfold tailWord_1037893
  simp only [CollatzResearch.WordTrace]
  refine ⟨37855067628898393857278333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25236711752598929238185555 37855067628898393857278333)
  ·
    refine ⟨14195650360836897696479375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37855067628898393857278333 14195650360836897696479375)
    ·
      refine ⟨21293475541255346544719063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14195650360836897696479375 21293475541255346544719063)
      ·
        refine ⟨31940213311883019817078595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21293475541255346544719063 31940213311883019817078595)
        ·
          refine ⟨47910319967824529725617893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31940213311883019817078595 47910319967824529725617893)
          ·
            refine ⟨8983184993967099323553355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47910319967824529725617893 8983184993967099323553355)
            ·
              refine ⟨13474777490950648985330033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8983184993967099323553355 13474777490950648985330033)
              ·
                refine ⟨10106083118212986738997525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13474777490950648985330033 10106083118212986738997525)
                ·
                  refine ⟨473722646166233753390509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10106083118212986738997525 473722646166233753390509)
                  ·
                    rfl

theorem cell20_1037893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_1037893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037893 prefixEnd_1037893 := by exact prefixLift 1037893
  have htrace : WordTrace (prefixWord ++ tailWord_1037893) baseStart_1037893 baseEnd_1037893 := by
    simpa [prefixWord, tailWord_1037893, baseEnd_1037893] using wordTrace_append hprefix tailTrace_1037893
  have hstable : (prefixWord ++ tailWord_1037893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037893).length < 2 ^ (prefixWord ++ tailWord_1037893).sum := by decide
  have hdescent : baseEnd_1037893 < baseStart_1037893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037934 : List Nat := [4, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1037934 : Nat := 118140960795 + 1037934 * 2 ^ 59
def prefixEnd_1037934 : Nat := 4983230072969 + 3 ^ 40 * 1037934 * 2
def baseEnd_1037934 : Nat := 157913786561139944341225

theorem tailTrace_1037934 : CollatzResearch.WordTrace tailWord_1037934 prefixEnd_1037934 157913786561139944341225 := by
  unfold tailWord_1037934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4732070377718732232440107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25237708681166571906347237 4732070377718732232440107)
  ·
    refine ⟨7098105566578098348660161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4732070377718732232440107 7098105566578098348660161)
    ·
      refine ⟨5323579174933573761495121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7098105566578098348660161 5323579174933573761495121)
      ·
        refine ⟨3992684381200180321121341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5323579174933573761495121 3992684381200180321121341)
        ·
          refine ⟨1497256642950067620420503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3992684381200180321121341 1497256642950067620420503)
          ·
            refine ⟨2245884964425101430630755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497256642950067620420503 2245884964425101430630755)
            ·
              refine ⟨3368827446637652145946133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2245884964425101430630755 3368827446637652145946133)
              ·
                refine ⟨157913786561139944341225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3368827446637652145946133 157913786561139944341225)
                ·
                  rfl

theorem cell20_1037934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1037934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037934 prefixEnd_1037934 := by exact prefixLift 1037934
  have htrace : WordTrace (prefixWord ++ tailWord_1037934) baseStart_1037934 baseEnd_1037934 := by
    simpa [prefixWord, tailWord_1037934, baseEnd_1037934] using wordTrace_append hprefix tailTrace_1037934
  have hstable : (prefixWord ++ tailWord_1037934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037934).length < 2 ^ (prefixWord ++ tailWord_1037934).sum := by decide
  have hdescent : baseEnd_1037934 < baseStart_1037934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037941 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_1037941 : Nat := 118140960795 + 1037941 * 2 ^ 59
def prefixEnd_1037941 : Nat := 4983230072969 + 3 ^ 40 * 1037941 * 2
def baseEnd_1037941 : Nat := 473744554674158919790313

theorem tailTrace_1037941 : CollatzResearch.WordTrace tailWord_1037941 prefixEnd_1037941 473744554674158919790313 := by
  unfold tailWord_1037941
  simp only [CollatzResearch.WordTrace]
  refine ⟨37856818332724498055025677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25237878888482998703350451 37856818332724498055025677)
  ·
    refine ⟨14196306874771686770634629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37856818332724498055025677 14196306874771686770634629)
    ·
      refine ⟨2661807539019691269493993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14196306874771686770634629 2661807539019691269493993)
      ·
        refine ⟨1996355654264768452120495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2661807539019691269493993 1996355654264768452120495)
        ·
          refine ⟨2994533481397152678180743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996355654264768452120495 2994533481397152678180743)
          ·
            refine ⟨4491800222095729017271115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2994533481397152678180743 4491800222095729017271115)
            ·
              refine ⟨6737700333143593525906673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4491800222095729017271115 6737700333143593525906673)
              ·
                refine ⟨5053275249857695144430005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6737700333143593525906673 5053275249857695144430005)
                ·
                  refine ⟨473744554674158919790313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5053275249857695144430005 473744554674158919790313)
                  ·
                    rfl

theorem cell20_1037941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_1037941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037941 prefixEnd_1037941 := by exact prefixLift 1037941
  have htrace : WordTrace (prefixWord ++ tailWord_1037941) baseStart_1037941 baseEnd_1037941 := by
    simpa [prefixWord, tailWord_1037941, baseEnd_1037941] using wordTrace_append hprefix tailTrace_1037941
  have hstable : (prefixWord ++ tailWord_1037941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037941).length < 2 ^ (prefixWord ++ tailWord_1037941).sum := by decide
  have hdescent : baseEnd_1037941 < baseStart_1037941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1037969 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_1037969 : Nat := 118140960795 + 1037969 * 2 ^ 59
def prefixEnd_1037969 : Nat := 4983230072969 + 3 ^ 40 * 1037969 * 2
def baseEnd_1037969 : Nat := 473757334637115266856865

theorem tailTrace_1037969 : CollatzResearch.WordTrace tailWord_1037969 prefixEnd_1037969 473757334637115266856865 := by
  unfold tailWord_1037969
  simp only [CollatzResearch.WordTrace]
  refine ⟨37857839576623058837044961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25238559717748705891363307 37857839576623058837044961)
  ·
    refine ⟨28393379682467294127783721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37857839576623058837044961 28393379682467294127783721)
    ·
      refine ⟨21295034761850470595837791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28393379682467294127783721 21295034761850470595837791)
      ·
        refine ⟨31942552142775705893756687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21295034761850470595837791 31942552142775705893756687)
        ·
          refine ⟨47913828214163558840635031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31942552142775705893756687 47913828214163558840635031)
          ·
            refine ⟨71870742321245338260952547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47913828214163558840635031 71870742321245338260952547)
            ·
              refine ⟨107806113481868007391428821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71870742321245338260952547 107806113481868007391428821)
              ·
                refine ⟨2526705784731281423236613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107806113481868007391428821 2526705784731281423236613)
                ·
                  refine ⟨473757334637115266856865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526705784731281423236613 473757334637115266856865)
                  ·
                    rfl

theorem cell20_1037969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1037969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1037969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1037969 prefixEnd_1037969 := by exact prefixLift 1037969
  have htrace : WordTrace (prefixWord ++ tailWord_1037969) baseStart_1037969 baseEnd_1037969 := by
    simpa [prefixWord, tailWord_1037969, baseEnd_1037969] using wordTrace_append hprefix tailTrace_1037969
  have hstable : (prefixWord ++ tailWord_1037969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1037969).length < 2 ^ (prefixWord ++ tailWord_1037969).sum := by decide
  have hdescent : baseEnd_1037969 < baseStart_1037969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1037969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038068 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1038068 : Nat := 118140960795 + 1038068 * 2 ^ 59
def prefixEnd_1038068 : Nat := 4983230072969 + 3 ^ 40 * 1038068 * 2
def baseEnd_1038068 : Nat := 473802520934710922556461

theorem tailTrace_1038068 : CollatzResearch.WordTrace tailWord_1038068 prefixEnd_1038068 473802520934710922556461 := by
  unfold tailWord_1038068
  simp only [CollatzResearch.WordTrace]
  refine ⟨18930725201632199372449429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25240966935509599163265905 18930725201632199372449429)
  ·
    refine ⟨887377743826509345583567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18930725201632199372449429 887377743826509345583567)
    ·
      refine ⟨1331066615739764018375351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 887377743826509345583567 1331066615739764018375351)
      ·
        refine ⟨1996599923609646027563027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331066615739764018375351 1996599923609646027563027)
        ·
          refine ⟨2994899885414469041344541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996599923609646027563027 2994899885414469041344541)
          ·
            refine ⟨1123087457030425890504203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2994899885414469041344541 1123087457030425890504203)
            ·
              refine ⟨1684631185545638835756305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123087457030425890504203 1684631185545638835756305)
              ·
                refine ⟨1263473389159229126817229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684631185545638835756305 1263473389159229126817229)
                ·
                  refine ⟨473802520934710922556461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263473389159229126817229 473802520934710922556461)
                  ·
                    rfl

theorem cell20_1038068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1038068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038068 prefixEnd_1038068 := by exact prefixLift 1038068
  have htrace : WordTrace (prefixWord ++ tailWord_1038068) baseStart_1038068 baseEnd_1038068 := by
    simpa [prefixWord, tailWord_1038068, baseEnd_1038068] using wordTrace_append hprefix tailTrace_1038068
  have hstable : (prefixWord ++ tailWord_1038068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038068).length < 2 ^ (prefixWord ++ tailWord_1038068).sum := by decide
  have hdescent : baseEnd_1038068 < baseStart_1038068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038076 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1038076 : Nat := 118140960795 + 1038076 * 2 ^ 59
def prefixEnd_1038076 : Nat := 4983230072969 + 3 ^ 40 * 1038076 * 2
def baseEnd_1038076 : Nat := 473806172352698450289761

theorem tailTrace_1038076 : CollatzResearch.WordTrace tailWord_1038076 prefixEnd_1038076 473806172352698450289761 := by
  unfold tailWord_1038076
  simp only [CollatzResearch.WordTrace]
  refine ⟨18930871093617708055595041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25241161458156944074126721 18930871093617708055595041)
  ·
    refine ⟨14198153320213281041696281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18930871093617708055595041 14198153320213281041696281)
    ·
      refine ⟨10648614990159960781272211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14198153320213281041696281 10648614990159960781272211)
      ·
        refine ⟨15972922485239941171908317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10648614990159960781272211 15972922485239941171908317)
        ·
          refine ⟨5989845931964977939465619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15972922485239941171908317 5989845931964977939465619)
          ·
            refine ⟨8984768897947466909198429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5989845931964977939465619 8984768897947466909198429)
            ·
              refine ⟨3369288336730300090949411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8984768897947466909198429 3369288336730300090949411)
              ·
                refine ⟨5053932505095450136424117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3369288336730300090949411 5053932505095450136424117)
                ·
                  refine ⟨473806172352698450289761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5053932505095450136424117 473806172352698450289761)
                  ·
                    rfl

theorem cell20_1038076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1038076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038076 prefixEnd_1038076 := by exact prefixLift 1038076
  have htrace : WordTrace (prefixWord ++ tailWord_1038076) baseStart_1038076 baseEnd_1038076 := by
    simpa [prefixWord, tailWord_1038076, baseEnd_1038076] using wordTrace_append hprefix tailTrace_1038076
  have hstable : (prefixWord ++ tailWord_1038076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038076).length < 2 ^ (prefixWord ++ tailWord_1038076).sum := by decide
  have hdescent : baseEnd_1038076 < baseStart_1038076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038083 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_1038083 : Nat := 118140960795 + 1038083 * 2 ^ 59
def prefixEnd_1038083 : Nat := 4983230072969 + 3 ^ 40 * 1038083 * 2
def baseEnd_1038083 : Nat := 473809367343437537056399

theorem tailTrace_1038083 : CollatzResearch.WordTrace tailWord_1038083 prefixEnd_1038083 473809367343437537056399 := by
  unfold tailWord_1038083
  simp only [CollatzResearch.WordTrace]
  refine ⟨37861997498210056306694903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25241331665473370871129935 37861997498210056306694903)
  ·
    refine ⟨56792996247315084460042355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37861997498210056306694903 56792996247315084460042355)
    ·
      refine ⟨85189494370972626690063533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56792996247315084460042355 85189494370972626690063533)
      ·
        refine ⟨31946060389114735008773825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85189494370972626690063533 31946060389114735008773825)
        ·
          refine ⟨23959545291836051256580369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31946060389114735008773825 23959545291836051256580369)
          ·
            refine ⟨17969658968877038442435277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23959545291836051256580369 17969658968877038442435277)
            ·
              refine ⟨6738622113328889415913229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17969658968877038442435277 6738622113328889415913229)
              ·
                refine ⟨2526983292498333530967461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6738622113328889415913229 2526983292498333530967461)
                ·
                  refine ⟨473809367343437537056399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2526983292498333530967461 473809367343437537056399)
                  ·
                    rfl

theorem cell20_1038083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_1038083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038083 prefixEnd_1038083 := by exact prefixLift 1038083
  have htrace : WordTrace (prefixWord ++ tailWord_1038083) baseStart_1038083 baseEnd_1038083 := by
    simpa [prefixWord, tailWord_1038083, baseEnd_1038083] using wordTrace_append hprefix tailTrace_1038083
  have hstable : (prefixWord ++ tailWord_1038083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038083).length < 2 ^ (prefixWord ++ tailWord_1038083).sum := by decide
  have hdescent : baseEnd_1038083 < baseStart_1038083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038114 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1038114 : Nat := 118140960795 + 1038114 * 2 ^ 59
def prefixEnd_1038114 : Nat := 4983230072969 + 3 ^ 40 * 1038114 * 2
def baseEnd_1038114 : Nat := 473823516588139207022939

theorem tailTrace_1038114 : CollatzResearch.WordTrace tailWord_1038114 prefixEnd_1038114 473823516588139207022939 := by
  unfold tailWord_1038114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9465782040274437150268349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25242085440731832400715597 9465782040274437150268349)
  ·
    refine ⟨3549668265102913931350631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9465782040274437150268349 3549668265102913931350631)
    ·
      refine ⟨5324502397654370897025947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3549668265102913931350631 5324502397654370897025947)
      ·
        refine ⟨7986753596481556345538921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5324502397654370897025947 7986753596481556345538921)
        ·
          refine ⟨5990065197361167259154191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7986753596481556345538921 5990065197361167259154191)
          ·
            refine ⟨8985097796041750888731287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5990065197361167259154191 8985097796041750888731287)
            ·
              refine ⟨13477646694062626333096931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8985097796041750888731287 13477646694062626333096931)
              ·
                refine ⟨20216470041093939499645397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13477646694062626333096931 20216470041093939499645397)
                ·
                  refine ⟨473823516588139207022939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20216470041093939499645397 473823516588139207022939)
                  ·
                    rfl

theorem cell20_1038114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1038114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038114 prefixEnd_1038114 := by exact prefixLift 1038114
  have htrace : WordTrace (prefixWord ++ tailWord_1038114) baseStart_1038114 baseEnd_1038114 := by
    simpa [prefixWord, tailWord_1038114, baseEnd_1038114] using wordTrace_append hprefix tailTrace_1038114
  have hstable : (prefixWord ++ tailWord_1038114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038114).length < 2 ^ (prefixWord ++ tailWord_1038114).sum := by decide
  have hdescent : baseEnd_1038114 < baseStart_1038114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038117 : List Nat := [1, 3, 1, 2, 3, 2, 3, 3, 2]
def baseStart_1038117 : Nat := 118140960795 + 1038117 * 2 ^ 59
def prefixEnd_1038117 : Nat := 4983230072969 + 3 ^ 40 * 1038117 * 2
def baseEnd_1038117 : Nat := 473824885869884529922927

theorem tailTrace_1038117 : CollatzResearch.WordTrace tailWord_1038117 prefixEnd_1038117 473824885869884529922927 := by
  unfold tailWord_1038117
  simp only [CollatzResearch.WordTrace]
  refine ⟨37863237580086880113432605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25242158386724586742288403 37863237580086880113432605)
  ·
    refine ⟨14198714092532580042537227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37863237580086880113432605 14198714092532580042537227)
    ·
      refine ⟨21298071138798870063805841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14198714092532580042537227 21298071138798870063805841)
      ·
        refine ⟨15973553354099152547854381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21298071138798870063805841 15973553354099152547854381)
        ·
          refine ⟨5990082507787182205445393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15973553354099152547854381 5990082507787182205445393)
          ·
            refine ⟨4492561880840386654084045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5990082507787182205445393 4492561880840386654084045)
            ·
              refine ⟨1684710705315144995281517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4492561880840386654084045 1684710705315144995281517)
              ·
                refine ⟨631766514493179373230569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1684710705315144995281517 631766514493179373230569)
                ·
                  refine ⟨473824885869884529922927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631766514493179373230569 473824885869884529922927)
                  ·
                    rfl

theorem cell20_1038117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_1038117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038117 prefixEnd_1038117 := by exact prefixLift 1038117
  have htrace : WordTrace (prefixWord ++ tailWord_1038117) baseStart_1038117 baseEnd_1038117 := by
    simpa [prefixWord, tailWord_1038117, baseEnd_1038117] using wordTrace_append hprefix tailTrace_1038117
  have hstable : (prefixWord ++ tailWord_1038117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038117).length < 2 ^ (prefixWord ++ tailWord_1038117).sum := by decide
  have hdescent : baseEnd_1038117 < baseStart_1038117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038134 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1038134 : Nat := 118140960795 + 1038134 * 2 ^ 59
def prefixEnd_1038134 : Nat := 4983230072969 + 3 ^ 40 * 1038134 * 2
def baseEnd_1038134 : Nat := 473832645133108026356191

theorem tailTrace_1038134 : CollatzResearch.WordTrace tailWord_1038134 prefixEnd_1038134 473832645133108026356191 := by
  unfold tailWord_1038134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366491101314080751050091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25242571747350194677867637 2366491101314080751050091)
  ·
    refine ⟨3549736651971121126575137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2366491101314080751050091 3549736651971121126575137)
    ·
      refine ⟨2662302488978340844931353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3549736651971121126575137 2662302488978340844931353)
      ·
        refine ⟨1996726866733755633698515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2662302488978340844931353 1996726866733755633698515)
        ·
          refine ⟨2995090300100633450547773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1996726866733755633698515 2995090300100633450547773)
          ·
            refine ⟨1123158862537737543955415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2995090300100633450547773 1123158862537737543955415)
            ·
              refine ⟨1684738293806606315933123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123158862537737543955415 1684738293806606315933123)
              ·
                refine ⟨2527107440709909473899685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684738293806606315933123 2527107440709909473899685)
                ·
                  refine ⟨473832645133108026356191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527107440709909473899685 473832645133108026356191)
                  ·
                    rfl

theorem cell20_1038134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1038134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038134 prefixEnd_1038134 := by exact prefixLift 1038134
  have htrace : WordTrace (prefixWord ++ tailWord_1038134) baseStart_1038134 baseEnd_1038134 := by
    simpa [prefixWord, tailWord_1038134, baseEnd_1038134] using wordTrace_append hprefix tailTrace_1038134
  have hstable : (prefixWord ++ tailWord_1038134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038134).length < 2 ^ (prefixWord ++ tailWord_1038134).sum := by decide
  have hdescent : baseEnd_1038134 < baseStart_1038134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038138 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_1038138 : Nat := 118140960795 + 1038138 * 2 ^ 59
def prefixEnd_1038138 : Nat := 4983230072969 + 3 ^ 40 * 1038138 * 2
def baseEnd_1038138 : Nat := 473834470842101790222841

theorem tailTrace_1038138 : CollatzResearch.WordTrace tailWord_1038138 prefixEnd_1038138 473834470842101790222841 := by
  unfold tailWord_1038138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9466000878252700174986767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25242669008673867133298045 9466000878252700174986767)
  ·
    refine ⟨14199001317379050262480151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9466000878252700174986767 14199001317379050262480151)
    ·
      refine ⟨21298501976068575393720227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14199001317379050262480151 21298501976068575393720227)
      ·
        refine ⟨31947752964102863090580341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21298501976068575393720227 31947752964102863090580341)
        ·
          refine ⟨2995101840384643414741907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31947752964102863090580341 2995101840384643414741907)
          ·
            refine ⟨4492652760576965122112861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2995101840384643414741907 4492652760576965122112861)
            ·
              refine ⟨1684744785216361920792323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4492652760576965122112861 1684744785216361920792323)
              ·
                refine ⟨2527117177824542881188485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684744785216361920792323 2527117177824542881188485)
                ·
                  refine ⟨473834470842101790222841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527117177824542881188485 473834470842101790222841)
                  ·
                    rfl

theorem cell20_1038138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_1038138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038138 prefixEnd_1038138 := by exact prefixLift 1038138
  have htrace : WordTrace (prefixWord ++ tailWord_1038138) baseStart_1038138 baseEnd_1038138 := by
    simpa [prefixWord, tailWord_1038138, baseEnd_1038138] using wordTrace_append hprefix tailTrace_1038138
  have hstable : (prefixWord ++ tailWord_1038138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038138).length < 2 ^ (prefixWord ++ tailWord_1038138).sum := by decide
  have hdescent : baseEnd_1038138 < baseStart_1038138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038231 : List Nat := [1, 1, 3, 3, 1, 4, 2, 3, 2]
def baseStart_1038231 : Nat := 118140960795 + 1038231 * 2 ^ 59
def prefixEnd_1038231 : Nat := 4983230072969 + 3 ^ 40 * 1038231 * 2
def baseEnd_1038231 : Nat := 473876918576206800122461

theorem tailTrace_1038231 : CollatzResearch.WordTrace tailWord_1038231 prefixEnd_1038231 473876918576206800122461 := by
  unfold tailWord_1038231
  simp only [CollatzResearch.WordTrace]
  refine ⟨37867395501673877583082547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25244930334449251722055031 37867395501673877583082547)
  ·
    refine ⟨56801093252510816374623821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37867395501673877583082547 56801093252510816374623821)
    ·
      refine ⟨21300409969691556140483933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56801093252510816374623821 21300409969691556140483933)
      ·
        refine ⟨7987653738634333552681475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21300409969691556140483933 7987653738634333552681475)
        ·
          refine ⟨11981480607951500329022213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7987653738634333552681475 11981480607951500329022213)
          ·
            refine ⟨2246527613990906311691665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11981480607951500329022213 2246527613990906311691665)
            ·
              refine ⟨1684895710493179733768749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246527613990906311691665 1684895710493179733768749)
              ·
                refine ⟨631835891434942400163281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1684895710493179733768749 631835891434942400163281)
                ·
                  refine ⟨473876918576206800122461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631835891434942400163281 473876918576206800122461)
                  ·
                    rfl

theorem cell20_1038231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 2].length) (baseStart_1038231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038231 prefixEnd_1038231 := by exact prefixLift 1038231
  have htrace : WordTrace (prefixWord ++ tailWord_1038231) baseStart_1038231 baseEnd_1038231 := by
    simpa [prefixWord, tailWord_1038231, baseEnd_1038231] using wordTrace_append hprefix tailTrace_1038231
  have hstable : (prefixWord ++ tailWord_1038231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038231).length < 2 ^ (prefixWord ++ tailWord_1038231).sum := by decide
  have hdescent : baseEnd_1038231 < baseStart_1038231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038241 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 3]
def baseStart_1038241 : Nat := 118140960795 + 1038241 * 2 ^ 59
def prefixEnd_1038241 : Nat := 4983230072969 + 3 ^ 40 * 1038241 * 2
def baseEnd_1038241 : Nat := 473881482848691209789087

theorem tailTrace_1038241 : CollatzResearch.WordTrace tailWord_1038241 prefixEnd_1038241 473881482848691209789087 := by
  unfold tailWord_1038241
  simp only [CollatzResearch.WordTrace]
  refine ⟨37867760231637649290946577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25245173487758432860631051 37867760231637649290946577)
  ·
    refine ⟨28400820173728236968209933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37867760231637649290946577 28400820173728236968209933)
    ·
      refine ⟨10650307565148088863078725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28400820173728236968209933 10650307565148088863078725)
      ·
        refine ⟨1996932668465266661827261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10650307565148088863078725 1996932668465266661827261)
        ·
          refine ⟨748849750674474998185223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1996932668465266661827261 748849750674474998185223)
          ·
            refine ⟨1123274626011712497277835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748849750674474998185223 1123274626011712497277835)
            ·
              refine ⟨1684911939017568745916753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123274626011712497277835 1684911939017568745916753)
              ·
                refine ⟨1263683954263176559437565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1684911939017568745916753 1263683954263176559437565)
                ·
                  refine ⟨473881482848691209789087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263683954263176559437565 473881482848691209789087)
                  ·
                    rfl

theorem cell20_1038241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_1038241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038241 prefixEnd_1038241 := by exact prefixLift 1038241
  have htrace : WordTrace (prefixWord ++ tailWord_1038241) baseStart_1038241 baseEnd_1038241 := by
    simpa [prefixWord, tailWord_1038241, baseEnd_1038241] using wordTrace_append hprefix tailTrace_1038241
  have hstable : (prefixWord ++ tailWord_1038241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038241).length < 2 ^ (prefixWord ++ tailWord_1038241).sum := by decide
  have hdescent : baseEnd_1038241 < baseStart_1038241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038248 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_1038248 : Nat := 118140960795 + 1038248 * 2 ^ 59
def prefixEnd_1038248 : Nat := 4983230072969 + 3 ^ 40 * 1038248 * 2
def baseEnd_1038248 : Nat := 473884677839430296555725

theorem tailTrace_1038248 : CollatzResearch.WordTrace tailWord_1038248 prefixEnd_1038248 473884677839430296555725 := by
  unfold tailWord_1038248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18934007771306144743225699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25245343695074859657634265 18934007771306144743225699)
  ·
    refine ⟨28401011656959217114838549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18934007771306144743225699 28401011656959217114838549)
    ·
      refine ⟨1331297421419963302258057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28401011656959217114838549 1331297421419963302258057)
      ·
        refine ⟨998473066064972476693543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331297421419963302258057 998473066064972476693543)
        ·
          refine ⟨1497709599097458715040315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998473066064972476693543 1497709599097458715040315)
          ·
            refine ⟨2246564398646188072560473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497709599097458715040315 2246564398646188072560473)
            ·
              refine ⟨1684923298984641054420355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2246564398646188072560473 1684923298984641054420355)
              ·
                refine ⟨2527384948476961581630533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684923298984641054420355 2527384948476961581630533)
                ·
                  refine ⟨473884677839430296555725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527384948476961581630533 473884677839430296555725)
                  ·
                    rfl

theorem cell20_1038248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_1038248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038248 prefixEnd_1038248 := by exact prefixLift 1038248
  have htrace : WordTrace (prefixWord ++ tailWord_1038248) baseStart_1038248 baseEnd_1038248 := by
    simpa [prefixWord, tailWord_1038248, baseEnd_1038248] using wordTrace_append hprefix tailTrace_1038248
  have hstable : (prefixWord ++ tailWord_1038248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038248).length < 2 ^ (prefixWord ++ tailWord_1038248).sum := by decide
  have hdescent : baseEnd_1038248 < baseStart_1038248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038287 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_1038287 : Nat := 118140960795 + 1038287 * 2 ^ 59
def prefixEnd_1038287 : Nat := 4983230072969 + 3 ^ 40 * 1038287 * 2
def baseEnd_1038287 : Nat := 473902478502119494255565

theorem tailTrace_1038287 : CollatzResearch.WordTrace tailWord_1038287 prefixEnd_1038287 473902478502119494255565 := by
  unfold tailWord_1038287
  simp only [CollatzResearch.WordTrace]
  refine ⟨37869437989470999147121115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25246291992980666098080743 37869437989470999147121115)
  ·
    refine ⟨56804156984206498720681673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37869437989470999147121115 56804156984206498720681673)
    ·
      refine ⟨42603117738154874040511255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56804156984206498720681673 42603117738154874040511255)
      ·
        refine ⟨63904676607232311060766883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42603117738154874040511255 63904676607232311060766883)
        ·
          refine ⟨95857014910848466591150325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63904676607232311060766883 95857014910848466591150325)
          ·
            refine ⟨8986595147892043742920343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95857014910848466591150325 8986595147892043742920343)
            ·
              refine ⟨13479892721838065614380515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8986595147892043742920343 13479892721838065614380515)
              ·
                refine ⟨20219839082757098421570773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13479892721838065614380515 20219839082757098421570773)
                ·
                  refine ⟨473902478502119494255565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20219839082757098421570773 473902478502119494255565)
                  ·
                    rfl

theorem cell20_1038287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_1038287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038287 prefixEnd_1038287 := by exact prefixLift 1038287
  have htrace : WordTrace (prefixWord ++ tailWord_1038287) baseStart_1038287 baseEnd_1038287 := by
    simpa [prefixWord, tailWord_1038287, baseEnd_1038287] using wordTrace_append hprefix tailTrace_1038287
  have hstable : (prefixWord ++ tailWord_1038287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038287).length < 2 ^ (prefixWord ++ tailWord_1038287).sum := by decide
  have hdescent : baseEnd_1038287 < baseStart_1038287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038297 : List Nat := [1, 2, 1, 2, 6, 2, 6]
def baseStart_1038297 : Nat := 118140960795 + 1038297 * 2 ^ 59
def prefixEnd_1038297 : Nat := 4983230072969 + 3 ^ 40 * 1038297 * 2
def baseEnd_1038297 : Nat := 52656338086067100435799

theorem tailTrace_1038297 : CollatzResearch.WordTrace tailWord_1038297 prefixEnd_1038297 52656338086067100435799 := by
  unfold tailWord_1038297
  simp only [CollatzResearch.WordTrace]
  refine ⟨37869802719434770854985145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25246535146289847236656763 37869802719434770854985145)
  ·
    refine ⟨28402352039576078141238859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37869802719434770854985145 28402352039576078141238859)
    ·
      refine ⟨42603528059364117211858289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28402352039576078141238859 42603528059364117211858289)
      ·
        refine ⟨31952646044523087908893717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42603528059364117211858289 31952646044523087908893717)
        ·
          refine ⟨1497780283337019745729393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31952646044523087908893717 1497780283337019745729393)
          ·
            refine ⟨1123335212502764809297045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1497780283337019745729393 1123335212502764809297045)
            ·
              refine ⟨52656338086067100435799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1123335212502764809297045 52656338086067100435799)
              ·
                rfl

theorem cell20_1038297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 6].length) (baseStart_1038297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038297 prefixEnd_1038297 := by exact prefixLift 1038297
  have htrace : WordTrace (prefixWord ++ tailWord_1038297) baseStart_1038297 baseEnd_1038297 := by
    simpa [prefixWord, tailWord_1038297, baseEnd_1038297] using wordTrace_append hprefix tailTrace_1038297
  have hstable : (prefixWord ++ tailWord_1038297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038297).length < 2 ^ (prefixWord ++ tailWord_1038297).sum := by decide
  have hdescent : baseEnd_1038297 < baseStart_1038297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038321 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 3]
def baseStart_1038321 : Nat := 118140960795 + 1038321 * 2 ^ 59
def prefixEnd_1038321 : Nat := 4983230072969 + 3 ^ 40 * 1038321 * 2
def baseEnd_1038321 : Nat := 473917997028566487122093

theorem tailTrace_1038321 : CollatzResearch.WordTrace tailWord_1038321 prefixEnd_1038321 473917997028566487122093 := by
  unfold tailWord_1038321
  simp only [CollatzResearch.WordTrace]
  refine ⟨37870678071347822953858817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25247118714231881969239211 37870678071347822953858817)
  ·
    refine ⟨28403008553510867215394113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37870678071347822953858817 28403008553510867215394113)
    ·
      refine ⟨21302256415133150411545585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28403008553510867215394113 21302256415133150411545585)
      ·
        refine ⟨15976692311349862808659189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21302256415133150411545585 15976692311349862808659189)
        ·
          refine ⟨1497814904189049638311799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15976692311349862808659189 1497814904189049638311799)
          ·
            refine ⟨2246722356283574457467699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497814904189049638311799 2246722356283574457467699)
            ·
              refine ⟨3370083534425361686201549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246722356283574457467699 3370083534425361686201549)
              ·
                refine ⟨1263781325409510632325581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3370083534425361686201549 1263781325409510632325581)
                ·
                  refine ⟨473917997028566487122093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1263781325409510632325581 473917997028566487122093)
                  ·
                    rfl

theorem cell20_1038321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 3].length) (baseStart_1038321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038321 prefixEnd_1038321 := by exact prefixLift 1038321
  have htrace : WordTrace (prefixWord ++ tailWord_1038321) baseStart_1038321 baseEnd_1038321 := by
    simpa [prefixWord, tailWord_1038321, baseEnd_1038321] using wordTrace_append hprefix tailTrace_1038321
  have hstable : (prefixWord ++ tailWord_1038321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038321).length < 2 ^ (prefixWord ++ tailWord_1038321).sum := by decide
  have hdescent : baseEnd_1038321 < baseStart_1038321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038362 : List Nat := [3, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_1038362 : Nat := 118140960795 + 1038362 * 2 ^ 59
def prefixEnd_1038362 : Nat := 4983230072969 + 3 ^ 40 * 1038362 * 2
def baseEnd_1038362 : Nat := 473936710545752566755259

theorem tailTrace_1038362 : CollatzResearch.WordTrace tailWord_1038362 prefixEnd_1038362 473936710545752566755259 := by
  unfold tailWord_1038362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468043366049821739025335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25248115642799524637400893 9468043366049821739025335)
  ·
    refine ⟨14202065049074732608538003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9468043366049821739025335 14202065049074732608538003)
    ·
      refine ⟨21303097573612098912807005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14202065049074732608538003 21303097573612098912807005)
      ·
        refine ⟨7988661590104537092302627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21303097573612098912807005 7988661590104537092302627)
        ·
          refine ⟨11982992385156805638453941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7988661590104537092302627 11982992385156805638453941)
          ·
            refine ⟨1123405536108450528605057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11982992385156805638453941 1123405536108450528605057)
            ·
              refine ⟨842554152081337896453793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123405536108450528605057 842554152081337896453793)
              ·
                refine ⟨631915614061003422340345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842554152081337896453793 631915614061003422340345)
                ·
                  refine ⟨473936710545752566755259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631915614061003422340345 473936710545752566755259)
                  ·
                    rfl

theorem cell20_1038362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_1038362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038362 prefixEnd_1038362 := by exact prefixLift 1038362
  have htrace : WordTrace (prefixWord ++ tailWord_1038362) baseStart_1038362 baseEnd_1038362 := by
    simpa [prefixWord, tailWord_1038362, baseEnd_1038362] using wordTrace_append hprefix tailTrace_1038362
  have hstable : (prefixWord ++ tailWord_1038362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038362).length < 2 ^ (prefixWord ++ tailWord_1038362).sum := by decide
  have hdescent : baseEnd_1038362 < baseStart_1038362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038373 : List Nat := [1, 3, 1, 2, 2, 5, 1, 5]
def baseStart_1038373 : Nat := 118140960795 + 1038373 * 2 ^ 59
def prefixEnd_1038373 : Nat := 4983230072969 + 3 ^ 40 * 1038373 * 2
def baseEnd_1038373 : Nat := 157980577081828472462849

theorem tailTrace_1038373 : CollatzResearch.WordTrace tailWord_1038373 prefixEnd_1038373 157980577081828472462849 := by
  unfold tailWord_1038373
  simp only [CollatzResearch.WordTrace]
  refine ⟨37872574667159435834751773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25248383111439623889834515 37872574667159435834751773)
  ·
    refine ⟨14202215500184788438031915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37872574667159435834751773 14202215500184788438031915)
    ·
      refine ⟨21303323250277182657047873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14202215500184788438031915 21303323250277182657047873)
      ·
        refine ⟨15977492437707886992785905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21303323250277182657047873 15977492437707886992785905)
        ·
          refine ⟨11983119328280915244589429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15977492437707886992785905 11983119328280915244589429)
          ·
            refine ⟨1123417437026335804180259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11983119328280915244589429 1123417437026335804180259)
            ·
              refine ⟨1685126155539503706270389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123417437026335804180259 1685126155539503706270389)
              ·
                refine ⟨157980577081828472462849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1685126155539503706270389 157980577081828472462849)
                ·
                  rfl

theorem cell20_1038373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_1038373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038373 prefixEnd_1038373 := by exact prefixLift 1038373
  have htrace : WordTrace (prefixWord ++ tailWord_1038373) baseStart_1038373 baseEnd_1038373 := by
    simpa [prefixWord, tailWord_1038373, baseEnd_1038373] using wordTrace_append hprefix tailTrace_1038373
  have hstable : (prefixWord ++ tailWord_1038373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038373).length < 2 ^ (prefixWord ++ tailWord_1038373).sum := by decide
  have hdescent : baseEnd_1038373 < baseStart_1038373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038390 : List Nat := [5, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1038390 : Nat := 118140960795 + 1038390 * 2 ^ 59
def prefixEnd_1038390 : Nat := 4983230072969 + 3 ^ 40 * 1038390 * 2
def baseEnd_1038390 : Nat := 157983163502902971273937

theorem tailTrace_1038390 : CollatzResearch.WordTrace tailWord_1038390 prefixEnd_1038390 157983163502902971273937 := by
  unfold tailWord_1038390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367074669256115483632539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25248796472065231825413749 2367074669256115483632539)
  ·
    refine ⟨3550612003884173225448809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2367074669256115483632539 3550612003884173225448809)
    ·
      refine ⟨2662959002913129919086607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3550612003884173225448809 2662959002913129919086607)
      ·
        refine ⟨3994438504369694878629911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662959002913129919086607 3994438504369694878629911)
        ·
          refine ⟨5991657756554542317944867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994438504369694878629911 5991657756554542317944867)
          ·
            refine ⟨8987486634831813476917301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5991657756554542317944867 8987486634831813476917301)
            ·
              refine ⟨842576872015482513460997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8987486634831813476917301 842576872015482513460997)
              ·
                refine ⟨157983163502902971273937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 842576872015482513460997 157983163502902971273937)
                ·
                  rfl

theorem cell20_1038390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1038390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038390 prefixEnd_1038390 := by exact prefixLift 1038390
  have htrace : WordTrace (prefixWord ++ tailWord_1038390) baseStart_1038390 baseEnd_1038390 := by
    simpa [prefixWord, tailWord_1038390, baseEnd_1038390] using wordTrace_append hprefix tailTrace_1038390
  have hstable : (prefixWord ++ tailWord_1038390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038390).length < 2 ^ (prefixWord ++ tailWord_1038390).sum := by decide
  have hdescent : baseEnd_1038390 < baseStart_1038390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038425 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_1038425 : Nat := 118140960795 + 1038425 * 2 ^ 59
def prefixEnd_1038425 : Nat := 4983230072969 + 3 ^ 40 * 1038425 * 2
def baseEnd_1038425 : Nat := 473965465462404347655001

theorem tailTrace_1038425 : CollatzResearch.WordTrace tailWord_1038425 prefixEnd_1038425 473965465462404347655001 := by
  unfold tailWord_1038425
  simp only [CollatzResearch.WordTrace]
  refine ⟨37874471262971048715644729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25249647508647365810429819 37874471262971048715644729)
  ·
    refine ⟨28405853447228286536733547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37874471262971048715644729 28405853447228286536733547)
    ·
      refine ⟨42608780170842429805100321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28405853447228286536733547 42608780170842429805100321)
      ·
        refine ⟨31956585128131822353825241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42608780170842429805100321 31956585128131822353825241)
        ·
          refine ⟨23967438846098866765368931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31956585128131822353825241 23967438846098866765368931)
          ·
            refine ⟨35951158269148300148053397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23967438846098866765368931 35951158269148300148053397)
            ·
              refine ⟨1685210543866326569440003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35951158269148300148053397 1685210543866326569440003)
              ·
                refine ⟨2527815815799489854160005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685210543866326569440003 2527815815799489854160005)
                ·
                  refine ⟨473965465462404347655001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2527815815799489854160005 473965465462404347655001)
                  ·
                    rfl

theorem cell20_1038425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_1038425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038425 prefixEnd_1038425 := by exact prefixLift 1038425
  have htrace : WordTrace (prefixWord ++ tailWord_1038425) baseStart_1038425 baseEnd_1038425 := by
    simpa [prefixWord, tailWord_1038425, baseEnd_1038425] using wordTrace_append hprefix tailTrace_1038425
  have hstable : (prefixWord ++ tailWord_1038425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038425).length < 2 ^ (prefixWord ++ tailWord_1038425).sum := by decide
  have hdescent : baseEnd_1038425 < baseStart_1038425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038487 : List Nat := [1, 1, 3, 3, 4, 1, 2, 5]
def baseStart_1038487 : Nat := 118140960795 + 1038487 * 2 ^ 59
def prefixEnd_1038487 : Nat := 4983230072969 + 3 ^ 40 * 1038487 * 2
def baseEnd_1038487 : Nat := 157997921317269229196027

theorem tailTrace_1038487 : CollatzResearch.WordTrace tailWord_1038487 prefixEnd_1038487 157997921317269229196027 := by
  unfold tailWord_1038487
  simp only [CollatzResearch.WordTrace]
  refine ⟨37876732588746433304401715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25251155059164288869601143 37876732588746433304401715)
  ·
    refine ⟨56815098883119649956602573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37876732588746433304401715 56815098883119649956602573)
    ·
      refine ⟨21305662081169868733725965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56815098883119649956602573 21305662081169868733725965)
      ·
        refine ⟨7989623280438700775147237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21305662081169868733725965 7989623280438700775147237)
        ·
          refine ⟨1498054365082256395340107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7989623280438700775147237 1498054365082256395340107)
          ·
            refine ⟨2247081547623384593010161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498054365082256395340107 2247081547623384593010161)
            ·
              refine ⟨1685311160717538444757621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247081547623384593010161 1685311160717538444757621)
              ·
                refine ⟨157997921317269229196027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1685311160717538444757621 157997921317269229196027)
                ·
                  rfl

theorem cell20_1038487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_1038487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038487 prefixEnd_1038487 := by exact prefixLift 1038487
  have htrace : WordTrace (prefixWord ++ tailWord_1038487) baseStart_1038487 baseEnd_1038487 := by
    simpa [prefixWord, tailWord_1038487, baseEnd_1038487] using wordTrace_append hprefix tailTrace_1038487
  have hstable : (prefixWord ++ tailWord_1038487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038487).length < 2 ^ (prefixWord ++ tailWord_1038487).sum := by decide
  have hdescent : baseEnd_1038487 < baseStart_1038487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038591 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 5]
def baseStart_1038591 : Nat := 118140960795 + 1038591 * 2 ^ 59
def prefixEnd_1038591 : Nat := 4983230072969 + 3 ^ 40 * 1038591 * 2
def baseEnd_1038591 : Nat := 474041232385645548120989

theorem tailTrace_1038591 : CollatzResearch.WordTrace tailWord_1038591 prefixEnd_1038591 474041232385645548120989 := by
  unfold tailWord_1038591
  simp only [CollatzResearch.WordTrace]
  refine ⟨37880525780369659066187627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25253683853579772710791751 37880525780369659066187627)
  ·
    refine ⟨56820788670554488599281441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37880525780369659066187627 56820788670554488599281441)
    ·
      refine ⟨42615591502915866449461081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56820788670554488599281441 42615591502915866449461081)
      ·
        refine ⟨31961693627186899837095811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42615591502915866449461081 31961693627186899837095811)
        ·
          refine ⟨47942540440780349755643717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31961693627186899837095811 47942540440780349755643717)
          ·
            refine ⟨8989226332646315579183197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47942540440780349755643717 8989226332646315579183197)
            ·
              refine ⟨3370959874742368342193699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8989226332646315579183197 3370959874742368342193699)
              ·
                refine ⟨5056439812113552513290549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3370959874742368342193699 5056439812113552513290549)
                ·
                  refine ⟨474041232385645548120989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5056439812113552513290549 474041232385645548120989)
                  ·
                    rfl

theorem cell20_1038591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_1038591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038591 prefixEnd_1038591 := by exact prefixLift 1038591
  have htrace : WordTrace (prefixWord ++ tailWord_1038591) baseStart_1038591 baseEnd_1038591 := by
    simpa [prefixWord, tailWord_1038591, baseEnd_1038591] using wordTrace_append hprefix tailTrace_1038591
  have hstable : (prefixWord ++ tailWord_1038591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038591).length < 2 ^ (prefixWord ++ tailWord_1038591).sum := by decide
  have hdescent : baseEnd_1038591 < baseStart_1038591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038594 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1038594 : Nat := 118140960795 + 1038594 * 2 ^ 59
def prefixEnd_1038594 : Nat := 4983230072969 + 3 ^ 40 * 1038594 * 2
def baseEnd_1038594 : Nat := 474042601667390871020977

theorem tailTrace_1038594 : CollatzResearch.WordTrace tailWord_1038594 prefixEnd_1038594 474042601667390871020977 := by
  unfold tailWord_1038594
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470158799839697644636709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25253756799572527052364557 9470158799839697644636709)
  ·
    refine ⟨1775654774969943308369383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9470158799839697644636709 1775654774969943308369383)
    ·
      refine ⟨2663482162454914962554075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775654774969943308369383 2663482162454914962554075)
      ·
        refine ⟨3995223243682372443831113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2663482162454914962554075 3995223243682372443831113)
        ·
          refine ⟨2996417432761779332873335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3995223243682372443831113 2996417432761779332873335)
          ·
            refine ⟨4494626149142668999310003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2996417432761779332873335 4494626149142668999310003)
            ·
              refine ⟨6741939223714003498965005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4494626149142668999310003 6741939223714003498965005)
              ·
                refine ⟨2528227208892751312111877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6741939223714003498965005 2528227208892751312111877)
                ·
                  refine ⟨474042601667390871020977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528227208892751312111877 474042601667390871020977)
                  ·
                    rfl

theorem cell20_1038594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1038594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038594 prefixEnd_1038594 := by exact prefixLift 1038594
  have htrace : WordTrace (prefixWord ++ tailWord_1038594) baseStart_1038594 baseEnd_1038594 := by
    simpa [prefixWord, tailWord_1038594, baseEnd_1038594] using wordTrace_append hprefix tailTrace_1038594
  have hstable : (prefixWord ++ tailWord_1038594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038594).length < 2 ^ (prefixWord ++ tailWord_1038594).sum := by decide
  have hdescent : baseEnd_1038594 < baseStart_1038594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038615 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_1038615 : Nat := 118140960795 + 1038615 * 2 ^ 59
def prefixEnd_1038615 : Nat := 4983230072969 + 3 ^ 40 * 1038615 * 2
def baseEnd_1038615 : Nat := 474052186639608131320891

theorem tailTrace_1038615 : CollatzResearch.WordTrace tailWord_1038615 prefixEnd_1038615 474052186639608131320891 := by
  unfold tailWord_1038615
  simp only [CollatzResearch.WordTrace]
  refine ⟨37881401132282711165061299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25254267421521807443374199 37881401132282711165061299)
  ·
    refine ⟨56822101698424066747591949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37881401132282711165061299 56822101698424066747591949)
    ·
      refine ⟨21308288136909025030346981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56822101698424066747591949 21308288136909025030346981)
      ·
        refine ⟨3995304025670442193190059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21308288136909025030346981 3995304025670442193190059)
        ·
          refine ⟨5992956038505663289785089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995304025670442193190059 5992956038505663289785089)
          ·
            refine ⟨4494717028879247467338817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5992956038505663289785089 4494717028879247467338817)
            ·
              refine ⟨3371037771659435600504113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4494717028879247467338817 3371037771659435600504113)
              ·
                refine ⟨2528278328744576700378085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371037771659435600504113 2528278328744576700378085)
                ·
                  refine ⟨474052186639608131320891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528278328744576700378085 474052186639608131320891)
                  ·
                    rfl

theorem cell20_1038615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_1038615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038615 prefixEnd_1038615 := by exact prefixLift 1038615
  have htrace : WordTrace (prefixWord ++ tailWord_1038615) baseStart_1038615 baseEnd_1038615 := by
    simpa [prefixWord, tailWord_1038615, baseEnd_1038615] using wordTrace_append hprefix tailTrace_1038615
  have hstable : (prefixWord ++ tailWord_1038615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038615).length < 2 ^ (prefixWord ++ tailWord_1038615).sum := by decide
  have hdescent : baseEnd_1038615 < baseStart_1038615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038618 : List Nat := [3, 1, 1, 3, 4, 2, 2, 4]
def baseStart_1038618 : Nat := 118140960795 + 1038618 * 2 ^ 59
def prefixEnd_1038618 : Nat := 4983230072969 + 3 ^ 40 * 1038618 * 2
def baseEnd_1038618 : Nat := 158017851973784484740293

theorem tailTrace_1038618 : CollatzResearch.WordTrace tailWord_1038618 prefixEnd_1038618 158017851973784484740293 := by
  unfold tailWord_1038618
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470377637817960669355127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25254340367514561784947005 9470377637817960669355127)
  ·
    refine ⟨14205566456726941004032691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9470377637817960669355127 14205566456726941004032691)
    ·
      refine ⟨21308349685090411506049037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14205566456726941004032691 21308349685090411506049037)
      ·
        refine ⟨7990631131908904314768389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21308349685090411506049037 7990631131908904314768389)
        ·
          refine ⟨1498243337232919559019073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7990631131908904314768389 1498243337232919559019073)
          ·
            refine ⟨1123682502924689669264305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498243337232919559019073 1123682502924689669264305)
            ·
              refine ⟨842761877193517251948229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123682502924689669264305 842761877193517251948229)
              ·
                refine ⟨158017851973784484740293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 842761877193517251948229 158017851973784484740293)
                ·
                  rfl

theorem cell20_1038618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_1038618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038618 prefixEnd_1038618 := by exact prefixLift 1038618
  have htrace : WordTrace (prefixWord ++ tailWord_1038618) baseStart_1038618 baseEnd_1038618 := by
    simpa [prefixWord, tailWord_1038618, baseEnd_1038618] using wordTrace_append hprefix tailTrace_1038618
  have hstable : (prefixWord ++ tailWord_1038618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038618).length < 2 ^ (prefixWord ++ tailWord_1038618).sum := by decide
  have hdescent : baseEnd_1038618 < baseStart_1038618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038636 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1038636 : Nat := 118140960795 + 1038636 * 2 ^ 59
def prefixEnd_1038636 : Nat := 4983230072969 + 3 ^ 40 * 1038636 * 2
def baseEnd_1038636 : Nat := 474061771611825391620805

theorem tailTrace_1038636 : CollatzResearch.WordTrace tailWord_1038636 prefixEnd_1038636 474061771611825391620805 := by
  unfold tailWord_1038636
  simp only [CollatzResearch.WordTrace]
  refine ⟨18941083532603315875787881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25254778043471087834383841 18941083532603315875787881)
  ·
    refine ⟨14205812649452486906840911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18941083532603315875787881 14205812649452486906840911)
    ·
      refine ⟨21308718974178730360261367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14205812649452486906840911 21308718974178730360261367)
      ·
        refine ⟨31963078461268095540392051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21308718974178730360261367 31963078461268095540392051)
        ·
          refine ⟨47944617691902143310588077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31963078461268095540392051 47944617691902143310588077)
          ·
            refine ⟨17979231634463303741470529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47944617691902143310588077 17979231634463303741470529)
            ·
              refine ⟨13484423725847477806102897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17979231634463303741470529 13484423725847477806102897)
              ·
                refine ⟨10113317794385608354577173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13484423725847477806102897 10113317794385608354577173)
                ·
                  refine ⟨474061771611825391620805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10113317794385608354577173 474061771611825391620805)
                  ·
                    rfl

theorem cell20_1038636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1038636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038636 prefixEnd_1038636 := by exact prefixLift 1038636
  have htrace : WordTrace (prefixWord ++ tailWord_1038636) baseStart_1038636 baseEnd_1038636 := by
    simpa [prefixWord, tailWord_1038636, baseEnd_1038636] using wordTrace_append hprefix tailTrace_1038636
  have hstable : (prefixWord ++ tailWord_1038636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038636).length < 2 ^ (prefixWord ++ tailWord_1038636).sum := by decide
  have hdescent : baseEnd_1038636 < baseStart_1038636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038698 : List Nat := [3, 1, 3, 3, 1, 9]
def baseStart_1038698 : Nat := 118140960795 + 1038698 * 2 ^ 59
def prefixEnd_1038698 : Nat := 4983230072969 + 3 ^ 40 * 1038698 * 2
def baseEnd_1038698 : Nat := 17558891485230693761255

theorem tailTrace_1038698 : CollatzResearch.WordTrace tailWord_1038698 prefixEnd_1038698 17558891485230693761255 := by
  unfold tailWord_1038698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471107097745504085083187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25256285593988010893555165 9471107097745504085083187)
  ·
    refine ⟨14206660646618256127624781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9471107097745504085083187 14206660646618256127624781)
    ·
      refine ⟨5327497742481846047859293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14206660646618256127624781 5327497742481846047859293)
      ·
        refine ⟨1997811653430692267947235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5327497742481846047859293 1997811653430692267947235)
        ·
          refine ⟨2996717480146038401920853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1997811653430692267947235 2996717480146038401920853)
          ·
            refine ⟨17558891485230693761255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2996717480146038401920853 17558891485230693761255)
            ·
              rfl

theorem cell20_1038698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 9].length) (baseStart_1038698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038698 prefixEnd_1038698 := by exact prefixLift 1038698
  have htrace : WordTrace (prefixWord ++ tailWord_1038698) baseStart_1038698 baseEnd_1038698 := by
    simpa [prefixWord, tailWord_1038698, baseEnd_1038698] using wordTrace_append hprefix tailTrace_1038698
  have hstable : (prefixWord ++ tailWord_1038698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038698).length < 2 ^ (prefixWord ++ tailWord_1038698).sum := by decide
  have hdescent : baseEnd_1038698 < baseStart_1038698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038729 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 4]
def baseStart_1038729 : Nat := 118140960795 + 1038729 * 2 ^ 59
def prefixEnd_1038729 : Nat := 4983230072969 + 3 ^ 40 * 1038729 * 2
def baseEnd_1038729 : Nat := 474104219345930401520425

theorem tailTrace_1038729 : CollatzResearch.WordTrace tailWord_1038729 prefixEnd_1038729 474104219345930401520425 := by
  unfold tailWord_1038729
  simp only [CollatzResearch.WordTrace]
  refine ⟨37885559053869708634711241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25257039369246472423140827 37885559053869708634711241)
  ·
    refine ⟨28414169290402281476033431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37885559053869708634711241 28414169290402281476033431)
    ·
      refine ⟨42621253935603422214050147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28414169290402281476033431 42621253935603422214050147)
      ·
        refine ⟨63931880903405133321075221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42621253935603422214050147 63931880903405133321075221)
        ·
          refine ⟨2996806917347115624425401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63931880903405133321075221 2996806917347115624425401)
          ·
            refine ⟨2247605188010336718319051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2996806917347115624425401 2247605188010336718319051)
            ·
              refine ⟨3371407782015505077478577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2247605188010336718319051 3371407782015505077478577)
              ·
                refine ⟨2528555836511628808108933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3371407782015505077478577 2528555836511628808108933)
                ·
                  refine ⟨474104219345930401520425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528555836511628808108933 474104219345930401520425)
                  ·
                    rfl

theorem cell20_1038729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_1038729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038729 prefixEnd_1038729 := by exact prefixLift 1038729
  have htrace : WordTrace (prefixWord ++ tailWord_1038729) baseStart_1038729 baseEnd_1038729 := by
    simpa [prefixWord, tailWord_1038729, baseEnd_1038729] using wordTrace_append hprefix tailTrace_1038729
  have hstable : (prefixWord ++ tailWord_1038729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038729).length < 2 ^ (prefixWord ++ tailWord_1038729).sum := by decide
  have hdescent : baseEnd_1038729 < baseStart_1038729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038746 : List Nat := [3, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_1038746 : Nat := 118140960795 + 1038746 * 2 ^ 59
def prefixEnd_1038746 : Nat := 4983230072969 + 3 ^ 40 * 1038746 * 2
def baseEnd_1038746 : Nat := 474111978609153897953689

theorem tailTrace_1038746 : CollatzResearch.WordTrace tailWord_1038746 prefixEnd_1038746 474111978609153897953689 := by
  unfold tailWord_1038746
  simp only [CollatzResearch.WordTrace]
  refine ⟨9471544773702030134520023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25257452729872080358720061 9471544773702030134520023)
  ·
    refine ⟨14207317160553045201780035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9471544773702030134520023 14207317160553045201780035)
    ·
      refine ⟨21310975740829567802670053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14207317160553045201780035 21310975740829567802670053)
      ·
        refine ⟨3995807951405543963000635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21310975740829567802670053 3995807951405543963000635)
        ·
          refine ⟨5993711927108315944500953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3995807951405543963000635 5993711927108315944500953)
          ·
            refine ⟨4495283945331236958375715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5993711927108315944500953 4495283945331236958375715)
            ·
              refine ⟨6742925917996855437563573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4495283945331236958375715 6742925917996855437563573)
              ·
                refine ⟨632149304812205197271585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6742925917996855437563573 632149304812205197271585)
                ·
                  refine ⟨474111978609153897953689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632149304812205197271585 474111978609153897953689)
                  ·
                    rfl

theorem cell20_1038746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_1038746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038746 prefixEnd_1038746 := by exact prefixLift 1038746
  have htrace : WordTrace (prefixWord ++ tailWord_1038746) baseStart_1038746 baseEnd_1038746 := by
    simpa [prefixWord, tailWord_1038746, baseEnd_1038746] using wordTrace_append hprefix tailTrace_1038746
  have hstable : (prefixWord ++ tailWord_1038746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038746).length < 2 ^ (prefixWord ++ tailWord_1038746).sum := by decide
  have hdescent : baseEnd_1038746 < baseStart_1038746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038753 : List Nat := [1, 2, 3, 5, 1, 1, 7]
def baseStart_1038753 : Nat := 118140960795 + 1038753 * 2 ^ 59
def prefixEnd_1038753 : Nat := 4983230072969 + 3 ^ 40 * 1038753 * 2
def baseEnd_1038753 : Nat := 52679463733321442746703

theorem tailTrace_1038753 : CollatzResearch.WordTrace tailWord_1038753 prefixEnd_1038753 52679463733321442746703 := by
  unfold tailWord_1038753
  simp only [CollatzResearch.WordTrace]
  refine ⟨37886434405782760733584913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25257622937188507155723275 37886434405782760733584913)
  ·
    refine ⟨28414825804337070550188685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37886434405782760733584913 28414825804337070550188685)
    ·
      refine ⟨10655559676626401456320757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28414825804337070550188685 10655559676626401456320757)
      ·
        refine ⟨998958719683725136530071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10655559676626401456320757 998958719683725136530071)
        ·
          refine ⟨1498438079525587704795107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998958719683725136530071 1498438079525587704795107)
          ·
            refine ⟨2247657119288381557192661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498438079525587704795107 2247657119288381557192661)
            ·
              refine ⟨52679463733321442746703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2247657119288381557192661 52679463733321442746703)
              ·
                rfl

theorem cell20_1038753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 7].length) (baseStart_1038753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038753 prefixEnd_1038753 := by exact prefixLift 1038753
  have htrace : WordTrace (prefixWord ++ tailWord_1038753) baseStart_1038753 baseEnd_1038753 := by
    simpa [prefixWord, tailWord_1038753, baseEnd_1038753] using wordTrace_append hprefix tailTrace_1038753
  have hstable : (prefixWord ++ tailWord_1038753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038753).length < 2 ^ (prefixWord ++ tailWord_1038753).sum := by decide
  have hdescent : baseEnd_1038753 < baseStart_1038753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038757 : List Nat := [1, 3, 1, 2, 1, 1, 11]
def baseStart_1038757 : Nat := 118140960795 + 1038757 * 2 ^ 59
def prefixEnd_1038757 : Nat := 4983230072969 + 3 ^ 40 * 1038757 * 2
def baseEnd_1038757 : Nat := 52679666589876305398553

theorem tailTrace_1038757 : CollatzResearch.WordTrace tailWord_1038757 prefixEnd_1038757 52679666589876305398553 := by
  unfold tailWord_1038757
  simp only [CollatzResearch.WordTrace]
  refine ⟨37886580297768269416730525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25257720198512179611153683 37886580297768269416730525)
  ·
    refine ⟨14207467611663101031273947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37886580297768269416730525 14207467611663101031273947)
    ·
      refine ⟨21311201417494651546910921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14207467611663101031273947 21311201417494651546910921)
      ·
        refine ⟨15983401063120988660183191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21311201417494651546910921 15983401063120988660183191)
        ·
          refine ⟨23975101594681482990274787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15983401063120988660183191 23975101594681482990274787)
          ·
            refine ⟨35962652392022224485412181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23975101594681482990274787 35962652392022224485412181)
            ·
              refine ⟨52679666589876305398553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35962652392022224485412181 52679666589876305398553)
              ·
                rfl

theorem cell20_1038757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 11].length) (baseStart_1038757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038757 prefixEnd_1038757 := by exact prefixLift 1038757
  have htrace : WordTrace (prefixWord ++ tailWord_1038757) baseStart_1038757 baseEnd_1038757 := by
    simpa [prefixWord, tailWord_1038757, baseEnd_1038757] using wordTrace_append hprefix tailTrace_1038757
  have hstable : (prefixWord ++ tailWord_1038757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038757).length < 2 ^ (prefixWord ++ tailWord_1038757).sum := by decide
  have hdescent : baseEnd_1038757 < baseStart_1038757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038777 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 3]
def baseStart_1038777 : Nat := 118140960795 + 1038777 * 2 ^ 59
def prefixEnd_1038777 : Nat := 4983230072969 + 3 ^ 40 * 1038777 * 2
def baseEnd_1038777 : Nat := 474126127853855567920229

theorem tailTrace_1038777 : CollatzResearch.WordTrace tailWord_1038777 prefixEnd_1038777 474126127853855567920229 := by
  unfold tailWord_1038777
  simp only [CollatzResearch.WordTrace]
  refine ⟨37887309757695812832458585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25258206505130541888305723 37887309757695812832458585)
  ·
    refine ⟨28415482318271859624343939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37887309757695812832458585 28415482318271859624343939)
    ·
      refine ⟨42623223477407789436515909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28415482318271859624343939 42623223477407789436515909)
      ·
        refine ⟨7991854402013960519346733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42623223477407789436515909 7991854402013960519346733)
        ·
          refine ⟨2996945400755235194755025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7991854402013960519346733 2996945400755235194755025)
          ·
            refine ⟨2247709050566426396066269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2996945400755235194755025 2247709050566426396066269)
            ·
              refine ⟨842890893962409898524851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2247709050566426396066269 842890893962409898524851)
              ·
                refine ⟨1264336340943614847787277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 842890893962409898524851 1264336340943614847787277)
                ·
                  refine ⟨474126127853855567920229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264336340943614847787277 474126127853855567920229)
                  ·
                    rfl

theorem cell20_1038777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_1038777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038777 prefixEnd_1038777 := by exact prefixLift 1038777
  have htrace : WordTrace (prefixWord ++ tailWord_1038777) baseStart_1038777 baseEnd_1038777 := by
    simpa [prefixWord, tailWord_1038777, baseEnd_1038777] using wordTrace_append hprefix tailTrace_1038777
  have hstable : (prefixWord ++ tailWord_1038777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038777).length < 2 ^ (prefixWord ++ tailWord_1038777).sum := by decide
  have hdescent : baseEnd_1038777 < baseStart_1038777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038791 : List Nat := [1, 1, 4, 1, 1, 6, 2, 4]
def baseStart_1038791 : Nat := 118140960795 + 1038791 * 2 ^ 59
def prefixEnd_1038791 : Nat := 4983230072969 + 3 ^ 40 * 1038791 * 2
def baseEnd_1038791 : Nat := 158044172611777913817835

theorem tailTrace_1038791 : CollatzResearch.WordTrace tailWord_1038791 prefixEnd_1038791 158044172611777913817835 := by
  unfold tailWord_1038791
  simp only [CollatzResearch.WordTrace]
  refine ⟨37887820379645093223468227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25258546919763395482312151 37887820379645093223468227)
  ·
    refine ⟨56831730569467639835202341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37887820379645093223468227 56831730569467639835202341)
    ·
      refine ⟨10655949481775182469100439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56831730569467639835202341 10655949481775182469100439)
      ·
        refine ⟨15983924222662773703650659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10655949481775182469100439 15983924222662773703650659)
        ·
          refine ⟨23975886333994160555475989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15983924222662773703650659 23975886333994160555475989)
          ·
            refine ⟨1123869671905976276037937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23975886333994160555475989 1123869671905976276037937)
            ·
              refine ⟨842902253929482207028453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1123869671905976276037937 842902253929482207028453)
              ·
                refine ⟨158044172611777913817835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 842902253929482207028453 158044172611777913817835)
                ·
                  rfl

theorem cell20_1038791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_1038791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038791 prefixEnd_1038791 := by exact prefixLift 1038791
  have htrace : WordTrace (prefixWord ++ tailWord_1038791) baseStart_1038791 baseEnd_1038791 := by
    simpa [prefixWord, tailWord_1038791, baseEnd_1038791] using wordTrace_append hprefix tailTrace_1038791
  have hstable : (prefixWord ++ tailWord_1038791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038791).length < 2 ^ (prefixWord ++ tailWord_1038791).sum := by decide
  have hdescent : baseEnd_1038791 < baseStart_1038791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038818 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1038818 : Nat := 118140960795 + 1038818 * 2 ^ 59
def prefixEnd_1038818 : Nat := 4983230072969 + 3 ^ 40 * 1038818 * 2
def baseEnd_1038818 : Nat := 474144841371041647553395

theorem tailTrace_1038818 : CollatzResearch.WordTrace tailWord_1038818 prefixEnd_1038818 474144841371041647553395 := by
  unfold tailWord_1038818
  simp only [CollatzResearch.WordTrace]
  refine ⟨9472201287636819208675277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25259203433698184556467405 9472201287636819208675277)
  ·
    refine ⟨3552075482863807203253229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9472201287636819208675277 3552075482863807203253229)
    ·
      refine ⟨1332028306073927701219961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3552075482863807203253229 1332028306073927701219961)
      ·
        refine ⟨999021229555445775914971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1332028306073927701219961 999021229555445775914971)
        ·
          refine ⟨1498531844333168663872457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999021229555445775914971 1498531844333168663872457)
          ·
            refine ⟨1123898883249876497904343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498531844333168663872457 1123898883249876497904343)
            ·
              refine ⟨1685848324874814746856515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123898883249876497904343 1685848324874814746856515)
              ·
                refine ⟨2528772487312222120284773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685848324874814746856515 2528772487312222120284773)
                ·
                  refine ⟨474144841371041647553395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2528772487312222120284773 474144841371041647553395)
                  ·
                    rfl

theorem cell20_1038818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1038818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038818 prefixEnd_1038818 := by exact prefixLift 1038818
  have htrace : WordTrace (prefixWord ++ tailWord_1038818) baseStart_1038818 baseEnd_1038818 := by
    simpa [prefixWord, tailWord_1038818, baseEnd_1038818] using wordTrace_append hprefix tailTrace_1038818
  have hstable : (prefixWord ++ tailWord_1038818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038818).length < 2 ^ (prefixWord ++ tailWord_1038818).sum := by decide
  have hdescent : baseEnd_1038818 < baseStart_1038818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038829 : List Nat := [1, 5, 1, 3, 1, 2, 2, 5]
def baseStart_1038829 : Nat := 118140960795 + 1038829 * 2 ^ 59
def prefixEnd_1038829 : Nat := 4983230072969 + 3 ^ 40 * 1038829 * 2
def baseEnd_1038829 : Nat := 158049954023591499395561

theorem tailTrace_1038829 : CollatzResearch.WordTrace tailWord_1038829 prefixEnd_1038829 158049954023591499395561 := by
  unfold tailWord_1038829
  simp only [CollatzResearch.WordTrace]
  refine ⟨37889206353507425713351541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25259470902338283808901027 37889206353507425713351541)
  ·
    refine ⟨3552113095641321160626707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37889206353507425713351541 3552113095641321160626707)
    ·
      refine ⟨5328169643461981740940061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552113095641321160626707 5328169643461981740940061)
      ·
        refine ⟨1998063616298243152852523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5328169643461981740940061 1998063616298243152852523)
        ·
          refine ⟨2997095424447364729278785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1998063616298243152852523 2997095424447364729278785)
          ·
            refine ⟨2247821568335523546959089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997095424447364729278785 2247821568335523546959089)
            ·
              refine ⟨1685866176251642660219317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247821568335523546959089 1685866176251642660219317)
              ·
                refine ⟨158049954023591499395561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1685866176251642660219317 158049954023591499395561)
                ·
                  rfl

theorem cell20_1038829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_1038829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038829 prefixEnd_1038829 := by exact prefixLift 1038829
  have htrace : WordTrace (prefixWord ++ tailWord_1038829) baseStart_1038829 baseEnd_1038829 := by
    simpa [prefixWord, tailWord_1038829, baseEnd_1038829] using wordTrace_append hprefix tailTrace_1038829
  have hstable : (prefixWord ++ tailWord_1038829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038829).length < 2 ^ (prefixWord ++ tailWord_1038829).sum := by decide
  have hdescent : baseEnd_1038829 < baseStart_1038829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038877 : List Nat := [1, 4, 2, 2, 1, 2, 4, 2, 2]
def baseStart_1038877 : Nat := 118140960795 + 1038877 * 2 ^ 59
def prefixEnd_1038877 : Nat := 4983230072969 + 3 ^ 40 * 1038877 * 2
def baseEnd_1038877 : Nat := 474171770578699664586487

theorem tailTrace_1038877 : CollatzResearch.WordTrace tailWord_1038877 prefixEnd_1038877 474171770578699664586487 := by
  unfold tailWord_1038877
  simp only [CollatzResearch.WordTrace]
  refine ⟨37890957057333529911098885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25260638038222353274065923 37890957057333529911098885)
  ·
    refine ⟨7104554448250036858331041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37890957057333529911098885 7104554448250036858331041)
    ·
      refine ⟨5328415836187527643748281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7104554448250036858331041 5328415836187527643748281)
      ·
        refine ⟨3996311877140645732811211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5328415836187527643748281 3996311877140645732811211)
        ·
          refine ⟨5994467815710968599216817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3996311877140645732811211 5994467815710968599216817)
          ·
            refine ⟨4495850861783226449412613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5994467815710968599216817 4495850861783226449412613)
            ·
              refine ⟨842972036584354959264865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4495850861783226449412613 842972036584354959264865)
              ·
                refine ⟨632229027438266219448649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 842972036584354959264865 632229027438266219448649)
                ·
                  refine ⟨474171770578699664586487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632229027438266219448649 474171770578699664586487)
                  ·
                    rfl

theorem cell20_1038877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_1038877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038877 prefixEnd_1038877 := by exact prefixLift 1038877
  have htrace : WordTrace (prefixWord ++ tailWord_1038877) baseStart_1038877 baseEnd_1038877 := by
    simpa [prefixWord, tailWord_1038877, baseEnd_1038877] using wordTrace_append hprefix tailTrace_1038877
  have hstable : (prefixWord ++ tailWord_1038877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038877).length < 2 ^ (prefixWord ++ tailWord_1038877).sum := by decide
  have hdescent : baseEnd_1038877 < baseStart_1038877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038884 : List Nat := [2, 3, 1, 5, 1, 2, 1, 5]
def baseStart_1038884 : Nat := 118140960795 + 1038884 * 2 ^ 59
def prefixEnd_1038884 : Nat := 4983230072969 + 3 ^ 40 * 1038884 * 2
def baseEnd_1038884 : Nat := 158058321856479583784375

theorem tailTrace_1038884 : CollatzResearch.WordTrace tailWord_1038884 prefixEnd_1038884 158058321856479583784375 := by
  unfold tailWord_1038884
  simp only [CollatzResearch.WordTrace]
  refine ⟨18945606184154085053301853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25260808245538780071069137 18945606184154085053301853)
  ·
    refine ⟨7104602319057781894988195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18945606184154085053301853 7104602319057781894988195)
    ·
      refine ⟨10656903478586672842482293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7104602319057781894988195 10656903478586672842482293)
      ·
        refine ⟨999084701117500578982715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10656903478586672842482293 999084701117500578982715)
        ·
          refine ⟨1498627051676250868474073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999084701117500578982715 1498627051676250868474073)
          ·
            refine ⟨1123970288757188151355555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1498627051676250868474073 1123970288757188151355555)
            ·
              refine ⟨1685955433135782227033333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123970288757188151355555 1685955433135782227033333)
              ·
                refine ⟨158058321856479583784375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1685955433135782227033333 158058321856479583784375)
                ·
                  rfl

theorem cell20_1038884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_1038884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038884 prefixEnd_1038884 := by exact prefixLift 1038884
  have htrace : WordTrace (prefixWord ++ tailWord_1038884) baseStart_1038884 baseEnd_1038884 := by
    simpa [prefixWord, tailWord_1038884, baseEnd_1038884] using wordTrace_append hprefix tailTrace_1038884
  have hstable : (prefixWord ++ tailWord_1038884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038884).length < 2 ^ (prefixWord ++ tailWord_1038884).sum := by decide
  have hdescent : baseEnd_1038884 < baseStart_1038884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038942 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1038942 : Nat := 118140960795 + 1038942 * 2 ^ 59
def prefixEnd_1038942 : Nat := 4983230072969 + 3 ^ 40 * 1038942 * 2
def baseEnd_1038942 : Nat := 474201438349848327419555

theorem tailTrace_1038942 : CollatzResearch.WordTrace tailWord_1038942 prefixEnd_1038942 474201438349848327419555 := by
  unfold tailWord_1038942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4736665975262255751526885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25262218534732030674810053 4736665975262255751526885)
  ·
    refine ⟨888124870361672953411291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4736665975262255751526885 888124870361672953411291)
    ·
      refine ⟨1332187305542509430116937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888124870361672953411291 1332187305542509430116937)
      ·
        refine ⟨999140479156882072587703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1332187305542509430116937 999140479156882072587703)
        ·
          refine ⟨1498710718735323108881555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999140479156882072587703 1498710718735323108881555)
          ·
            refine ⟨2248066078102984663322333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498710718735323108881555 2248066078102984663322333)
            ·
              refine ⟨843024779288619248745875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2248066078102984663322333 843024779288619248745875)
              ·
                refine ⟨1264537168932928873118813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843024779288619248745875 1264537168932928873118813)
                ·
                  refine ⟨474201438349848327419555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264537168932928873118813 474201438349848327419555)
                  ·
                    rfl

theorem cell20_1038942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1038942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038942 prefixEnd_1038942 := by exact prefixLift 1038942
  have htrace : WordTrace (prefixWord ++ tailWord_1038942) baseStart_1038942 baseEnd_1038942 := by
    simpa [prefixWord, tailWord_1038942, baseEnd_1038942] using wordTrace_append hprefix tailTrace_1038942
  have hstable : (prefixWord ++ tailWord_1038942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038942).length < 2 ^ (prefixWord ++ tailWord_1038942).sum := by decide
  have hdescent : baseEnd_1038942 < baseStart_1038942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038947 : List Nat := [1, 1, 1, 5, 1, 2, 2, 7]
def baseStart_1038947 : Nat := 118140960795 + 1038947 * 2 ^ 59
def prefixEnd_1038947 : Nat := 4983230072969 + 3 ^ 40 * 1038947 * 2
def baseEnd_1038947 : Nat := 158067906828696844084289

theorem tailTrace_1038947 : CollatzResearch.WordTrace tailWord_1038947 prefixEnd_1038947 158067906828696844084289 := by
  unfold tailWord_1038947
  simp only [CollatzResearch.WordTrace]
  refine ⟨37893510167079931866147095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25262340111386621244098063 37893510167079931866147095)
  ·
    refine ⟨56840265250619897799220643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37893510167079931866147095 56840265250619897799220643)
    ·
      refine ⟨85260397875929846698830965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56840265250619897799220643 85260397875929846698830965)
      ·
        refine ⟨7993162300868423128015403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85260397875929846698830965 7993162300868423128015403)
        ·
          refine ⟨11989743451302634692023105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993162300868423128015403 11989743451302634692023105)
          ·
            refine ⟨8992307588476976019017329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11989743451302634692023105 8992307588476976019017329)
            ·
              refine ⟨6744230691357732014262997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8992307588476976019017329 6744230691357732014262997)
              ·
                refine ⟨158067906828696844084289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6744230691357732014262997 158067906828696844084289)
                ·
                  rfl

theorem cell20_1038947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_1038947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038947 prefixEnd_1038947 := by exact prefixLift 1038947
  have htrace : WordTrace (prefixWord ++ tailWord_1038947) baseStart_1038947 baseEnd_1038947 := by
    simpa [prefixWord, tailWord_1038947, baseEnd_1038947] using wordTrace_append hprefix tailTrace_1038947
  have hstable : (prefixWord ++ tailWord_1038947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038947).length < 2 ^ (prefixWord ++ tailWord_1038947).sum := by decide
  have hdescent : baseEnd_1038947 < baseStart_1038947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038957 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_1038957 : Nat := 118140960795 + 1038957 * 2 ^ 59
def prefixEnd_1038957 : Nat := 4983230072969 + 3 ^ 40 * 1038957 * 2
def baseEnd_1038957 : Nat := 474208284758574941919493

theorem tailTrace_1038957 : CollatzResearch.WordTrace tailWord_1038957 prefixEnd_1038957 474208284758574941919493 := by
  unfold tailWord_1038957
  simp only [CollatzResearch.WordTrace]
  refine ⟨37893874897043703574011125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25262583264695802382674083 37893874897043703574011125)
  ·
    refine ⟨3552550771597847210063543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37893874897043703574011125 3552550771597847210063543)
    ·
      refine ⟨5328826157396770815095315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552550771597847210063543 5328826157396770815095315)
      ·
        refine ⟨7993239236095156222642973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5328826157396770815095315 7993239236095156222642973)
        ·
          refine ⟨2997464713535683583491115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7993239236095156222642973 2997464713535683583491115)
          ·
            refine ⟨4496197070303525375236673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2997464713535683583491115 4496197070303525375236673)
            ·
              refine ⟨3372147802727644031427505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496197070303525375236673 3372147802727644031427505)
              ·
                refine ⟨2529110852045733023570629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3372147802727644031427505 2529110852045733023570629)
                ·
                  refine ⟨474208284758574941919493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529110852045733023570629 474208284758574941919493)
                  ·
                    rfl

theorem cell20_1038957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_1038957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038957 prefixEnd_1038957 := by exact prefixLift 1038957
  have htrace : WordTrace (prefixWord ++ tailWord_1038957) baseStart_1038957 baseEnd_1038957 := by
    simpa [prefixWord, tailWord_1038957, baseEnd_1038957] using wordTrace_append hprefix tailTrace_1038957
  have hstable : (prefixWord ++ tailWord_1038957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038957).length < 2 ^ (prefixWord ++ tailWord_1038957).sum := by decide
  have hdescent : baseEnd_1038957 < baseStart_1038957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1038960 : List Nat := [2, 1, 1, 1, 8, 1, 2, 4]
def baseStart_1038960 : Nat := 118140960795 + 1038960 * 2 ^ 59
def prefixEnd_1038960 : Nat := 4983230072969 + 3 ^ 40 * 1038960 * 2
def baseEnd_1038960 : Nat := 158069884680106754939827

theorem tailTrace_1038960 : CollatzResearch.WordTrace tailWord_1038960 prefixEnd_1038960 158069884680106754939827 := by
  unfold tailWord_1038960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18946992158016417543185167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25262656210688556724246889 18946992158016417543185167)
  ·
    refine ⟨28420488237024626314777751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18946992158016417543185167 28420488237024626314777751)
    ·
      refine ⟨42630732355536939472166627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28420488237024626314777751 42630732355536939472166627)
      ·
        refine ⟨63946098533305409208249941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42630732355536939472166627 63946098533305409208249941)
        ·
          refine ⟨749368342187172764159179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 63946098533305409208249941 749368342187172764159179)
          ·
            refine ⟨1124052513280759146238769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749368342187172764159179 1124052513280759146238769)
            ·
              refine ⟨843039384960569359679077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124052513280759146238769 843039384960569359679077)
              ·
                refine ⟨158069884680106754939827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843039384960569359679077 158069884680106754939827)
                ·
                  rfl

theorem cell20_1038960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_1038960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1038960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1038960 prefixEnd_1038960 := by exact prefixLift 1038960
  have htrace : WordTrace (prefixWord ++ tailWord_1038960) baseStart_1038960 baseEnd_1038960 := by
    simpa [prefixWord, tailWord_1038960, baseEnd_1038960] using wordTrace_append hprefix tailTrace_1038960
  have hstable : (prefixWord ++ tailWord_1038960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1038960).length < 2 ^ (prefixWord ++ tailWord_1038960).sum := by decide
  have hdescent : baseEnd_1038960 < baseStart_1038960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1038960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039023 : List Nat := [1, 1, 2, 1, 2, 5, 2, 6]
def baseStart_1039023 : Nat := 118140960795 + 1039023 * 2 ^ 59
def prefixEnd_1039023 : Nat := 4983230072969 + 3 ^ 40 * 1039023 * 2
def baseEnd_1039023 : Nat := 158079469652324015239741

theorem tailTrace_1039023 : CollatzResearch.WordTrace tailWord_1039023 prefixEnd_1039023 158079469652324015239741 := by
  unfold tailWord_1039023
  simp only [CollatzResearch.WordTrace]
  refine ⟨37896282114804596845913723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25264188076536397897275815 37896282114804596845913723)
  ·
    refine ⟨56844423172206895268870585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37896282114804596845913723 56844423172206895268870585)
    ·
      refine ⟨42633317379155171451652939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56844423172206895268870585 42633317379155171451652939)
      ·
        refine ⟨63949976068732757177479409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42633317379155171451652939 63949976068732757177479409)
        ·
          refine ⟨47962482051549567883109557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63949976068732757177479409 47962482051549567883109557)
          ·
            refine ⟨4496482692332771989041521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47962482051549567883109557 4496482692332771989041521)
            ·
              refine ⟨3372362019249578991781141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4496482692332771989041521 3372362019249578991781141)
              ·
                refine ⟨158079469652324015239741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3372362019249578991781141 158079469652324015239741)
                ·
                  rfl

theorem cell20_1039023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_1039023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039023 prefixEnd_1039023 := by exact prefixLift 1039023
  have htrace : WordTrace (prefixWord ++ tailWord_1039023) baseStart_1039023 baseEnd_1039023 := by
    simpa [prefixWord, tailWord_1039023, baseEnd_1039023] using wordTrace_append hprefix tailTrace_1039023
  have hstable : (prefixWord ++ tailWord_1039023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039023).length < 2 ^ (prefixWord ++ tailWord_1039023).sum := by decide
  have hdescent : baseEnd_1039023 < baseStart_1039023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039033 : List Nat := [1, 2, 1, 4, 1, 1, 1, 7, 2]
def baseStart_1039033 : Nat := 118140960795 + 1039033 * 2 ^ 59
def prefixEnd_1039033 : Nat := 4983230072969 + 3 ^ 40 * 1039033 * 2
def baseEnd_1039033 : Nat := 474242973229456455385849

theorem tailTrace_1039033 : CollatzResearch.WordTrace tailWord_1039033 prefixEnd_1039033 474242973229456455385849 := by
  unfold tailWord_1039033
  simp only [CollatzResearch.WordTrace]
  refine ⟨37896646844768368553777753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25264431229845579035851835 37896646844768368553777753)
  ·
    refine ⟨28422485133576276415333315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37896646844768368553777753 28422485133576276415333315)
    ·
      refine ⟨42633727700364414622999973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28422485133576276415333315 42633727700364414622999973)
      ·
        refine ⟨7993823943818327741812495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42633727700364414622999973 7993823943818327741812495)
        ·
          refine ⟨11990735915727491612718743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7993823943818327741812495 11990735915727491612718743)
          ·
            refine ⟨17986103873591237419078115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11990735915727491612718743 17986103873591237419078115)
            ·
              refine ⟨26979155810386856128617173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17986103873591237419078115 26979155810386856128617173)
              ·
                refine ⟨632323964305941940514465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26979155810386856128617173 632323964305941940514465)
                ·
                  refine ⟨474242973229456455385849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632323964305941940514465 474242973229456455385849)
                  ·
                    rfl

theorem cell20_1039033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_1039033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039033 prefixEnd_1039033 := by exact prefixLift 1039033
  have htrace : WordTrace (prefixWord ++ tailWord_1039033) baseStart_1039033 baseEnd_1039033 := by
    simpa [prefixWord, tailWord_1039033, baseEnd_1039033] using wordTrace_append hprefix tailTrace_1039033
  have hstable : (prefixWord ++ tailWord_1039033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039033).length < 2 ^ (prefixWord ++ tailWord_1039033).sum := by decide
  have hdescent : baseEnd_1039033 < baseStart_1039033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039050 : List Nat := [3, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_1039050 : Nat := 118140960795 + 1039050 * 2 ^ 59
def prefixEnd_1039050 : Nat := 4983230072969 + 3 ^ 40 * 1039050 * 2
def baseEnd_1039050 : Nat := 474250732492679951819113

theorem tailTrace_1039050 : CollatzResearch.WordTrace tailWord_1039050 prefixEnd_1039050 474250732492679951819113 := by
  unfold tailWord_1039050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9474316721426695114286651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25264844590471186971431069 9474316721426695114286651)
  ·
    refine ⟨14211475082140042671429977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9474316721426695114286651 14211475082140042671429977)
    ·
      refine ⟨10658606311605032003572483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14211475082140042671429977 10658606311605032003572483)
      ·
        refine ⟨15987909467407548005358725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10658606311605032003572483 15987909467407548005358725)
        ·
          refine ⟨2997733025138915251004761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15987909467407548005358725 2997733025138915251004761)
          ·
            refine ⟨2248299768854186438253571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997733025138915251004761 2248299768854186438253571)
            ·
              refine ⟨3372449653281279657380357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248299768854186438253571 3372449653281279657380357)
              ·
                refine ⟨632334309990239935758817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3372449653281279657380357 632334309990239935758817)
                ·
                  refine ⟨474250732492679951819113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632334309990239935758817 474250732492679951819113)
                  ·
                    rfl

theorem cell20_1039050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_1039050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039050 prefixEnd_1039050 := by exact prefixLift 1039050
  have htrace : WordTrace (prefixWord ++ tailWord_1039050) baseStart_1039050 baseEnd_1039050 := by
    simpa [prefixWord, tailWord_1039050, baseEnd_1039050] using wordTrace_append hprefix tailTrace_1039050
  have hstable : (prefixWord ++ tailWord_1039050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039050).length < 2 ^ (prefixWord ++ tailWord_1039050).sum := by decide
  have hdescent : baseEnd_1039050 < baseStart_1039050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039053 : List Nat := [1, 6, 2, 1, 3, 1, 1, 5]
def baseStart_1039053 : Nat := 118140960795 + 1039053 * 2 ^ 59
def prefixEnd_1039053 : Nat := 4983230072969 + 3 ^ 40 * 1039053 * 2
def baseEnd_1039053 : Nat := 158084033924808424906367

theorem tailTrace_1039053 : CollatzResearch.WordTrace tailWord_1039053 prefixEnd_1039053 158084033924808424906367 := by
  unfold tailWord_1039053
  simp only [CollatzResearch.WordTrace]
  refine ⟨37897376304695911969505813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25264917536463941313003875 37897376304695911969505813)
  ·
    refine ⟨1776439514282620873570585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37897376304695911969505813 1776439514282620873570585)
    ·
      refine ⟨1332329635711965655177939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1776439514282620873570585 1332329635711965655177939)
      ·
        refine ⟨1998494453567948482766909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332329635711965655177939 1998494453567948482766909)
        ·
          refine ⟨749435420087980681037591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1998494453567948482766909 749435420087980681037591)
          ·
            refine ⟨1124153130131971021556387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749435420087980681037591 1124153130131971021556387)
            ·
              refine ⟨1686229695197956532334581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124153130131971021556387 1686229695197956532334581)
              ·
                refine ⟨158084033924808424906367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1686229695197956532334581 158084033924808424906367)
                ·
                  rfl

theorem cell20_1039053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5].length) (baseStart_1039053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039053 prefixEnd_1039053 := by exact prefixLift 1039053
  have htrace : WordTrace (prefixWord ++ tailWord_1039053) baseStart_1039053 baseEnd_1039053 := by
    simpa [prefixWord, tailWord_1039053, baseEnd_1039053] using wordTrace_append hprefix tailTrace_1039053
  have hstable : (prefixWord ++ tailWord_1039053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039053).length < 2 ^ (prefixWord ++ tailWord_1039053).sum := by decide
  have hdescent : baseEnd_1039053 < baseStart_1039053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039085 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1039085 : Nat := 118140960795 + 1039085 * 2 ^ 59
def prefixEnd_1039085 : Nat := 4983230072969 + 3 ^ 40 * 1039085 * 2
def baseEnd_1039085 : Nat := 474266707446375385652303

theorem tailTrace_1039085 : CollatzResearch.WordTrace tailWord_1039085 prefixEnd_1039085 474266707446375385652303 := by
  unfold tailWord_1039085
  simp only [CollatzResearch.WordTrace]
  refine ⟨37898543440579981434670709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25265695627053320956447139 37898543440579981434670709)
  ·
    refine ⟨3552988447554373259500379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37898543440579981434670709 3552988447554373259500379)
    ·
      refine ⟨5329482671331559889250569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3552988447554373259500379 5329482671331559889250569)
      ·
        refine ⟨3997112003498669916937927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5329482671331559889250569 3997112003498669916937927)
        ·
          refine ⟨5995668005248004875406891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3997112003498669916937927 5995668005248004875406891)
          ·
            refine ⟨8993502007872007313110337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995668005248004875406891 8993502007872007313110337)
            ·
              refine ⟨6745126505904005484832753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8993502007872007313110337 6745126505904005484832753)
              ·
                refine ⟨5058844879428004113624565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6745126505904005484832753 5058844879428004113624565)
                ·
                  refine ⟨474266707446375385652303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058844879428004113624565 474266707446375385652303)
                  ·
                    rfl

theorem cell20_1039085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1039085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039085 prefixEnd_1039085 := by exact prefixLift 1039085
  have htrace : WordTrace (prefixWord ++ tailWord_1039085) baseStart_1039085 baseEnd_1039085 := by
    simpa [prefixWord, tailWord_1039085, baseEnd_1039085] using wordTrace_append hprefix tailTrace_1039085
  have hstable : (prefixWord ++ tailWord_1039085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039085).length < 2 ^ (prefixWord ++ tailWord_1039085).sum := by decide
  have hdescent : baseEnd_1039085 < baseStart_1039085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039102 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1039102 : Nat := 118140960795 + 1039102 * 2 ^ 59
def prefixEnd_1039102 : Nat := 4983230072969 + 3 ^ 40 * 1039102 * 2
def baseEnd_1039102 : Nat := 474274466709598882085567

theorem tailTrace_1039102 : CollatzResearch.WordTrace tailWord_1039102 prefixEnd_1039102 474274466709598882085567 := by
  unfold tailWord_1039102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4737395435189799167254945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25266108987678928892026373 4737395435189799167254945)
  ·
    refine ⟨3553046576392349375441209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4737395435189799167254945 3553046576392349375441209)
    ·
      refine ⟨2664784932294262031580907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3553046576392349375441209 2664784932294262031580907)
      ·
        refine ⟨3997177398441393047371361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2664784932294262031580907 3997177398441393047371361)
        ·
          refine ⟨2997883048831044785528521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3997177398441393047371361 2997883048831044785528521)
          ·
            refine ⟨2248412286623283589146391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2997883048831044785528521 2248412286623283589146391)
            ·
              refine ⟨3372618429934925383719587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248412286623283589146391 3372618429934925383719587)
              ·
                refine ⟨5058927644902388075579381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3372618429934925383719587 5058927644902388075579381)
                ·
                  refine ⟨474274466709598882085567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5058927644902388075579381 474274466709598882085567)
                  ·
                    rfl

theorem cell20_1039102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1039102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039102 prefixEnd_1039102 := by exact prefixLift 1039102
  have htrace : WordTrace (prefixWord ++ tailWord_1039102) baseStart_1039102 baseEnd_1039102 := by
    simpa [prefixWord, tailWord_1039102, baseEnd_1039102] using wordTrace_append hprefix tailTrace_1039102
  have hstable : (prefixWord ++ tailWord_1039102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039102).length < 2 ^ (prefixWord ++ tailWord_1039102).sum := by decide
  have hdescent : baseEnd_1039102 < baseStart_1039102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039130 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1039130 : Nat := 118140960795 + 1039130 * 2 ^ 59
def prefixEnd_1039130 : Nat := 4983230072969 + 3 ^ 40 * 1039130 * 2
def baseEnd_1039130 : Nat := 474287246672555229152119

theorem tailTrace_1039130 : CollatzResearch.WordTrace tailWord_1039130 prefixEnd_1039130 474287246672555229152119 := by
  unfold tailWord_1039130
  simp only [CollatzResearch.WordTrace]
  refine ⟨9475046181354238530014711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25266789816944636080039229 9475046181354238530014711)
  ·
    refine ⟨14212569272031357795022067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9475046181354238530014711 14212569272031357795022067)
    ·
      refine ⟨21318853908047036692533101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14212569272031357795022067 21318853908047036692533101)
      ·
        refine ⟨7994570215517638759699913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21318853908047036692533101 7994570215517638759699913)
        ·
          refine ⟨5995927661638229069774935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7994570215517638759699913 5995927661638229069774935)
          ·
            refine ⟨8993891492457343604662403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5995927661638229069774935 8993891492457343604662403)
            ·
              refine ⟨13490837238686015406993605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8993891492457343604662403 13490837238686015406993605)
              ·
                refine ⟨2529531982253627888811301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13490837238686015406993605 2529531982253627888811301)
                ·
                  refine ⟨474287246672555229152119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2529531982253627888811301 474287246672555229152119)
                  ·
                    rfl

theorem cell20_1039130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1039130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039130 prefixEnd_1039130 := by exact prefixLift 1039130
  have htrace : WordTrace (prefixWord ++ tailWord_1039130) baseStart_1039130 baseEnd_1039130 := by
    simpa [prefixWord, tailWord_1039130, baseEnd_1039130] using wordTrace_append hprefix tailTrace_1039130
  have hstable : (prefixWord ++ tailWord_1039130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039130).length < 2 ^ (prefixWord ++ tailWord_1039130).sum := by decide
  have hdescent : baseEnd_1039130 < baseStart_1039130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039133 : List Nat := [1, 4, 2, 4, 1, 1, 1, 6]
def baseStart_1039133 : Nat := 118140960795 + 1039133 * 2 ^ 59
def prefixEnd_1039133 : Nat := 4983230072969 + 3 ^ 40 * 1039133 * 2
def baseEnd_1039133 : Nat := 158096205318100184017369

theorem tailTrace_1039133 : CollatzResearch.WordTrace tailWord_1039133 prefixEnd_1039133 158096205318100184017369 := by
  unfold tailWord_1039133
  simp only [CollatzResearch.WordTrace]
  refine ⟨37900294144406085632418053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25266862762937390421612035 37900294144406085632418053)
  ·
    refine ⟨7106305152076141056078385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37900294144406085632418053 7106305152076141056078385)
    ·
      refine ⟨5329728864057105792058789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7106305152076141056078385 5329728864057105792058789)
      ·
        refine ⟨999324162010707336011023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5329728864057105792058789 999324162010707336011023)
        ·
          refine ⟨1498986243016061004016535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999324162010707336011023 1498986243016061004016535)
          ·
            refine ⟨2248479364524091506024803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498986243016061004016535 2248479364524091506024803)
            ·
              refine ⟨3372719046786137259037205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248479364524091506024803 3372719046786137259037205)
              ·
                refine ⟨158096205318100184017369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3372719046786137259037205 158096205318100184017369)
                ·
                  rfl

theorem cell20_1039133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_1039133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039133 prefixEnd_1039133 := by exact prefixLift 1039133
  have htrace : WordTrace (prefixWord ++ tailWord_1039133) baseStart_1039133 baseEnd_1039133 := by
    simpa [prefixWord, tailWord_1039133, baseEnd_1039133] using wordTrace_append hprefix tailTrace_1039133
  have hstable : (prefixWord ++ tailWord_1039133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039133).length < 2 ^ (prefixWord ++ tailWord_1039133).sum := by decide
  have hdescent : baseEnd_1039133 < baseStart_1039133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039137 : List Nat := [1, 2, 3, 2, 1, 2, 3, 6]
def baseStart_1039137 : Nat := 118140960795 + 1039137 * 2 ^ 59
def prefixEnd_1039137 : Nat := 4983230072969 + 3 ^ 40 * 1039137 * 2
def baseEnd_1039137 : Nat := 158096813887764771972919

theorem tailTrace_1039137 : CollatzResearch.WordTrace tailWord_1039137 prefixEnd_1039137 158096813887764771972919 := by
  unfold tailWord_1039137
  simp only [CollatzResearch.WordTrace]
  refine ⟨37900440036391594315563665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25266960024261062877042443 37900440036391594315563665)
  ·
    refine ⟨28425330027293695736672749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37900440036391594315563665 28425330027293695736672749)
    ·
      refine ⟨10659498760235135901252281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28425330027293695736672749 10659498760235135901252281)
      ·
        refine ⟨7994624070176351925939211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10659498760235135901252281 7994624070176351925939211)
        ·
          refine ⟨11991936105264527888908817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7994624070176351925939211 11991936105264527888908817)
          ·
            refine ⟨8993952078948395916681613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11991936105264527888908817 8993952078948395916681613)
            ·
              refine ⟨3372732029605648468755605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8993952078948395916681613 3372732029605648468755605)
              ·
                refine ⟨158096813887764771972919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3372732029605648468755605 158096813887764771972919)
                ·
                  rfl

theorem cell20_1039137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_1039137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039137 prefixEnd_1039137 := by exact prefixLift 1039137
  have htrace : WordTrace (prefixWord ++ tailWord_1039137) baseStart_1039137 baseEnd_1039137 := by
    simpa [prefixWord, tailWord_1039137, baseEnd_1039137] using wordTrace_append hprefix tailTrace_1039137
  have hstable : (prefixWord ++ tailWord_1039137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039137).length < 2 ^ (prefixWord ++ tailWord_1039137).sum := by decide
  have hdescent : baseEnd_1039137 < baseStart_1039137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039174 : List Nat := [6, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1039174 : Nat := 118140960795 + 1039174 * 2 ^ 59
def prefixEnd_1039174 : Nat := 4983230072969 + 3 ^ 40 * 1039174 * 2
def baseEnd_1039174 : Nat := 474307329471486631685273

theorem tailTrace_1039174 : CollatzResearch.WordTrace tailWord_1039174 prefixEnd_1039174 474307329471486631685273 := by
  unfold tailWord_1039174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184430923039298426083143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25267859691505033089773717 1184430923039298426083143)
  ·
    refine ⟨1776646384558947639124715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1184430923039298426083143 1776646384558947639124715)
    ·
      refine ⟨2664969576838421458687073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1776646384558947639124715 2664969576838421458687073)
      ·
        refine ⟨1998727182628816094015305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2664969576838421458687073 1998727182628816094015305)
        ·
          refine ⟨1499045386971612070511479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1998727182628816094015305 1499045386971612070511479)
          ·
            refine ⟨2248568080457418105767219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499045386971612070511479 2248568080457418105767219)
            ·
              refine ⟨3372852120686127158650829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2248568080457418105767219 3372852120686127158650829)
              ·
                refine ⟨1264819545257297684494061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3372852120686127158650829 1264819545257297684494061)
                ·
                  refine ⟨474307329471486631685273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264819545257297684494061 474307329471486631685273)
                  ·
                    rfl

theorem cell20_1039174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1039174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039174 prefixEnd_1039174 := by exact prefixLift 1039174
  have htrace : WordTrace (prefixWord ++ tailWord_1039174) baseStart_1039174 baseEnd_1039174 := by
    simpa [prefixWord, tailWord_1039174, baseEnd_1039174] using wordTrace_append hprefix tailTrace_1039174
  have hstable : (prefixWord ++ tailWord_1039174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039174).length < 2 ^ (prefixWord ++ tailWord_1039174).sum := by decide
  have hdescent : baseEnd_1039174 < baseStart_1039174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039237 : List Nat := [1, 3, 1, 1, 3, 3, 2, 3, 3]
def baseStart_1039237 : Nat := 118140960795 + 1039237 * 2 ^ 59
def prefixEnd_1039237 : Nat := 4983230072969 + 3 ^ 40 * 1039237 * 2
def baseEnd_1039237 : Nat := 474336084388138412585015

theorem tailTrace_1039237 : CollatzResearch.WordTrace tailWord_1039237 prefixEnd_1039237 474336084388138412585015 := by
  unfold tailWord_1039237
  simp only [CollatzResearch.WordTrace]
  refine ⟨37904087336029311394203965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25269391557352874262802643 37904087336029311394203965)
  ·
    refine ⟨14214032751010991772826487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37904087336029311394203965 14214032751010991772826487)
    ·
      refine ⟨21321049126516487659239731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14214032751010991772826487 21321049126516487659239731)
      ·
        refine ⟨31981573689774731488859597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21321049126516487659239731 31981573689774731488859597)
        ·
          refine ⟨11993090133665524308322349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31981573689774731488859597 11993090133665524308322349)
          ·
            refine ⟨4497408800124571615620881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11993090133665524308322349 4497408800124571615620881)
            ·
              refine ⟨3373056600093428711715661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4497408800124571615620881 3373056600093428711715661)
              ·
                refine ⟨1264896225035035766893373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3373056600093428711715661 1264896225035035766893373)
                ·
                  refine ⟨474336084388138412585015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264896225035035766893373 474336084388138412585015)
                  ·
                    rfl

theorem cell20_1039237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_1039237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039237 prefixEnd_1039237 := by exact prefixLift 1039237
  have htrace : WordTrace (prefixWord ++ tailWord_1039237) baseStart_1039237 baseEnd_1039237 := by
    simpa [prefixWord, tailWord_1039237, baseEnd_1039237] using wordTrace_append hprefix tailTrace_1039237
  have hstable : (prefixWord ++ tailWord_1039237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039237).length < 2 ^ (prefixWord ++ tailWord_1039237).sum := by decide
  have hdescent : baseEnd_1039237 < baseStart_1039237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039271 : List Nat := [1, 1, 6, 1, 3, 2, 1, 2, 3]
def baseStart_1039271 : Nat := 118140960795 + 1039271 * 2 ^ 59
def prefixEnd_1039271 : Nat := 4983230072969 + 3 ^ 40 * 1039271 * 2
def baseEnd_1039271 : Nat := 474351602914585405451543

theorem tailTrace_1039271 : CollatzResearch.WordTrace tailWord_1039271 prefixEnd_1039271 474351602914585405451543 := by
  unfold tailWord_1039271
  simp only [CollatzResearch.WordTrace]
  refine ⟨37905327417906135200941667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25270218278604090133961111 37905327417906135200941667)
  ·
    refine ⟨56857991126859202801412501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37905327417906135200941667 56857991126859202801412501)
    ·
      refine ⟨2665218334071525131316211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56857991126859202801412501 2665218334071525131316211)
      ·
        refine ⟨3997827501107287696974317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2665218334071525131316211 3997827501107287696974317)
        ·
          refine ⟨1499185312915232886365369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3997827501107287696974317 1499185312915232886365369)
          ·
            refine ⟨1124388984686424664774027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499185312915232886365369 1124388984686424664774027)
            ·
              refine ⟨1686583477029636997161041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124388984686424664774027 1686583477029636997161041)
              ·
                refine ⟨1264937607772227747870781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1686583477029636997161041 1264937607772227747870781)
                ·
                  refine ⟨474351602914585405451543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1264937607772227747870781 474351602914585405451543)
                  ·
                    rfl

theorem cell20_1039271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_1039271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039271 prefixEnd_1039271 := by exact prefixLift 1039271
  have htrace : WordTrace (prefixWord ++ tailWord_1039271) baseStart_1039271 baseEnd_1039271 := by
    simpa [prefixWord, tailWord_1039271, baseEnd_1039271] using wordTrace_append hprefix tailTrace_1039271
  have hstable : (prefixWord ++ tailWord_1039271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039271).length < 2 ^ (prefixWord ++ tailWord_1039271).sum := by decide
  have hdescent : baseEnd_1039271 < baseStart_1039271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039316 : List Nat := [2, 4, 1, 2, 1, 2, 3, 3, 2]
def baseStart_1039316 : Nat := 118140960795 + 1039316 * 2 ^ 59
def prefixEnd_1039316 : Nat := 4983230072969 + 3 ^ 40 * 1039316 * 2
def baseEnd_1039316 : Nat := 474372142140765248951359

theorem tailTrace_1039316 : CollatzResearch.WordTrace tailWord_1039316 prefixEnd_1039316 474372142140765248951359 := by
  unfold tailWord_1039316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18953484351371553943164901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25271312468495405257553201 18953484351371553943164901)
  ·
    refine ⟨3553778315882166364343419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18953484351371553943164901 3553778315882166364343419)
    ·
      refine ⟨5330667473823249546515129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3553778315882166364343419 5330667473823249546515129)
      ·
        refine ⟨3998000605367437159886347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5330667473823249546515129 3998000605367437159886347)
        ·
          refine ⟨5997000908051155739829521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3998000605367437159886347 5997000908051155739829521)
          ·
            refine ⟨4497750681038366804872141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5997000908051155739829521 4497750681038366804872141)
            ·
              refine ⟨1686656505389387551827053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4497750681038366804872141 1686656505389387551827053)
              ·
                refine ⟨632496189521020331935145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1686656505389387551827053 632496189521020331935145)
                ·
                  refine ⟨474372142140765248951359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632496189521020331935145 474372142140765248951359)
                  ·
                    rfl

theorem cell20_1039316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_1039316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039316 prefixEnd_1039316 := by exact prefixLift 1039316
  have htrace : WordTrace (prefixWord ++ tailWord_1039316) baseStart_1039316 baseEnd_1039316 := by
    simpa [prefixWord, tailWord_1039316, baseEnd_1039316] using wordTrace_append hprefix tailTrace_1039316
  have hstable : (prefixWord ++ tailWord_1039316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039316).length < 2 ^ (prefixWord ++ tailWord_1039316).sum := by decide
  have hdescent : baseEnd_1039316 < baseStart_1039316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039330 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1039330 : Nat := 118140960795 + 1039330 * 2 ^ 59
def prefixEnd_1039330 : Nat := 4983230072969 + 3 ^ 40 * 1039330 * 2
def baseEnd_1039330 : Nat := 474378532122243422484635

theorem tailTrace_1039330 : CollatzResearch.WordTrace tailWord_1039330 prefixEnd_1039330 474378532122243422484635 := by
  unfold tailWord_1039330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476869831173097069334861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25271652883128258851559629 9476869831173097069334861)
  ·
    refine ⟨3553826186689911401000573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9476869831173097069334861 3553826186689911401000573)
    ·
      refine ⟨1332684820008716775375215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3553826186689911401000573 1332684820008716775375215)
      ·
        refine ⟨1999027230013075163062823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332684820008716775375215 1999027230013075163062823)
        ·
          refine ⟨2998540845019612744594235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999027230013075163062823 2998540845019612744594235)
          ·
            refine ⟨4497811267529419116891353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2998540845019612744594235 4497811267529419116891353)
            ·
              refine ⟨3373358450647064337668515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4497811267529419116891353 3373358450647064337668515)
              ·
                refine ⟨5060037675970596506502773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373358450647064337668515 5060037675970596506502773)
                ·
                  refine ⟨474378532122243422484635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5060037675970596506502773 474378532122243422484635)
                  ·
                    rfl

theorem cell20_1039330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1039330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039330 prefixEnd_1039330 := by exact prefixLift 1039330
  have htrace : WordTrace (prefixWord ++ tailWord_1039330) baseStart_1039330 baseEnd_1039330 := by
    simpa [prefixWord, tailWord_1039330, baseEnd_1039330] using wordTrace_append hprefix tailTrace_1039330
  have hstable : (prefixWord ++ tailWord_1039330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039330).length < 2 ^ (prefixWord ++ tailWord_1039330).sum := by decide
  have hdescent : baseEnd_1039330 < baseStart_1039330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039333 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 4]
def baseStart_1039333 : Nat := 118140960795 + 1039333 * 2 ^ 59
def prefixEnd_1039333 : Nat := 4983230072969 + 3 ^ 40 * 1039333 * 2
def baseEnd_1039333 : Nat := 474379901403988745384623

theorem tailTrace_1039333 : CollatzResearch.WordTrace tailWord_1039333 prefixEnd_1039333 474379901403988745384623 := by
  unfold tailWord_1039333
  simp only [CollatzResearch.WordTrace]
  refine ⟨37907588743681519789698653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25271725829121013193132435 37907588743681519789698653)
  ·
    refine ⟨14215345778880569921136995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37907588743681519789698653 14215345778880569921136995)
    ·
      refine ⟨21323018668320854881705493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14215345778880569921136995 21323018668320854881705493)
      ·
        refine ⟨999516500077540072579945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21323018668320854881705493 999516500077540072579945)
        ·
          refine ⟨749637375058155054434959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999516500077540072579945 749637375058155054434959)
          ·
            refine ⟨1124456062587232581652439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749637375058155054434959 1124456062587232581652439)
            ·
              refine ⟨1686684093880848872478659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124456062587232581652439 1686684093880848872478659)
              ·
                refine ⟨2530026140821273308717989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1686684093880848872478659 2530026140821273308717989)
                ·
                  refine ⟨474379901403988745384623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530026140821273308717989 474379901403988745384623)
                  ·
                    rfl

theorem cell20_1039333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 4].length) (baseStart_1039333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039333 prefixEnd_1039333 := by exact prefixLift 1039333
  have htrace : WordTrace (prefixWord ++ tailWord_1039333) baseStart_1039333 baseEnd_1039333 := by
    simpa [prefixWord, tailWord_1039333, baseEnd_1039333] using wordTrace_append hprefix tailTrace_1039333
  have hstable : (prefixWord ++ tailWord_1039333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039333).length < 2 ^ (prefixWord ++ tailWord_1039333).sum := by decide
  have hdescent : baseEnd_1039333 < baseStart_1039333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039378 : List Nat := [3, 2, 5, 1, 2, 7]
def baseStart_1039378 : Nat := 118140960795 + 1039378 * 2 ^ 59
def prefixEnd_1039378 : Nat := 4983230072969 + 3 ^ 40 * 1039378 * 2
def baseEnd_1039378 : Nat := 17570386690006244032757

theorem tailTrace_1039378 : CollatzResearch.WordTrace tailWord_1039378 prefixEnd_1039378 17570386690006244032757 := by
  unfold tailWord_1039378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9477307507129623118771697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25272820019012328316724525 9477307507129623118771697)
  ·
    refine ⟨7107980630347217339078773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9477307507129623118771697 7107980630347217339078773)
    ·
      refine ⟨666373184095051625538635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7107980630347217339078773 666373184095051625538635)
      ·
        refine ⟨999559776142577438307953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666373184095051625538635 999559776142577438307953)
        ·
          refine ⟨749669832106933078730965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999559776142577438307953 749669832106933078730965)
          ·
            refine ⟨17570386690006244032757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 749669832106933078730965 17570386690006244032757)
            ·
              rfl

theorem cell20_1039378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 7].length) (baseStart_1039378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039378 prefixEnd_1039378 := by exact prefixLift 1039378
  have htrace : WordTrace (prefixWord ++ tailWord_1039378) baseStart_1039378 baseEnd_1039378 := by
    simpa [prefixWord, tailWord_1039378, baseEnd_1039378] using wordTrace_append hprefix tailTrace_1039378
  have hstable : (prefixWord ++ tailWord_1039378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039378).length < 2 ^ (prefixWord ++ tailWord_1039378).sum := by decide
  have hdescent : baseEnd_1039378 < baseStart_1039378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039388 : List Nat := [2, 2, 3, 1, 5, 1, 2, 2, 2]
def baseStart_1039388 : Nat := 118140960795 + 1039388 * 2 ^ 59
def prefixEnd_1039388 : Nat := 4983230072969 + 3 ^ 40 * 1039388 * 2
def baseEnd_1039388 : Nat := 474405004902652998551065

theorem tailTrace_1039388 : CollatzResearch.WordTrace tailWord_1039388 prefixEnd_1039388 474405004902652998551065 := by
  unfold tailWord_1039388
  simp only [CollatzResearch.WordTrace]
  refine ⟨18954797379241132091475409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25273063172321509455300545 18954797379241132091475409)
  ·
    refine ⟨14216098034430849068606557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18954797379241132091475409 14216098034430849068606557)
    ·
      refine ⟨5331036762911568400727459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14216098034430849068606557 5331036762911568400727459)
      ·
        refine ⟨7996555144367352601091189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331036762911568400727459 7996555144367352601091189)
        ·
          refine ⟨749677044784439306352299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7996555144367352601091189 749677044784439306352299)
          ·
            refine ⟨1124515567176658959528449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749677044784439306352299 1124515567176658959528449)
            ·
              refine ⟨843386675382494219646337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124515567176658959528449 843386675382494219646337)
              ·
                refine ⟨632540006536870664734753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 843386675382494219646337 632540006536870664734753)
                ·
                  refine ⟨474405004902652998551065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632540006536870664734753 474405004902652998551065)
                  ·
                    rfl

theorem cell20_1039388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_1039388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039388 prefixEnd_1039388 := by exact prefixLift 1039388
  have htrace : WordTrace (prefixWord ++ tailWord_1039388) baseStart_1039388 baseEnd_1039388 := by
    simpa [prefixWord, tailWord_1039388, baseEnd_1039388] using wordTrace_append hprefix tailTrace_1039388
  have hstable : (prefixWord ++ tailWord_1039388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039388).length < 2 ^ (prefixWord ++ tailWord_1039388).sum := by decide
  have hdescent : baseEnd_1039388 < baseStart_1039388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039399 : List Nat := [1, 1, 7, 1, 1, 3, 1, 5]
def baseStart_1039399 : Nat := 118140960795 + 1039399 * 2 ^ 59
def prefixEnd_1039399 : Nat := 4983230072969 + 3 ^ 40 * 1039399 * 2
def baseEnd_1039399 : Nat := 158136675200795283061451

theorem tailTrace_1039399 : CollatzResearch.WordTrace tailWord_1039399 prefixEnd_1039399 158136675200795283061451 := by
  unfold tailWord_1039399
  simp only [CollatzResearch.WordTrace]
  refine ⟨37909995961442413061601251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25273330640961608707734167 37909995961442413061601251)
  ·
    refine ⟨56864993942163619592401877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37909995961442413061601251 56864993942163619592401877)
    ·
      refine ⟨1332773295519459834196919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 56864993942163619592401877 1332773295519459834196919)
      ·
        refine ⟨1999159943279189751295379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332773295519459834196919 1999159943279189751295379)
        ·
          refine ⟨2998739914918784626943069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999159943279189751295379 2998739914918784626943069)
          ·
            refine ⟨1124527468094544235103651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2998739914918784626943069 1124527468094544235103651)
            ·
              refine ⟨1686791202141816352655477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1124527468094544235103651 1686791202141816352655477)
              ·
                refine ⟨158136675200795283061451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1686791202141816352655477 158136675200795283061451)
                ·
                  rfl

theorem cell20_1039399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_1039399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039399 prefixEnd_1039399 := by exact prefixLift 1039399
  have htrace : WordTrace (prefixWord ++ tailWord_1039399) baseStart_1039399 baseEnd_1039399 := by
    simpa [prefixWord, tailWord_1039399, baseEnd_1039399] using wordTrace_append hprefix tailTrace_1039399
  have hstable : (prefixWord ++ tailWord_1039399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039399).length < 2 ^ (prefixWord ++ tailWord_1039399).sum := by decide
  have hdescent : baseEnd_1039399 < baseStart_1039399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039420 : List Nat := [2, 2, 2, 2, 2, 3, 3, 4]
def baseStart_1039420 : Nat := 118140960795 + 1039420 * 2 ^ 59
def prefixEnd_1039420 : Nat := 4983230072969 + 3 ^ 40 * 1039420 * 2
def baseEnd_1039420 : Nat := 158139870191534369828089

theorem tailTrace_1039420 : CollatzResearch.WordTrace tailWord_1039420 prefixEnd_1039420 158139870191534369828089 := by
  unfold tailWord_1039420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955380947183166824057857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25273841262910889098743809 18955380947183166824057857)
  ·
    refine ⟨14216535710387375118043393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18955380947183166824057857 14216535710387375118043393)
    ·
      refine ⟨10662401782790531338532545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14216535710387375118043393 10662401782790531338532545)
      ·
        refine ⟨7996801337092898503899409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10662401782790531338532545 7996801337092898503899409)
        ·
          refine ⟨5997601002819673877924557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7996801337092898503899409 5997601002819673877924557)
          ·
            refine ⟨2249100376057377704221709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5997601002819673877924557 2249100376057377704221709)
            ·
              refine ⟨843412641021516639083141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2249100376057377704221709 843412641021516639083141)
              ·
                refine ⟨158139870191534369828089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843412641021516639083141 158139870191534369828089)
                ·
                  rfl

theorem cell20_1039420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_1039420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039420 prefixEnd_1039420 := by exact prefixLift 1039420
  have htrace : WordTrace (prefixWord ++ tailWord_1039420) baseStart_1039420 baseEnd_1039420 := by
    simpa [prefixWord, tailWord_1039420, baseEnd_1039420] using wordTrace_append hprefix tailTrace_1039420
  have hstable : (prefixWord ++ tailWord_1039420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039420).length < 2 ^ (prefixWord ++ tailWord_1039420).sum := by decide
  have hdescent : baseEnd_1039420 < baseStart_1039420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039448 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1039448 : Nat := 118140960795 + 1039448 * 2 ^ 59
def prefixEnd_1039448 : Nat := 4983230072969 + 3 ^ 40 * 1039448 * 2
def baseEnd_1039448 : Nat := 474432390537559456550819

theorem tailTrace_1039448 : CollatzResearch.WordTrace tailWord_1039448 prefixEnd_1039448 474432390537559456550819 := by
  unfold tailWord_1039448
  simp only [CollatzResearch.WordTrace]
  refine ⟨18955891569132447215067499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25274522092176596286756665 18955891569132447215067499)
  ·
    refine ⟨28433837353698670822601249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18955891569132447215067499 28433837353698670822601249)
    ·
      refine ⟨21325378015274003116950937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28433837353698670822601249 21325378015274003116950937)
      ·
        refine ⟨15994033511455502337713203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21325378015274003116950937 15994033511455502337713203)
        ·
          refine ⟨23991050267183253506569805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15994033511455502337713203 23991050267183253506569805)
          ·
            refine ⟨8996643850193720064963677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23991050267183253506569805 8996643850193720064963677)
            ·
              refine ⟨3373741443822645024361379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8996643850193720064963677 3373741443822645024361379)
              ·
                refine ⟨5060612165733967536542069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3373741443822645024361379 5060612165733967536542069)
                ·
                  refine ⟨474432390537559456550819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5060612165733967536542069 474432390537559456550819)
                  ·
                    rfl

theorem cell20_1039448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1039448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039448 prefixEnd_1039448 := by exact prefixLift 1039448
  have htrace : WordTrace (prefixWord ++ tailWord_1039448) baseStart_1039448 baseEnd_1039448 := by
    simpa [prefixWord, tailWord_1039448, baseEnd_1039448] using wordTrace_append hprefix tailTrace_1039448
  have hstable : (prefixWord ++ tailWord_1039448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039448).length < 2 ^ (prefixWord ++ tailWord_1039448).sum := by decide
  have hdescent : baseEnd_1039448 < baseStart_1039448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039496 : List Nat := [2, 1, 3, 4, 2, 2, 6]
def baseStart_1039496 : Nat := 118140960795 + 1039496 * 2 ^ 59
def prefixEnd_1039496 : Nat := 4983230072969 + 3 ^ 40 * 1039496 * 2
def baseEnd_1039496 : Nat := 52717144338387180327847

theorem tailTrace_1039496 : CollatzResearch.WordTrace tailWord_1039496 prefixEnd_1039496 52717144338387180327847 := by
  unfold tailWord_1039496
  simp only [CollatzResearch.WordTrace]
  refine ⟨18956766921045499313941171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25275689228060665751921561 18956766921045499313941171)
  ·
    refine ⟨28435150381568248970911757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18956766921045499313941171 28435150381568248970911757)
    ·
      refine ⟨10663181393088093364091909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28435150381568248970911757 10663181393088093364091909)
      ·
        refine ⟨1999346511204017505767233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10663181393088093364091909 1999346511204017505767233)
        ·
          refine ⟨1499509883403013129325425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999346511204017505767233 1499509883403013129325425)
          ·
            refine ⟨1124632412552259846994069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1499509883403013129325425 1124632412552259846994069)
            ·
              refine ⟨52717144338387180327847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1124632412552259846994069 52717144338387180327847)
              ·
                rfl

theorem cell20_1039496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 6].length) (baseStart_1039496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039496 prefixEnd_1039496 := by exact prefixLift 1039496
  have htrace : WordTrace (prefixWord ++ tailWord_1039496) baseStart_1039496 baseEnd_1039496 := by
    simpa [prefixWord, tailWord_1039496, baseEnd_1039496] using wordTrace_append hprefix tailTrace_1039496
  have hstable : (prefixWord ++ tailWord_1039496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039496).length < 2 ^ (prefixWord ++ tailWord_1039496).sum := by decide
  have hdescent : baseEnd_1039496 < baseStart_1039496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039517 : List Nat := [1, 4, 2, 1, 1, 2, 4, 5]
def baseStart_1039517 : Nat := 118140960795 + 1039517 * 2 ^ 59
def prefixEnd_1039517 : Nat := 4983230072969 + 3 ^ 40 * 1039517 * 2
def baseEnd_1039517 : Nat := 158154628005900627750179

theorem tailTrace_1039517 : CollatzResearch.WordTrace tailWord_1039517 prefixEnd_1039517 158154628005900627750179 := by
  unfold tailWord_1039517
  simp only [CollatzResearch.WordTrace]
  refine ⟨37914299775014919214396805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25276199850009946142931203 37914299775014919214396805)
  ·
    refine ⟨7108931207815297352699401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37914299775014919214396805 7108931207815297352699401)
    ·
      refine ⟨5331698405861473014524551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7108931207815297352699401 5331698405861473014524551)
      ·
        refine ⟨7997547608792209521786827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5331698405861473014524551 7997547608792209521786827)
        ·
          refine ⟨11996321413188314282680241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7997547608792209521786827 11996321413188314282680241)
          ·
            refine ⟨8997241059891235712010181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11996321413188314282680241 8997241059891235712010181)
            ·
              refine ⟨1686982698729606696001909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8997241059891235712010181 1686982698729606696001909)
              ·
                refine ⟨158154628005900627750179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1686982698729606696001909 158154628005900627750179)
                ·
                  rfl

theorem cell20_1039517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_1039517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039517 prefixEnd_1039517 := by exact prefixLift 1039517
  have htrace : WordTrace (prefixWord ++ tailWord_1039517) baseStart_1039517 baseEnd_1039517 := by
    simpa [prefixWord, tailWord_1039517, baseEnd_1039517] using wordTrace_append hprefix tailTrace_1039517
  have hstable : (prefixWord ++ tailWord_1039517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039517).length < 2 ^ (prefixWord ++ tailWord_1039517).sum := by decide
  have hdescent : baseEnd_1039517 < baseStart_1039517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039554 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1039554 : Nat := 118140960795 + 1039554 * 2 ^ 59
def prefixEnd_1039554 : Nat := 4983230072969 + 3 ^ 40 * 1039554 * 2
def baseEnd_1039554 : Nat := 474480771825894199017053

theorem tailTrace_1039554 : CollatzResearch.WordTrace tailWord_1039554 prefixEnd_1039554 474480771825894199017053 := by
  unfold tailWord_1039554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9478912318970218633373429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25277099517253916355662477 9478912318970218633373429)
  ·
    refine ⟨888648029903457996878759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9478912318970218633373429 888648029903457996878759)
    ·
      refine ⟨1332972044855186995318139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888648029903457996878759 1332972044855186995318139)
      ·
        refine ⟨1999458067282780492977209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332972044855186995318139 1999458067282780492977209)
        ·
          refine ⟨1499593550462085369732907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999458067282780492977209 1499593550462085369732907)
          ·
            refine ⟨2249390325693128054599361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499593550462085369732907 2249390325693128054599361)
            ·
              refine ⟨1687042744269846040949521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2249390325693128054599361 1687042744269846040949521)
              ·
                refine ⟨1265282058202384530712141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687042744269846040949521 1265282058202384530712141)
                ·
                  refine ⟨474480771825894199017053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265282058202384530712141 474480771825894199017053)
                  ·
                    rfl

theorem cell20_1039554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1039554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039554 prefixEnd_1039554 := by exact prefixLift 1039554
  have htrace : WordTrace (prefixWord ++ tailWord_1039554) baseStart_1039554 baseEnd_1039554 := by
    simpa [prefixWord, tailWord_1039554, baseEnd_1039554] using wordTrace_append hprefix tailTrace_1039554
  have hstable : (prefixWord ++ tailWord_1039554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039554).length < 2 ^ (prefixWord ++ tailWord_1039554).sum := by decide
  have hdescent : baseEnd_1039554 < baseStart_1039554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039569 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_1039569 : Nat := 118140960795 + 1039569 * 2 ^ 59
def prefixEnd_1039569 : Nat := 4983230072969 + 3 ^ 40 * 1039569 * 2
def baseEnd_1039569 : Nat := 474487618234620813516991

theorem tailTrace_1039569 : CollatzResearch.WordTrace tailWord_1039569 prefixEnd_1039569 474487618234620813516991 := by
  unfold tailWord_1039569
  simp only [CollatzResearch.WordTrace]
  refine ⟨37916196370826532095289761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25277464247217688063526507 37916196370826532095289761)
  ·
    refine ⟨28437147278119899071467321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37916196370826532095289761 28437147278119899071467321)
    ·
      refine ⟨21327860458589924303600491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28437147278119899071467321 21327860458589924303600491)
      ·
        refine ⟨31991790687884886455400737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21327860458589924303600491 31991790687884886455400737)
        ·
          refine ⟨23993843015913664841550553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31991790687884886455400737 23993843015913664841550553)
          ·
            refine ⟨17995382261935248631162915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23993843015913664841550553 17995382261935248631162915)
            ·
              refine ⟨26993073392902872946744373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17995382261935248631162915 26993073392902872946744373)
              ·
                refine ⟨2530600630584644338757285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26993073392902872946744373 2530600630584644338757285)
                ·
                  refine ⟨474487618234620813516991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2530600630584644338757285 474487618234620813516991)
                  ·
                    rfl

theorem cell20_1039569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_1039569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039569 prefixEnd_1039569 := by exact prefixLift 1039569
  have htrace : WordTrace (prefixWord ++ tailWord_1039569) baseStart_1039569 baseEnd_1039569 := by
    simpa [prefixWord, tailWord_1039569, baseEnd_1039569] using wordTrace_append hprefix tailTrace_1039569
  have hstable : (prefixWord ++ tailWord_1039569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039569).length < 2 ^ (prefixWord ++ tailWord_1039569).sum := by decide
  have hdescent : baseEnd_1039569 < baseStart_1039569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039603 : List Nat := [1, 1, 1, 2, 2, 6, 2, 3, 2]
def baseStart_1039603 : Nat := 118140960795 + 1039603 * 2 ^ 59
def prefixEnd_1039603 : Nat := 4983230072969 + 3 ^ 40 * 1039603 * 2
def baseEnd_1039603 : Nat := 474503136761067806383519

theorem tailTrace_1039603 : CollatzResearch.WordTrace tailWord_1039603 prefixEnd_1039603 474503136761067806383519 := by
  unfold tailWord_1039603
  simp only [CollatzResearch.WordTrace]
  refine ⟨37917436452703355902027463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25278290968468903934684975 37917436452703355902027463)
  ·
    refine ⟨56876154679055033853041195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37917436452703355902027463 56876154679055033853041195)
    ·
      refine ⟨85314232018582550779561793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56876154679055033853041195 85314232018582550779561793)
      ·
        refine ⟨63985674013936913084671345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85314232018582550779561793 63985674013936913084671345)
        ·
          refine ⟨47989255510452684813503509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63985674013936913084671345 47989255510452684813503509)
          ·
            refine ⟨2249496352052469600632977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47989255510452684813503509 2249496352052469600632977)
            ·
              refine ⟨1687122264039352200474733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2249496352052469600632977 1687122264039352200474733)
              ·
                refine ⟨632670849014757075178025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1687122264039352200474733 632670849014757075178025)
                ·
                  refine ⟨474503136761067806383519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632670849014757075178025 474503136761067806383519)
                  ·
                    rfl

theorem cell20_1039603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 2].length) (baseStart_1039603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039603 prefixEnd_1039603 := by exact prefixLift 1039603
  have htrace : WordTrace (prefixWord ++ tailWord_1039603) baseStart_1039603 baseEnd_1039603 := by
    simpa [prefixWord, tailWord_1039603, baseEnd_1039603] using wordTrace_append hprefix tailTrace_1039603
  have hstable : (prefixWord ++ tailWord_1039603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039603).length < 2 ^ (prefixWord ++ tailWord_1039603).sum := by decide
  have hdescent : baseEnd_1039603 < baseStart_1039603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039617 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 3]
def baseStart_1039617 : Nat := 118140960795 + 1039617 * 2 ^ 59
def prefixEnd_1039617 : Nat := 4983230072969 + 3 ^ 40 * 1039617 * 2
def baseEnd_1039617 : Nat := 474509526742545979916795

theorem tailTrace_1039617 : CollatzResearch.WordTrace tailWord_1039617 prefixEnd_1039617 474509526742545979916795 := by
  unfold tailWord_1039617
  simp only [CollatzResearch.WordTrace]
  refine ⟨37917947074652636293037105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25278631383101757528691403 37917947074652636293037105)
  ·
    refine ⟨28438460305989477219777829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37917947074652636293037105 28438460305989477219777829)
    ·
      refine ⟨5332211307373026978708343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28438460305989477219777829 5332211307373026978708343)
      ·
        refine ⟨7998316961059540468062515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332211307373026978708343 7998316961059540468062515)
        ·
          refine ⟨11997475441589310702093773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998316961059540468062515 11997475441589310702093773)
          ·
            refine ⟨4499053290595991513285165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11997475441589310702093773 4499053290595991513285165)
            ·
              refine ⟨1687144983973496817481937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4499053290595991513285165 1687144983973496817481937)
              ·
                refine ⟨1265358737980122613111453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687144983973496817481937 1265358737980122613111453)
                ·
                  refine ⟨474509526742545979916795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265358737980122613111453 474509526742545979916795)
                  ·
                    rfl

theorem cell20_1039617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 3].length) (baseStart_1039617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039617 prefixEnd_1039617 := by exact prefixLift 1039617
  have htrace : WordTrace (prefixWord ++ tailWord_1039617) baseStart_1039617 baseEnd_1039617 := by
    simpa [prefixWord, tailWord_1039617, baseEnd_1039617] using wordTrace_append hprefix tailTrace_1039617
  have hstable : (prefixWord ++ tailWord_1039617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039617).length < 2 ^ (prefixWord ++ tailWord_1039617).sum := by decide
  have hdescent : baseEnd_1039617 < baseStart_1039617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039658 : List Nat := [3, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_1039658 : Nat := 118140960795 + 1039658 * 2 ^ 59
def prefixEnd_1039658 : Nat := 4983230072969 + 3 ^ 40 * 1039658 * 2
def baseEnd_1039658 : Nat := 474528240259732059549961

theorem tailTrace_1039658 : CollatzResearch.WordTrace tailWord_1039658 prefixEnd_1039658 474528240259732059549961 := by
  unfold tailWord_1039658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9479860616876025073819907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25279628311669400196853085 9479860616876025073819907)
  ·
    refine ⟨14219790925314037610729861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9479860616876025073819907 14219790925314037610729861)
    ·
      refine ⟨2666210798496382052011849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14219790925314037610729861 2666210798496382052011849)
      ·
        refine ⟨1999658098872286539008887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2666210798496382052011849 1999658098872286539008887)
        ·
          refine ⟨2999487148308429808513331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999658098872286539008887 2999487148308429808513331)
          ·
            refine ⟨4499230722462644712769997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2999487148308429808513331 4499230722462644712769997)
            ·
              refine ⟨1687211520923491767288749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4499230722462644712769997 1687211520923491767288749)
              ·
                refine ⟨632704320346309412733281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1687211520923491767288749 632704320346309412733281)
                ·
                  refine ⟨474528240259732059549961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632704320346309412733281 474528240259732059549961)
                  ·
                    rfl

theorem cell20_1039658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_1039658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039658 prefixEnd_1039658 := by exact prefixLift 1039658
  have htrace : WordTrace (prefixWord ++ tailWord_1039658) baseStart_1039658 baseEnd_1039658 := by
    simpa [prefixWord, tailWord_1039658, baseEnd_1039658] using wordTrace_append hprefix tailTrace_1039658
  have hstable : (prefixWord ++ tailWord_1039658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039658).length < 2 ^ (prefixWord ++ tailWord_1039658).sum := by decide
  have hdescent : baseEnd_1039658 < baseStart_1039658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039669 : List Nat := [1, 3, 3, 1, 2, 4, 6]
def baseStart_1039669 : Nat := 118140960795 + 1039669 * 2 ^ 59
def prefixEnd_1039669 : Nat := 4983230072969 + 3 ^ 40 * 1039669 * 2
def baseEnd_1039669 : Nat := 52725917884384990020361

theorem tailTrace_1039669 : CollatzResearch.WordTrace tailWord_1039669 prefixEnd_1039669 52725917884384990020361 := by
  unfold tailWord_1039669
  simp only [CollatzResearch.WordTrace]
  refine ⟨37919843670464249173930061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25279895780309499449286707 37919843670464249173930061)
  ·
    refine ⟨14219941376424093440223773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37919843670464249173930061 14219941376424093440223773)
    ·
      refine ⟨5332478016159035040083915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14219941376424093440223773 5332478016159035040083915)
      ·
        refine ⟨7998717024238552560125873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5332478016159035040083915 7998717024238552560125873)
        ·
          refine ⟨5999037768178914420094405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7998717024238552560125873 5999037768178914420094405)
          ·
            refine ⟨1124819581533546453767701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5999037768178914420094405 1124819581533546453767701)
            ·
              refine ⟨52725917884384990020361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1124819581533546453767701 52725917884384990020361)
              ·
                rfl

theorem cell20_1039669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 6].length) (baseStart_1039669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039669 prefixEnd_1039669 := by exact prefixLift 1039669
  have htrace : WordTrace (prefixWord ++ tailWord_1039669) baseStart_1039669 baseEnd_1039669 := by
    simpa [prefixWord, tailWord_1039669, baseEnd_1039669] using wordTrace_append hprefix tailTrace_1039669
  have hstable : (prefixWord ++ tailWord_1039669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039669).length < 2 ^ (prefixWord ++ tailWord_1039669).sum := by decide
  have hdescent : baseEnd_1039669 < baseStart_1039669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039676 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1039676 : Nat := 118140960795 + 1039676 * 2 ^ 59
def prefixEnd_1039676 : Nat := 4983230072969 + 3 ^ 40 * 1039676 * 2
def baseEnd_1039676 : Nat := 474536455950203996949887

theorem tailTrace_1039676 : CollatzResearch.WordTrace tailWord_1039676 prefixEnd_1039676 474536455950203996949887 := by
  unfold tailWord_1039676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18960049490719444684717441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25280065987625926246289921 18960049490719444684717441)
  ·
    refine ⟨14220037118039583513538081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18960049490719444684717441 14220037118039583513538081)
    ·
      refine ⟨10665027838529687635153561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14220037118039583513538081 10665027838529687635153561)
      ·
        refine ⟨7998770878897265726365171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10665027838529687635153561 7998770878897265726365171)
        ·
          refine ⟨11998156318345898589547757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7998770878897265726365171 11998156318345898589547757)
          ·
            refine ⟨4499308619379711971080409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11998156318345898589547757 4499308619379711971080409)
            ·
              refine ⟨3374481464534783978310307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4499308619379711971080409 3374481464534783978310307)
              ·
                refine ⟨5061722196802175967465461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3374481464534783978310307 5061722196802175967465461)
                ·
                  refine ⟨474536455950203996949887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5061722196802175967465461 474536455950203996949887)
                  ·
                    rfl

theorem cell20_1039676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1039676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039676 prefixEnd_1039676 := by exact prefixLift 1039676
  have htrace : WordTrace (prefixWord ++ tailWord_1039676) baseStart_1039676 baseEnd_1039676 := by
    simpa [prefixWord, tailWord_1039676, baseEnd_1039676] using wordTrace_append hprefix tailTrace_1039676
  have hstable : (prefixWord ++ tailWord_1039676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039676).length < 2 ^ (prefixWord ++ tailWord_1039676).sum := by decide
  have hdescent : baseEnd_1039676 < baseStart_1039676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039738 : List Nat := [3, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_1039738 : Nat := 118140960795 + 1039738 * 2 ^ 59
def prefixEnd_1039738 : Nat := 4983230072969 + 3 ^ 40 * 1039738 * 2
def baseEnd_1039738 : Nat := 474564754439607336882967

theorem tailTrace_1039738 : CollatzResearch.WordTrace tailWord_1039738 prefixEnd_1039738 474564754439607336882967 := by
  unfold tailWord_1039738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9480590076803568489547967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25281573538142849305461245 9480590076803568489547967)
  ·
    refine ⟨14220885115205352734321951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9480590076803568489547967 14220885115205352734321951)
    ·
      refine ⟨21331327672808029101482927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14220885115205352734321951 21331327672808029101482927)
      ·
        refine ⟨31996991509212043652224391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21331327672808029101482927 31996991509212043652224391)
        ·
          refine ⟨47995487263818065478336587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31996991509212043652224391 47995487263818065478336587)
          ·
            refine ⟨71993230895727098217504881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47995487263818065478336587 71993230895727098217504881)
            ·
              refine ⟨53994923171795323663128661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71993230895727098217504881 53994923171795323663128661)
              ·
                refine ⟨632753005919476449177289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 53994923171795323663128661 632753005919476449177289)
                ·
                  refine ⟨474564754439607336882967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632753005919476449177289 474564754439607336882967)
                  ·
                    rfl

theorem cell20_1039738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_1039738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039738 prefixEnd_1039738 := by exact prefixLift 1039738
  have htrace : WordTrace (prefixWord ++ tailWord_1039738) baseStart_1039738 baseEnd_1039738 := by
    simpa [prefixWord, tailWord_1039738, baseEnd_1039738] using wordTrace_append hprefix tailTrace_1039738
  have hstable : (prefixWord ++ tailWord_1039738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039738).length < 2 ^ (prefixWord ++ tailWord_1039738).sum := by decide
  have hdescent : baseEnd_1039738 < baseStart_1039738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039862 : List Nat := [5, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1039862 : Nat := 118140960795 + 1039862 * 2 ^ 59
def prefixEnd_1039862 : Nat := 4983230072969 + 3 ^ 40 * 1039862 * 2
def baseEnd_1039862 : Nat := 474621351418414016749127

theorem tailTrace_1039862 : CollatzResearch.WordTrace tailWord_1039862 prefixEnd_1039862 474621351418414016749127 := by
  unfold tailWord_1039862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370430184922815195981615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25284588639176695423803893 2370430184922815195981615)
  ·
    refine ⟨3555645277384222793972423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370430184922815195981615 3555645277384222793972423)
    ·
      refine ⟨5333467916076334190958635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555645277384222793972423 5333467916076334190958635)
      ·
        refine ⟨8000201874114501286437953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333467916076334190958635 8000201874114501286437953)
        ·
          refine ⟨6000151405585875964828465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8000201874114501286437953 6000151405585875964828465)
          ·
            refine ⟨4500113554189406973621349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6000151405585875964828465 4500113554189406973621349)
            ·
              refine ⟨843771291410513807554003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4500113554189406973621349 843771291410513807554003)
              ·
                refine ⟨1265656937115770711331005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843771291410513807554003 1265656937115770711331005)
                ·
                  refine ⟨474621351418414016749127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265656937115770711331005 474621351418414016749127)
                  ·
                    rfl

theorem cell20_1039862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1039862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039862 prefixEnd_1039862 := by exact prefixLift 1039862
  have htrace : WordTrace (prefixWord ++ tailWord_1039862) baseStart_1039862 baseEnd_1039862 := by
    simpa [prefixWord, tailWord_1039862, baseEnd_1039862] using wordTrace_append hprefix tailTrace_1039862
  have hstable : (prefixWord ++ tailWord_1039862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039862).length < 2 ^ (prefixWord ++ tailWord_1039862).sum := by decide
  have hdescent : baseEnd_1039862 < baseStart_1039862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039866 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_1039866 : Nat := 118140960795 + 1039866 * 2 ^ 59
def prefixEnd_1039866 : Nat := 4983230072969 + 3 ^ 40 * 1039866 * 2
def baseEnd_1039866 : Nat := 474623177127407780615777

theorem tailTrace_1039866 : CollatzResearch.WordTrace tailWord_1039866 prefixEnd_1039866 474623177127407780615777 := by
  unfold tailWord_1039866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9481757212687637954712863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25284685900500367879234301 9481757212687637954712863)
  ·
    refine ⟨14222635819031456932069295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9481757212687637954712863 14222635819031456932069295)
    ·
      refine ⟨21333953728547185398103943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14222635819031456932069295 21333953728547185398103943)
      ·
        refine ⟨32000930592820778097155915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21333953728547185398103943 32000930592820778097155915)
        ·
          refine ⟨48001395889231167145733873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32000930592820778097155915 48001395889231167145733873)
          ·
            refine ⟨36001046916923375359300405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48001395889231167145733873 36001046916923375359300405)
            ·
              refine ⟨3375098148461566439934413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36001046916923375359300405 3375098148461566439934413)
              ·
                refine ⟨1265661805673087414975405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3375098148461566439934413 1265661805673087414975405)
                ·
                  refine ⟨474623177127407780615777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265661805673087414975405 474623177127407780615777)
                  ·
                    rfl

theorem cell20_1039866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_1039866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039866 prefixEnd_1039866 := by exact prefixLift 1039866
  have htrace : WordTrace (prefixWord ++ tailWord_1039866) baseStart_1039866 baseEnd_1039866 := by
    simpa [prefixWord, tailWord_1039866, baseEnd_1039866] using wordTrace_append hprefix tailTrace_1039866
  have hstable : (prefixWord ++ tailWord_1039866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039866).length < 2 ^ (prefixWord ++ tailWord_1039866).sum := by decide
  have hdescent : baseEnd_1039866 < baseStart_1039866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039880 : List Nat := [2, 1, 3, 2, 1, 1, 4, 6]
def baseStart_1039880 : Nat := 118140960795 + 1039880 * 2 ^ 59
def prefixEnd_1039880 : Nat := 4983230072969 + 3 ^ 40 * 1039880 * 2
def baseEnd_1039880 : Nat := 158209855702961984716351

theorem tailTrace_1039880 : CollatzResearch.WordTrace tailWord_1039880 prefixEnd_1039880 158209855702961984716351 := by
  unfold tailWord_1039880
  simp only [CollatzResearch.WordTrace]
  refine ⟨18963769736349916104930547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25285026315133221473240729 18963769736349916104930547)
  ·
    refine ⟨28445654604524874157395821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18963769736349916104930547 28445654604524874157395821)
    ·
      refine ⟨10667120476696827809023433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28445654604524874157395821 10667120476696827809023433)
      ·
        refine ⟨8000340357522620856767575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10667120476696827809023433 8000340357522620856767575)
        ·
          refine ⟨12000510536283931285151363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8000340357522620856767575 12000510536283931285151363)
          ·
            refine ⟨18000765804425896927727045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12000510536283931285151363 18000765804425896927727045)
            ·
              refine ⟨3375143588329855673948821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18000765804425896927727045 3375143588329855673948821)
              ·
                refine ⟨158209855702961984716351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3375143588329855673948821 158209855702961984716351)
                ·
                  rfl

theorem cell20_1039880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_1039880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039880 prefixEnd_1039880 := by exact prefixLift 1039880
  have htrace : WordTrace (prefixWord ++ tailWord_1039880) baseStart_1039880 baseEnd_1039880 := by
    simpa [prefixWord, tailWord_1039880, baseEnd_1039880] using wordTrace_append hprefix tailTrace_1039880
  have hstable : (prefixWord ++ tailWord_1039880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039880).length < 2 ^ (prefixWord ++ tailWord_1039880).sum := by decide
  have hdescent : baseEnd_1039880 < baseStart_1039880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039907 : List Nat := [1, 1, 1, 4, 5, 1, 1, 4, 2]
def baseStart_1039907 : Nat := 118140960795 + 1039907 * 2 ^ 59
def prefixEnd_1039907 : Nat := 4983230072969 + 3 ^ 40 * 1039907 * 2
def baseEnd_1039907 : Nat := 474641890644593860248943

theorem tailTrace_1039907 : CollatzResearch.WordTrace tailWord_1039907 prefixEnd_1039907 474641890644593860248943 := by
  unfold tailWord_1039907
  simp only [CollatzResearch.WordTrace]
  refine ⟨37928524243602015821093975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25285682829068010547395983 37928524243602015821093975)
  ·
    refine ⟨56892786365403023731640963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37928524243602015821093975 56892786365403023731640963)
    ·
      refine ⟨85339179548104535597461445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56892786365403023731640963 85339179548104535597461445)
      ·
        refine ⟨16001096165269600424524021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85339179548104535597461445 16001096165269600424524021)
        ·
          refine ⟨1500102765494025039799127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16001096165269600424524021 1500102765494025039799127)
          ·
            refine ⟨2250154148241037559698691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500102765494025039799127 2250154148241037559698691)
            ·
              refine ⟨3375231222361556339548037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250154148241037559698691 3375231222361556339548037)
              ·
                refine ⟨632855854192791813665257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3375231222361556339548037 632855854192791813665257)
                ·
                  refine ⟨474641890644593860248943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 632855854192791813665257 474641890644593860248943)
                  ·
                    rfl

theorem cell20_1039907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 2].length) (baseStart_1039907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039907 prefixEnd_1039907 := by exact prefixLift 1039907
  have htrace : WordTrace (prefixWord ++ tailWord_1039907) baseStart_1039907 baseEnd_1039907 := by
    simpa [prefixWord, tailWord_1039907, baseEnd_1039907] using wordTrace_append hprefix tailTrace_1039907
  have hstable : (prefixWord ++ tailWord_1039907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039907).length < 2 ^ (prefixWord ++ tailWord_1039907).sum := by decide
  have hdescent : baseEnd_1039907 < baseStart_1039907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039935 : List Nat := [1, 1, 2, 2, 3, 4, 3, 4]
def baseStart_1039935 : Nat := 118140960795 + 1039935 * 2 ^ 59
def prefixEnd_1039935 : Nat := 4983230072969 + 3 ^ 40 * 1039935 * 2
def baseEnd_1039935 : Nat := 158218223535850069105165

theorem tailTrace_1039935 : CollatzResearch.WordTrace tailWord_1039935 prefixEnd_1039935 158218223535850069105165 := by
  unfold tailWord_1039935
  simp only [CollatzResearch.WordTrace]
  refine ⟨37929545487500576603113259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25286363658333717735408839 37929545487500576603113259)
  ·
    refine ⟨56894318231250864904669889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37929545487500576603113259 56894318231250864904669889)
    ·
      refine ⟨42670738673438148678502417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56894318231250864904669889 42670738673438148678502417)
      ·
        refine ⟨32003054005078611508876813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42670738673438148678502417 32003054005078611508876813)
        ·
          refine ⟨12001145251904479315828805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32003054005078611508876813 12001145251904479315828805)
          ·
            refine ⟨2250214734732089871717901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12001145251904479315828805 2250214734732089871717901)
            ·
              refine ⟨843830525524533701894213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2250214734732089871717901 843830525524533701894213)
              ·
                refine ⟨158218223535850069105165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843830525524533701894213 158218223535850069105165)
                ·
                  rfl

theorem cell20_1039935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_1039935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039935 prefixEnd_1039935 := by exact prefixLift 1039935
  have htrace : WordTrace (prefixWord ++ tailWord_1039935) baseStart_1039935 baseEnd_1039935 := by
    simpa [prefixWord, tailWord_1039935, baseEnd_1039935] using wordTrace_append hprefix tailTrace_1039935
  have hstable : (prefixWord ++ tailWord_1039935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039935).length < 2 ^ (prefixWord ++ tailWord_1039935).sum := by decide
  have hdescent : baseEnd_1039935 < baseStart_1039935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039956 : List Nat := [2, 4, 1, 1, 1, 2, 9]
def baseStart_1039956 : Nat := 118140960795 + 1039956 * 2 ^ 59
def prefixEnd_1039956 : Nat := 4983230072969 + 3 ^ 40 * 1039956 * 2
def baseEnd_1039956 : Nat := 52740472842196385290601

theorem tailTrace_1039956 : CollatzResearch.WordTrace tailWord_1039956 prefixEnd_1039956 52740472842196385290601 := by
  unfold tailWord_1039956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965155710212248594813861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25286874280282998126418481 18965155710212248594813861)
  ·
    refine ⟨3555966695664796611527599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18965155710212248594813861 3555966695664796611527599)
    ·
      refine ⟨5333950043497194917291399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3555966695664796611527599 5333950043497194917291399)
      ·
        refine ⟨8000925065245792375937099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5333950043497194917291399 8000925065245792375937099)
        ·
          refine ⟨12001387597868688563905649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8000925065245792375937099 12001387597868688563905649)
          ·
            refine ⟨9001040698401516422929237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12001387597868688563905649 9001040698401516422929237)
            ·
              refine ⟨52740472842196385290601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9001040698401516422929237 52740472842196385290601)
              ·
                rfl

theorem cell20_1039956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 9].length) (baseStart_1039956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039956 prefixEnd_1039956 := by exact prefixLift 1039956
  have htrace : WordTrace (prefixWord ++ tailWord_1039956) baseStart_1039956 baseEnd_1039956 := by
    simpa [prefixWord, tailWord_1039956, baseEnd_1039956] using wordTrace_append hprefix tailTrace_1039956
  have hstable : (prefixWord ++ tailWord_1039956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039956).length < 2 ^ (prefixWord ++ tailWord_1039956).sum := by decide
  have hdescent : baseEnd_1039956 < baseStart_1039956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039959 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 3]
def baseStart_1039959 : Nat := 118140960795 + 1039959 * 2 ^ 59
def prefixEnd_1039959 : Nat := 4983230072969 + 3 ^ 40 * 1039959 * 2
def baseEnd_1039959 : Nat := 474665624861512790515397

theorem tailTrace_1039959 : CollatzResearch.WordTrace tailWord_1039959 prefixEnd_1039959 474665624861512790515397 := by
  unfold tailWord_1039959
  simp only [CollatzResearch.WordTrace]
  refine ⟨37930420839413628701986931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25286947226275752467991287 37930420839413628701986931)
  ·
    refine ⟨56895631259120443052980397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37930420839413628701986931 56895631259120443052980397)
    ·
      refine ⟨21335861722170166144867649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56895631259120443052980397 21335861722170166144867649)
      ·
        refine ⟨16001896291627624608650737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21335861722170166144867649 16001896291627624608650737)
        ·
          refine ⟨12001422218720718456488053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16001896291627624608650737 12001422218720718456488053)
          ·
            refine ⟨1125133333005067355295755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12001422218720718456488053 1125133333005067355295755)
            ·
              refine ⟨1687699999507601032943633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125133333005067355295755 1687699999507601032943633)
              ·
                refine ⟨1265774999630700774707725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1687699999507601032943633 1265774999630700774707725)
                ·
                  refine ⟨474665624861512790515397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265774999630700774707725 474665624861512790515397)
                  ·
                    rfl

theorem cell20_1039959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 3].length) (baseStart_1039959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039959 prefixEnd_1039959 := by exact prefixLift 1039959
  have htrace : WordTrace (prefixWord ++ tailWord_1039959) baseStart_1039959 baseEnd_1039959 := by
    simpa [prefixWord, tailWord_1039959, baseEnd_1039959] using wordTrace_append hprefix tailTrace_1039959
  have hstable : (prefixWord ++ tailWord_1039959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039959).length < 2 ^ (prefixWord ++ tailWord_1039959).sum := by decide
  have hdescent : baseEnd_1039959 < baseStart_1039959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039976 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_1039976 : Nat := 118140960795 + 1039976 * 2 ^ 59
def prefixEnd_1039976 : Nat := 4983230072969 + 3 ^ 40 * 1039976 * 2
def baseEnd_1039976 : Nat := 474673384124736286948661

theorem tailTrace_1039976 : CollatzResearch.WordTrace tailWord_1039976 prefixEnd_1039976 474673384124736286948661 := by
  unfold tailWord_1039976
  simp only [CollatzResearch.WordTrace]
  refine ⟨18965520440176020302677891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25287360586901360403570521 18965520440176020302677891)
  ·
    refine ⟨28448280660264030454016837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18965520440176020302677891 28448280660264030454016837)
    ·
      refine ⟨5334052623799505710128157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28448280660264030454016837 5334052623799505710128157)
      ·
        refine ⟨2000269733924814641298059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5334052623799505710128157 2000269733924814641298059)
        ·
          refine ⟨3000404600887221961947089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2000269733924814641298059 3000404600887221961947089)
          ·
            refine ⟨2250303450665416471460317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3000404600887221961947089 2250303450665416471460317)
            ·
              refine ⟨843863793999531176797619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2250303450665416471460317 843863793999531176797619)
              ·
                refine ⟨1265795690999296765196429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843863793999531176797619 1265795690999296765196429)
                ·
                  refine ⟨474673384124736286948661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265795690999296765196429 474673384124736286948661)
                  ·
                    rfl

theorem cell20_1039976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_1039976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039976 prefixEnd_1039976 := by exact prefixLift 1039976
  have htrace : WordTrace (prefixWord ++ tailWord_1039976) baseStart_1039976 baseEnd_1039976 := by
    simpa [prefixWord, tailWord_1039976, baseEnd_1039976] using wordTrace_append hprefix tailTrace_1039976
  have hstable : (prefixWord ++ tailWord_1039976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039976).length < 2 ^ (prefixWord ++ tailWord_1039976).sum := by decide
  have hdescent : baseEnd_1039976 < baseStart_1039976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1039990 : List Nat := [5, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1039990 : Nat := 118140960795 + 1039990 * 2 ^ 59
def prefixEnd_1039990 : Nat := 4983230072969 + 3 ^ 40 * 1039990 * 2
def baseEnd_1039990 : Nat := 158226591368738153493979

theorem tailTrace_1039990 : CollatzResearch.WordTrace tailWord_1039990 prefixEnd_1039990 158226591368738153493979 := by
  unfold tailWord_1039990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2370721968893832562272839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25287701001534213997576949 2370721968893832562272839)
  ·
    refine ⟨3556082953340748843409259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2370721968893832562272839 3556082953340748843409259)
    ·
      refine ⟨5334124430011123265113889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556082953340748843409259 5334124430011123265113889)
      ·
        refine ⟨4000593322508342448835417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5334124430011123265113889 4000593322508342448835417)
        ·
          refine ⟨3000444991881256836626563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4000593322508342448835417 3000444991881256836626563)
          ·
            refine ⟨4500667487821885254939845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000444991881256836626563 4500667487821885254939845)
            ·
              refine ⟨843875153966603485301221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4500667487821885254939845 843875153966603485301221)
              ·
                refine ⟨158226591368738153493979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 843875153966603485301221 158226591368738153493979)
                ·
                  rfl

theorem cell20_1039990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1039990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1039990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1039990 prefixEnd_1039990 := by exact prefixLift 1039990
  have htrace : WordTrace (prefixWord ++ tailWord_1039990) baseStart_1039990 baseEnd_1039990 := by
    simpa [prefixWord, tailWord_1039990, baseEnd_1039990] using wordTrace_append hprefix tailTrace_1039990
  have hstable : (prefixWord ++ tailWord_1039990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1039990).length < 2 ^ (prefixWord ++ tailWord_1039990).sum := by decide
  have hdescent : baseEnd_1039990 < baseStart_1039990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1039990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040031 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 3]
def baseStart_1040031 : Nat := 118140960795 + 1040031 * 2 ^ 59
def prefixEnd_1040031 : Nat := 4983230072969 + 3 ^ 40 * 1040031 * 2
def baseEnd_1040031 : Nat := 474698487623400540115103

theorem tailTrace_1040031 : CollatzResearch.WordTrace tailWord_1040031 prefixEnd_1040031 474698487623400540115103 := by
  unfold tailWord_1040031
  simp only [CollatzResearch.WordTrace]
  refine ⟨37933046895152784998607947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25288697930101856665738631 37933046895152784998607947)
  ·
    refine ⟨56899570342729177497911921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37933046895152784998607947 56899570342729177497911921)
    ·
      refine ⟨42674677757046883123433941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56899570342729177497911921 42674677757046883123433941)
      ·
        refine ⟨1000187759930786323205483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 42674677757046883123433941 1000187759930786323205483)
        ·
          refine ⟨1500281639896179484808225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000187759930786323205483 1500281639896179484808225)
          ·
            refine ⟨1125211229922134613606169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500281639896179484808225 1125211229922134613606169)
            ·
              refine ⟨843908422441600960204627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125211229922134613606169 843908422441600960204627)
              ·
                refine ⟨1265862633662401440306941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843908422441600960204627 1265862633662401440306941)
                ·
                  refine ⟨474698487623400540115103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265862633662401440306941 474698487623400540115103)
                  ·
                    rfl

theorem cell20_1040031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 3].length) (baseStart_1040031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040031 prefixEnd_1040031 := by exact prefixLift 1040031
  have htrace : WordTrace (prefixWord ++ tailWord_1040031) baseStart_1040031 baseEnd_1040031 := by
    simpa [prefixWord, tailWord_1040031, baseEnd_1040031] using wordTrace_append hprefix tailTrace_1040031
  have hstable : (prefixWord ++ tailWord_1040031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040031).length < 2 ^ (prefixWord ++ tailWord_1040031).sum := by decide
  have hdescent : baseEnd_1040031 < baseStart_1040031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040032 : List Nat := [2, 1, 1, 4, 3, 1, 1, 7]
def baseStart_1040032 : Nat := 118140960795 + 1040032 * 2 ^ 59
def prefixEnd_1040032 : Nat := 4983230072969 + 3 ^ 40 * 1040032 * 2
def baseEnd_1040032 : Nat := 158232981350216327027255

theorem tailTrace_1040032 : CollatzResearch.WordTrace tailWord_1040032 prefixEnd_1040032 158232981350216327027255 := by
  unfold tailWord_1040032
  simp only [CollatzResearch.WordTrace]
  refine ⟨18966541684074581084697175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25288722245432774779596233 18966541684074581084697175)
  ·
    refine ⟨28449812526111871627045763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18966541684074581084697175 28449812526111871627045763)
    ·
      refine ⟨42674718789167807440568645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28449812526111871627045763 42674718789167807440568645)
      ·
        refine ⟨8001509772968963895106621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42674718789167807440568645 8001509772968963895106621)
        ·
          refine ⟨3000566164863361460664983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8001509772968963895106621 3000566164863361460664983)
          ·
            refine ⟨4500849247295042190997475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3000566164863361460664983 4500849247295042190997475)
            ·
              refine ⟨6751273870942563286496213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4500849247295042190997475 6751273870942563286496213)
              ·
                refine ⟨158232981350216327027255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6751273870942563286496213 158232981350216327027255)
                ·
                  rfl

theorem cell20_1040032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_1040032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040032 prefixEnd_1040032 := by exact prefixLift 1040032
  have htrace : WordTrace (prefixWord ++ tailWord_1040032) baseStart_1040032 baseEnd_1040032 := by
    simpa [prefixWord, tailWord_1040032, baseEnd_1040032] using wordTrace_append hprefix tailTrace_1040032
  have hstable : (prefixWord ++ tailWord_1040032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040032).length < 2 ^ (prefixWord ++ tailWord_1040032).sum := by decide
  have hdescent : baseEnd_1040032 < baseStart_1040032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040066 : List Nat := [3, 5, 1, 2, 9]
def baseStart_1040066 : Nat := 118140960795 + 1040066 * 2 ^ 59
def prefixEnd_1040066 : Nat := 4983230072969 + 3 ^ 40 * 1040066 * 2
def baseEnd_1040066 : Nat := 5860672377495012024053

theorem tailTrace_1040066 : CollatzResearch.WordTrace tailWord_1040066 prefixEnd_1040066 5860672377495012024053 := by
  unfold tailWord_1040066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9483580862506496494033013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25289548966683990650754701 9483580862506496494033013)
  ·
    refine ⟨889085705859984046315595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9483580862506496494033013 889085705859984046315595)
    ·
      refine ⟨1333628558789976069473393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889085705859984046315595 1333628558789976069473393)
      ·
        refine ⟨1000221419092482052105045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333628558789976069473393 1000221419092482052105045)
        ·
          refine ⟨5860672377495012024053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 1000221419092482052105045 5860672377495012024053)
          ·
            rfl

theorem cell20_1040066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 9].length) (baseStart_1040066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040066 prefixEnd_1040066 := by exact prefixLift 1040066
  have htrace : WordTrace (prefixWord ++ tailWord_1040066) baseStart_1040066 baseEnd_1040066 := by
    simpa [prefixWord, tailWord_1040066, baseEnd_1040066] using wordTrace_append hprefix tailTrace_1040066
  have hstable : (prefixWord ++ tailWord_1040066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040066).length < 2 ^ (prefixWord ++ tailWord_1040066).sum := by decide
  have hdescent : baseEnd_1040066 < baseStart_1040066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040101 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_1040101 : Nat := 118140960795 + 1040101 * 2 ^ 59
def prefixEnd_1040101 : Nat := 4983230072969 + 3 ^ 40 * 1040101 * 2
def baseEnd_1040101 : Nat := 474730437530791407781483

theorem tailTrace_1040101 : CollatzResearch.WordTrace tailWord_1040101 prefixEnd_1040101 474730437530791407781483 := by
  unfold tailWord_1040101
  simp only [CollatzResearch.WordTrace]
  refine ⟨37935600004899186953656157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25290400003266124635770771 37935600004899186953656157)
  ·
    refine ⟨14225850001837195107621059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37935600004899186953656157 14225850001837195107621059)
    ·
      refine ⟨21338775002755792661431589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14225850001837195107621059 21338775002755792661431589)
      ·
        refine ⟨4001020313016711124018423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21338775002755792661431589 4001020313016711124018423)
        ·
          refine ⟨6001530469525066686027635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001020313016711124018423 6001530469525066686027635)
          ·
            refine ⟨9002295704287600029041453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6001530469525066686027635 9002295704287600029041453)
            ·
              refine ⟨3375860889107850010890545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9002295704287600029041453 3375860889107850010890545)
              ·
                refine ⟨2531895666830887508167909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3375860889107850010890545 2531895666830887508167909)
                ·
                  refine ⟨474730437530791407781483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2531895666830887508167909 474730437530791407781483)
                  ·
                    rfl

theorem cell20_1040101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_1040101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040101 prefixEnd_1040101 := by exact prefixLift 1040101
  have htrace : WordTrace (prefixWord ++ tailWord_1040101) baseStart_1040101 baseEnd_1040101 := by
    simpa [prefixWord, tailWord_1040101, baseEnd_1040101] using wordTrace_append hprefix tailTrace_1040101
  have hstable : (prefixWord ++ tailWord_1040101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040101).length < 2 ^ (prefixWord ++ tailWord_1040101).sum := by decide
  have hdescent : baseEnd_1040101 < baseStart_1040101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040122 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1040122 : Nat := 118140960795 + 1040122 * 2 ^ 59
def prefixEnd_1040122 : Nat := 4983230072969 + 3 ^ 40 * 1040122 * 2
def baseEnd_1040122 : Nat := 474740022503008668081397

theorem tailTrace_1040122 : CollatzResearch.WordTrace tailWord_1040122 prefixEnd_1040122 474740022503008668081397 := by
  unfold tailWord_1040122
  simp only [CollatzResearch.WordTrace]
  refine ⟨9484091484455776885042655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25290910625215405026780413 9484091484455776885042655)
  ·
    refine ⟨14226137226683665327563983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9484091484455776885042655 14226137226683665327563983)
    ·
      refine ⟨21339205840025497991345975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14226137226683665327563983 21339205840025497991345975)
      ·
        refine ⟨32008808760038246987018963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21339205840025497991345975 32008808760038246987018963)
        ·
          refine ⟨48013213140057370480528445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32008808760038246987018963 48013213140057370480528445)
          ·
            refine ⟨18004954927521513930198167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48013213140057370480528445 18004954927521513930198167)
            ·
              refine ⟨27007432391282270895297251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18004954927521513930198167 27007432391282270895297251)
              ·
                refine ⟨40511148586923406342945877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27007432391282270895297251 40511148586923406342945877)
                ·
                  refine ⟨474740022503008668081397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40511148586923406342945877 474740022503008668081397)
                  ·
                    rfl

theorem cell20_1040122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1040122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040122 prefixEnd_1040122 := by exact prefixLift 1040122
  have htrace : WordTrace (prefixWord ++ tailWord_1040122) baseStart_1040122 baseEnd_1040122 := by
    simpa [prefixWord, tailWord_1040122, baseEnd_1040122] using wordTrace_append hprefix tailTrace_1040122
  have hstable : (prefixWord ++ tailWord_1040122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040122).length < 2 ^ (prefixWord ++ tailWord_1040122).sum := by decide
  have hdescent : baseEnd_1040122 < baseStart_1040122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040132 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1040132 : Nat := 118140960795 + 1040132 * 2 ^ 59
def prefixEnd_1040132 : Nat := 4983230072969 + 3 ^ 40 * 1040132 * 2
def baseEnd_1040132 : Nat := 474744586775493077748023

theorem tailTrace_1040132 : CollatzResearch.WordTrace tailWord_1040132 prefixEnd_1040132 474744586775493077748023 := by
  unfold tailWord_1040132
  simp only [CollatzResearch.WordTrace]
  refine ⟨18968365333893439624017325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25291153778524586165356433 18968365333893439624017325)
  ·
    refine ⟨7113137000210039859006497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18968365333893439624017325 7113137000210039859006497)
    ·
      refine ⟨5334852750157529894254873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7113137000210039859006497 5334852750157529894254873)
      ·
        refine ⟨4001139562618147420691155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5334852750157529894254873 4001139562618147420691155)
        ·
          refine ⟨6001709343927221131036733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001139562618147420691155 6001709343927221131036733)
          ·
            refine ⟨2250641003972707924138775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6001709343927221131036733 2250641003972707924138775)
            ·
              refine ⟨3375961505959061886208163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2250641003972707924138775 3375961505959061886208163)
              ·
                refine ⟨5063942258938592829312245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3375961505959061886208163 5063942258938592829312245)
                ·
                  refine ⟨474744586775493077748023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5063942258938592829312245 474744586775493077748023)
                  ·
                    rfl

theorem cell20_1040132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1040132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040132 prefixEnd_1040132 := by exact prefixLift 1040132
  have htrace : WordTrace (prefixWord ++ tailWord_1040132) baseStart_1040132 baseEnd_1040132 := by
    simpa [prefixWord, tailWord_1040132, baseEnd_1040132] using wordTrace_append hprefix tailTrace_1040132
  have hstable : (prefixWord ++ tailWord_1040132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040132).length < 2 ^ (prefixWord ++ tailWord_1040132).sum := by decide
  have hdescent : baseEnd_1040132 < baseStart_1040132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040141 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1040141 : Nat := 118140960795 + 1040141 * 2 ^ 59
def prefixEnd_1040141 : Nat := 4983230072969 + 3 ^ 40 * 1040141 * 2
def baseEnd_1040141 : Nat := 474748694620729046447987

theorem tailTrace_1040141 : CollatzResearch.WordTrace tailWord_1040141 prefixEnd_1040141 474748694620729046447987 := by
  unfold tailWord_1040141
  simp only [CollatzResearch.WordTrace]
  refine ⟨37937058924754273785112277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25291372616502849190074851 37937058924754273785112277)
  ·
    refine ⟨889149818548928291838569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 37937058924754273785112277 889149818548928291838569)
    ·
      refine ⟨666862363911696218878927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 889149818548928291838569 666862363911696218878927)
      ·
        refine ⟨1000293545867544328318391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666862363911696218878927 1000293545867544328318391)
        ·
          refine ⟨1500440318801316492477587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1000293545867544328318391 1500440318801316492477587)
          ·
            refine ⟨2250660478201974738716381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500440318801316492477587 2250660478201974738716381)
            ·
              refine ⟨843997679325740527018643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2250660478201974738716381 843997679325740527018643)
              ·
                refine ⟨1265996518988610790527965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 843997679325740527018643 1265996518988610790527965)
                ·
                  refine ⟨474748694620729046447987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1265996518988610790527965 474748694620729046447987)
                  ·
                    rfl

theorem cell20_1040141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1040141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040141 prefixEnd_1040141 := by exact prefixLift 1040141
  have htrace : WordTrace (prefixWord ++ tailWord_1040141) baseStart_1040141 baseEnd_1040141 := by
    simpa [prefixWord, tailWord_1040141, baseEnd_1040141] using wordTrace_append hprefix tailTrace_1040141
  have hstable : (prefixWord ++ tailWord_1040141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040141).length < 2 ^ (prefixWord ++ tailWord_1040141).sum := by decide
  have hdescent : baseEnd_1040141 < baseStart_1040141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040149 : List Nat := [1, 3, 2, 1, 2, 4, 3, 1, 3]
def baseStart_1040149 : Nat := 118140960795 + 1040149 * 2 ^ 59
def prefixEnd_1040149 : Nat := 4983230072969 + 3 ^ 40 * 1040149 * 2
def baseEnd_1040149 : Nat := 474752346038716574181287

theorem tailTrace_1040149 : CollatzResearch.WordTrace tailWord_1040149 prefixEnd_1040149 474752346038716574181287 := by
  unfold tailWord_1040149
  simp only [CollatzResearch.WordTrace]
  refine ⟨37937350708725291151403501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25291567139150194100935667 37937350708725291151403501)
  ·
    refine ⟨14226506515771984181776313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37937350708725291151403501 14226506515771984181776313)
    ·
      refine ⟨10669879886828988136332235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14226506515771984181776313 10669879886828988136332235)
      ·
        refine ⟨16004819830243482204498353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10669879886828988136332235 16004819830243482204498353)
        ·
          refine ⟨12003614872682611653373765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16004819830243482204498353 12003614872682611653373765)
          ·
            refine ⟨2250677788627989685007581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12003614872682611653373765 2250677788627989685007581)
            ·
              refine ⟨844004170735496131877843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2250677788627989685007581 844004170735496131877843)
              ·
                refine ⟨1266006256103244197816765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844004170735496131877843 1266006256103244197816765)
                ·
                  refine ⟨474752346038716574181287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266006256103244197816765 474752346038716574181287)
                  ·
                    rfl

theorem cell20_1040149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_1040149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040149 prefixEnd_1040149 := by exact prefixLift 1040149
  have htrace : WordTrace (prefixWord ++ tailWord_1040149) baseStart_1040149 baseEnd_1040149 := by
    simpa [prefixWord, tailWord_1040149, baseEnd_1040149] using wordTrace_append hprefix tailTrace_1040149
  have hstable : (prefixWord ++ tailWord_1040149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040149).length < 2 ^ (prefixWord ++ tailWord_1040149).sum := by decide
  have hdescent : baseEnd_1040149 < baseStart_1040149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040184 : List Nat := [2, 1, 2, 1, 3, 5, 6]
def baseStart_1040184 : Nat := 118140960795 + 1040184 * 2 ^ 59
def prefixEnd_1040184 : Nat := 4983230072969 + 3 ^ 40 * 1040184 * 2
def baseEnd_1040184 : Nat := 52752035665823556446053

theorem tailTrace_1040184 : CollatzResearch.WordTrace tailWord_1040184 prefixEnd_1040184 52752035665823556446053 := by
  unfold tailWord_1040184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969313631799246064463803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25292418175732328085951737 18969313631799246064463803)
  ·
    refine ⟨28453970447698869096695705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18969313631799246064463803 28453970447698869096695705)
    ·
      refine ⟨21340477835774151822521779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28453970447698869096695705 21340477835774151822521779)
      ·
        refine ⟨32010716753661227733782669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21340477835774151822521779 32010716753661227733782669)
        ·
          refine ⟨12004018782622960400168501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32010716753661227733782669 12004018782622960400168501)
          ·
            refine ⟨1125376760870902537515797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12004018782622960400168501 1125376760870902537515797)
            ·
              refine ⟨52752035665823556446053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1125376760870902537515797 52752035665823556446053)
              ·
                rfl

theorem cell20_1040184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 6].length) (baseStart_1040184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040184 prefixEnd_1040184 := by exact prefixLift 1040184
  have htrace : WordTrace (prefixWord ++ tailWord_1040184) baseStart_1040184 baseEnd_1040184 := by
    simpa [prefixWord, tailWord_1040184, baseEnd_1040184] using wordTrace_append hprefix tailTrace_1040184
  have hstable : (prefixWord ++ tailWord_1040184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040184).length < 2 ^ (prefixWord ++ tailWord_1040184).sum := by decide
  have hdescent : baseEnd_1040184 < baseStart_1040184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040190 : List Nat := [4, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_1040190 : Nat := 118140960795 + 1040190 * 2 ^ 59
def prefixEnd_1040190 : Nat := 4983230072969 + 3 ^ 40 * 1040190 * 2
def baseEnd_1040190 : Nat := 474771059555902653814453

theorem tailTrace_1040190 : CollatzResearch.WordTrace tailWord_1040190 prefixEnd_1040190 474771059555902653814453 := by
  unfold tailWord_1040190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4742355762697094394205753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25292564067717836769097349 4742355762697094394205753)
  ·
    refine ⟨3556766822022820795654315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4742355762697094394205753 3556766822022820795654315)
    ·
      refine ⟨5335150233034231193481473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3556766822022820795654315 5335150233034231193481473)
      ·
        refine ⟨4001362674775673395111105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5335150233034231193481473 4001362674775673395111105)
        ·
          refine ⟨3001022006081755046333329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4001362674775673395111105 3001022006081755046333329)
          ·
            refine ⟨2250766504561316284749997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3001022006081755046333329 2250766504561316284749997)
            ·
              refine ⟨844037439210493606781249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2250766504561316284749997 844037439210493606781249)
              ·
                refine ⟨633028079407870205085937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844037439210493606781249 633028079407870205085937)
                ·
                  refine ⟨474771059555902653814453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633028079407870205085937 474771059555902653814453)
                  ·
                    rfl

theorem cell20_1040190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_1040190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040190 prefixEnd_1040190 := by exact prefixLift 1040190
  have htrace : WordTrace (prefixWord ++ tailWord_1040190) baseStart_1040190 baseEnd_1040190 := by
    simpa [prefixWord, tailWord_1040190, baseEnd_1040190] using wordTrace_append hprefix tailTrace_1040190
  have hstable : (prefixWord ++ tailWord_1040190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040190).length < 2 ^ (prefixWord ++ tailWord_1040190).sum := by decide
  have hdescent : baseEnd_1040190 < baseStart_1040190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040204 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_1040204 : Nat := 118140960795 + 1040204 * 2 ^ 59
def prefixEnd_1040204 : Nat := 4983230072969 + 3 ^ 40 * 1040204 * 2
def baseEnd_1040204 : Nat := 474777449537380827347729

theorem tailTrace_1040204 : CollatzResearch.WordTrace tailWord_1040204 prefixEnd_1040204 474777449537380827347729 := by
  unfold tailWord_1040204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18969678361763017772327833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25292904482350690363103777 18969678361763017772327833)
  ·
    refine ⟨14227258771322263329245875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18969678361763017772327833 14227258771322263329245875)
    ·
      refine ⟨21340888156983394993868813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14227258771322263329245875 21340888156983394993868813)
      ·
        refine ⟨8002833058868773122700805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21340888156983394993868813 8002833058868773122700805)
        ·
          refine ⟨1500531198537894960506401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8002833058868773122700805 1500531198537894960506401)
          ·
            refine ⟨1125398398903421220379801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1500531198537894960506401 1125398398903421220379801)
            ·
              refine ⟨844048799177565915284851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125398398903421220379801 844048799177565915284851)
              ·
                refine ⟨1266073198766348872927277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844048799177565915284851 1266073198766348872927277)
                ·
                  refine ⟨474777449537380827347729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266073198766348872927277 474777449537380827347729)
                  ·
                    rfl

theorem cell20_1040204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_1040204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040204 prefixEnd_1040204 := by exact prefixLift 1040204
  have htrace : WordTrace (prefixWord ++ tailWord_1040204) baseStart_1040204 baseEnd_1040204 := by
    simpa [prefixWord, tailWord_1040204, baseEnd_1040204] using wordTrace_append hprefix tailTrace_1040204
  have hstable : (prefixWord ++ tailWord_1040204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040204).length < 2 ^ (prefixWord ++ tailWord_1040204).sum := by decide
  have hdescent : baseEnd_1040204 < baseStart_1040204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040232 : List Nat := [2, 1, 4, 2, 1, 1, 2, 5, 2]
def baseStart_1040232 : Nat := 118140960795 + 1040232 * 2 ^ 59
def prefixEnd_1040232 : Nat := 4983230072969 + 3 ^ 40 * 1040232 * 2
def baseEnd_1040232 : Nat := 474790229500337174414281

theorem tailTrace_1040232 : CollatzResearch.WordTrace tailWord_1040232 prefixEnd_1040232 474790229500337174414281 := by
  unfold tailWord_1040232
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970188983712298163337475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25293585311616397551116633 18970188983712298163337475)
  ·
    refine ⟨28455283475568447245006213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18970188983712298163337475 28455283475568447245006213)
    ·
      refine ⟨5335365651669083858438665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28455283475568447245006213 5335365651669083858438665)
      ·
        refine ⟨4001524238751812893828999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5335365651669083858438665 4001524238751812893828999)
        ·
          refine ⟨6002286358127719340743499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4001524238751812893828999 6002286358127719340743499)
          ·
            refine ⟨9003429537191579011115249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6002286358127719340743499 9003429537191579011115249)
            ·
              refine ⟨6752572152893684258336437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9003429537191579011115249 6752572152893684258336437)
              ·
                refine ⟨633053639333782899219041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6752572152893684258336437 633053639333782899219041)
                ·
                  refine ⟨474790229500337174414281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633053639333782899219041 474790229500337174414281)
                  ·
                    rfl

theorem cell20_1040232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_1040232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040232 prefixEnd_1040232 := by exact prefixLift 1040232
  have htrace : WordTrace (prefixWord ++ tailWord_1040232) baseStart_1040232 baseEnd_1040232 := by
    simpa [prefixWord, tailWord_1040232, baseEnd_1040232] using wordTrace_append hprefix tailTrace_1040232
  have hstable : (prefixWord ++ tailWord_1040232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040232).length < 2 ^ (prefixWord ++ tailWord_1040232).sum := by decide
  have hdescent : baseEnd_1040232 < baseStart_1040232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040260 : List Nat := [2, 3, 2, 1, 1, 1, 5, 5]
def baseStart_1040260 : Nat := 118140960795 + 1040260 * 2 ^ 59
def prefixEnd_1040260 : Nat := 4983230072969 + 3 ^ 40 * 1040260 * 2
def baseEnd_1040260 : Nat := 158267669821097840493611

theorem tailTrace_1040260 : CollatzResearch.WordTrace tailWord_1040260 prefixEnd_1040260 158267669821097840493611 := by
  unfold tailWord_1040260
  simp only [CollatzResearch.WordTrace]
  refine ⟨18970699605661578554347117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25294266140882104739129489 18970699605661578554347117)
  ·
    refine ⟨7114012352123091957880169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18970699605661578554347117 7114012352123091957880169)
    ·
      refine ⟨5335509264092318968410127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7114012352123091957880169 5335509264092318968410127)
      ·
        refine ⟨8003263896138478452615191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5335509264092318968410127 8003263896138478452615191)
        ·
          refine ⟨12004895844207717678922787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8003263896138478452615191 12004895844207717678922787)
          ·
            refine ⟨18007343766311576518384181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12004895844207717678922787 18007343766311576518384181)
            ·
              refine ⟨1688188478091710298598517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18007343766311576518384181 1688188478091710298598517)
              ·
                refine ⟨158267669821097840493611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1688188478091710298598517 158267669821097840493611)
                ·
                  rfl

theorem cell20_1040260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_1040260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040260 prefixEnd_1040260 := by exact prefixLift 1040260
  have htrace : WordTrace (prefixWord ++ tailWord_1040260) baseStart_1040260 baseEnd_1040260 := by
    simpa [prefixWord, tailWord_1040260, baseEnd_1040260] using wordTrace_append hprefix tailTrace_1040260
  have hstable : (prefixWord ++ tailWord_1040260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040260).length < 2 ^ (prefixWord ++ tailWord_1040260).sum := by decide
  have hdescent : baseEnd_1040260 < baseStart_1040260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040281 : List Nat := [1, 2, 1, 2, 1, 3, 2, 8]
def baseStart_1040281 : Nat := 118140960795 + 1040281 * 2 ^ 59
def prefixEnd_1040281 : Nat := 4983230072969 + 3 ^ 40 * 1040281 * 2
def baseEnd_1040281 : Nat := 158270864811836927260249

theorem tailTrace_1040281 : CollatzResearch.WordTrace tailWord_1040281 prefixEnd_1040281 158270864811836927260249 := by
  unfold tailWord_1040281
  simp only [CollatzResearch.WordTrace]
  refine ⟨37942165144247077695208697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25294776762831385130139131 37942165144247077695208697)
  ·
    refine ⟨28456623858185308271406523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37942165144247077695208697 28456623858185308271406523)
    ·
      refine ⟨42684935787277962407109785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28456623858185308271406523 42684935787277962407109785)
      ·
        refine ⟨32013701840458471805332339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42684935787277962407109785 32013701840458471805332339)
        ·
          refine ⟨48020552760687707707998509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32013701840458471805332339 48020552760687707707998509)
          ·
            refine ⟨18007707285257890390499441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48020552760687707707998509 18007707285257890390499441)
            ·
              refine ⟨13505780463943417792874581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18007707285257890390499441 13505780463943417792874581)
              ·
                refine ⟨158270864811836927260249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13505780463943417792874581 158270864811836927260249)
                ·
                  rfl

theorem cell20_1040281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_1040281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040281 prefixEnd_1040281 := by exact prefixLift 1040281
  have htrace : WordTrace (prefixWord ++ tailWord_1040281) baseStart_1040281 baseEnd_1040281 := by
    simpa [prefixWord, tailWord_1040281, baseEnd_1040281] using wordTrace_append hprefix tailTrace_1040281
  have hstable : (prefixWord ++ tailWord_1040281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040281).length < 2 ^ (prefixWord ++ tailWord_1040281).sum := by decide
  have hdescent : baseEnd_1040281 < baseStart_1040281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040287 : List Nat := [1, 1, 2, 5, 3, 1, 2, 3, 2]
def baseStart_1040287 : Nat := 118140960795 + 1040287 * 2 ^ 59
def prefixEnd_1040287 : Nat := 4983230072969 + 3 ^ 40 * 1040287 * 2
def baseEnd_1040287 : Nat := 474815332999001427580723

theorem tailTrace_1040287 : CollatzResearch.WordTrace tailWord_1040287 prefixEnd_1040287 474815332999001427580723 := by
  unfold tailWord_1040287
  simp only [CollatzResearch.WordTrace]
  refine ⟨37942383982225340719927115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25294922654816893813284743 37942383982225340719927115)
  ·
    refine ⟨56913575973338011079890673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37942383982225340719927115 56913575973338011079890673)
    ·
      refine ⟨42685181980003508309918005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56913575973338011079890673 42685181980003508309918005)
      ·
        refine ⟨4001735810625328904054813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42685181980003508309918005 4001735810625328904054813)
        ·
          refine ⟨1500650928984498339020555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4001735810625328904054813 1500650928984498339020555)
          ·
            refine ⟨2250976393476747508530833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500650928984498339020555 2250976393476747508530833)
            ·
              refine ⟨1688232295107560631398125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2250976393476747508530833 1688232295107560631398125)
              ·
                refine ⟨633087110665335236774297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1688232295107560631398125 633087110665335236774297)
                ·
                  refine ⟨474815332999001427580723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633087110665335236774297 474815332999001427580723)
                  ·
                    rfl

theorem cell20_1040287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 2].length) (baseStart_1040287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040287 prefixEnd_1040287 := by exact prefixLift 1040287
  have htrace : WordTrace (prefixWord ++ tailWord_1040287) baseStart_1040287 baseEnd_1040287 := by
    simpa [prefixWord, tailWord_1040287, baseEnd_1040287] using wordTrace_append hprefix tailTrace_1040287
  have hstable : (prefixWord ++ tailWord_1040287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040287).length < 2 ^ (prefixWord ++ tailWord_1040287).sum := by decide
  have hdescent : baseEnd_1040287 < baseStart_1040287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040319 : List Nat := [1, 1, 2, 2, 2, 1, 4, 7]
def baseStart_1040319 : Nat := 118140960795 + 1040319 * 2 ^ 59
def prefixEnd_1040319 : Nat := 4983230072969 + 3 ^ 40 * 1040319 * 2
def baseEnd_1040319 : Nat := 158276646223650512837975

theorem tailTrace_1040319 : CollatzResearch.WordTrace tailWord_1040319 prefixEnd_1040319 158276646223650512837975 := by
  unfold tailWord_1040319
  simp only [CollatzResearch.WordTrace]
  refine ⟨37943551118109410185092011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25295700745406273456728007 37943551118109410185092011)
  ·
    refine ⟨56915326677164115277638017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37943551118109410185092011 56915326677164115277638017)
    ·
      refine ⟨42686495007873086458228513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56915326677164115277638017 42686495007873086458228513)
      ·
        refine ⟨32014871255904814843671385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42686495007873086458228513 32014871255904814843671385)
        ·
          refine ⟨24011153441928611132753539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32014871255904814843671385 24011153441928611132753539)
          ·
            refine ⟨36016730162892916699130309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24011153441928611132753539 36016730162892916699130309)
            ·
              refine ⟨6753136905542421881086933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36016730162892916699130309 6753136905542421881086933)
              ·
                refine ⟨158276646223650512837975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6753136905542421881086933 158276646223650512837975)
                ·
                  rfl

theorem cell20_1040319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_1040319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040319 prefixEnd_1040319 := by exact prefixLift 1040319
  have htrace : WordTrace (prefixWord ++ tailWord_1040319) baseStart_1040319 baseEnd_1040319 := by
    simpa [prefixWord, tailWord_1040319, baseEnd_1040319] using wordTrace_append hprefix tailTrace_1040319
  have hstable : (prefixWord ++ tailWord_1040319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040319).length < 2 ^ (prefixWord ++ tailWord_1040319).sum := by decide
  have hdescent : baseEnd_1040319 < baseStart_1040319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040336 : List Nat := [2, 1, 1, 1, 1, 2, 8, 4]
def baseStart_1040336 : Nat := 118140960795 + 1040336 * 2 ^ 59
def prefixEnd_1040336 : Nat := 4983230072969 + 3 ^ 40 * 1040336 * 2
def baseEnd_1040336 : Nat := 158279232644725011649063

theorem tailTrace_1040336 : CollatzResearch.WordTrace tailWord_1040336 prefixEnd_1040336 158279232644725011649063 := by
  unfold tailWord_1040336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18972085579523911044230431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25296114106031881392307241 18972085579523911044230431)
  ·
    refine ⟨28458128369285866566345647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18972085579523911044230431 28458128369285866566345647)
    ·
      refine ⟨42687192553928799849518471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28458128369285866566345647 42687192553928799849518471)
      ·
        refine ⟨64030788830893199774277707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42687192553928799849518471 64030788830893199774277707)
        ·
          refine ⟨96046183246339799661416561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64030788830893199774277707 96046183246339799661416561)
          ·
            refine ⟨72034637434754849746062421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96046183246339799661416561 72034637434754849746062421)
            ·
              refine ⟨844155907438533395461669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 72034637434754849746062421 844155907438533395461669)
              ·
                refine ⟨158279232644725011649063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844155907438533395461669 158279232644725011649063)
                ·
                  rfl

theorem cell20_1040336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_1040336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040336 prefixEnd_1040336 := by exact prefixLift 1040336
  have htrace : WordTrace (prefixWord ++ tailWord_1040336) baseStart_1040336 baseEnd_1040336 := by
    simpa [prefixWord, tailWord_1040336, baseEnd_1040336] using wordTrace_append hprefix tailTrace_1040336
  have hstable : (prefixWord ++ tailWord_1040336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040336).length < 2 ^ (prefixWord ++ tailWord_1040336).sum := by decide
  have hdescent : baseEnd_1040336 < baseStart_1040336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040377 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 3]
def baseStart_1040377 : Nat := 118140960795 + 1040377 * 2 ^ 59
def prefixEnd_1040377 : Nat := 4983230072969 + 3 ^ 40 * 1040377 * 2
def baseEnd_1040377 : Nat := 474856411451361114580355

theorem tailTrace_1040377 : CollatzResearch.WordTrace tailWord_1040377 prefixEnd_1040377 474856411451361114580355 := by
  unfold tailWord_1040377
  simp only [CollatzResearch.WordTrace]
  refine ⟨37945666551899286090703385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25297111034599524060468923 37945666551899286090703385)
  ·
    refine ⟨28459249913924464568027539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37945666551899286090703385 28459249913924464568027539)
    ·
      refine ⟨42688874870886696852041309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28459249913924464568027539 42688874870886696852041309)
      ·
        refine ⟨16008328076582511319515491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42688874870886696852041309 16008328076582511319515491)
        ·
          refine ⟨24012492114873766979273237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16008328076582511319515491 24012492114873766979273237)
          ·
            refine ⟨1125585567884707827153433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24012492114873766979273237 1125585567884707827153433)
            ·
              refine ⟨844189175913530870365075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125585567884707827153433 844189175913530870365075)
              ·
                refine ⟨1266283763870296305547613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844189175913530870365075 1266283763870296305547613)
                ·
                  refine ⟨474856411451361114580355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266283763870296305547613 474856411451361114580355)
                  ·
                    rfl

theorem cell20_1040377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_1040377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040377 prefixEnd_1040377 := by exact prefixLift 1040377
  have htrace : WordTrace (prefixWord ++ tailWord_1040377) baseStart_1040377 baseEnd_1040377 := by
    simpa [prefixWord, tailWord_1040377, baseEnd_1040377] using wordTrace_append hprefix tailTrace_1040377
  have hstable : (prefixWord ++ tailWord_1040377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040377).length < 2 ^ (prefixWord ++ tailWord_1040377).sum := by decide
  have hdescent : baseEnd_1040377 < baseStart_1040377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040395 : List Nat := [1, 1, 1, 1, 6, 1, 1, 8]
def baseStart_1040395 : Nat := 118140960795 + 1040395 * 2 ^ 59
def prefixEnd_1040395 : Nat := 4983230072969 + 3 ^ 40 * 1040395 * 2
def baseEnd_1040395 : Nat := 158288209047277683993427

theorem tailTrace_1040395 : CollatzResearch.WordTrace tailWord_1040395 prefixEnd_1040395 158288209047277683993427 := by
  unfold tailWord_1040395
  simp only [CollatzResearch.WordTrace]
  refine ⟨37946323065834075164858639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25297548710556050109905759 37946323065834075164858639)
  ·
    refine ⟨56919484598751112747287959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37946323065834075164858639 56919484598751112747287959)
    ·
      refine ⟨85379226898126669120931939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56919484598751112747287959 85379226898126669120931939)
      ·
        refine ⟨128068840347190003681397909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85379226898126669120931939 128068840347190003681397909)
        ·
          refine ⟨6003226891274531422565527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 128068840347190003681397909 6003226891274531422565527)
          ·
            refine ⟨9004840336911797133848291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6003226891274531422565527 9004840336911797133848291)
            ·
              refine ⟨13507260505367695700772437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9004840336911797133848291 13507260505367695700772437)
              ·
                refine ⟨158288209047277683993427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13507260505367695700772437 158288209047277683993427)
                ·
                  rfl

theorem cell20_1040395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_1040395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040395 prefixEnd_1040395 := by exact prefixLift 1040395
  have htrace : WordTrace (prefixWord ++ tailWord_1040395) baseStart_1040395 baseEnd_1040395 := by
    simpa [prefixWord, tailWord_1040395, baseEnd_1040395] using wordTrace_append hprefix tailTrace_1040395
  have hstable : (prefixWord ++ tailWord_1040395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040395).length < 2 ^ (prefixWord ++ tailWord_1040395).sum := by decide
  have hdescent : baseEnd_1040395 < baseStart_1040395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040446 : List Nat := [4, 2, 1, 3, 2, 1, 3, 4]
def baseStart_1040446 : Nat := 118140960795 + 1040446 * 2 ^ 59
def prefixEnd_1040446 : Nat := 4983230072969 + 3 ^ 40 * 1040446 * 2
def baseEnd_1040446 : Nat := 158295968310501180426691

theorem tailTrace_1040446 : CollatzResearch.WordTrace tailWord_1040446 prefixEnd_1040446 158295968310501180426691 := by
  unfold tailWord_1040446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4743522898581163859370649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25298788792432873916643461 4743522898581163859370649)
  ·
    refine ⟨3557642173935872894527987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4743522898581163859370649 3557642173935872894527987)
    ·
      refine ⟨5336463260903809341791981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3557642173935872894527987 5336463260903809341791981)
      ·
        refine ⟨2001173722838928503171993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5336463260903809341791981 2001173722838928503171993)
        ·
          refine ⟨1500880292129196377378995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2001173722838928503171993 1500880292129196377378995)
          ·
            refine ⟨2251320438193794566068493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1500880292129196377378995 2251320438193794566068493)
            ·
              refine ⟨844245164322672962275685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2251320438193794566068493 844245164322672962275685)
              ·
                refine ⟨158295968310501180426691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844245164322672962275685 158295968310501180426691)
                ·
                  rfl

theorem cell20_1040446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_1040446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040446 prefixEnd_1040446 := by exact prefixLift 1040446
  have htrace : WordTrace (prefixWord ++ tailWord_1040446) baseStart_1040446 baseEnd_1040446 := by
    simpa [prefixWord, tailWord_1040446, baseEnd_1040446] using wordTrace_append hprefix tailTrace_1040446
  have hstable : (prefixWord ++ tailWord_1040446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040446).length < 2 ^ (prefixWord ++ tailWord_1040446).sum := by decide
  have hdescent : baseEnd_1040446 < baseStart_1040446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040470 : List Nat := [5, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1040470 : Nat := 118140960795 + 1040470 * 2 ^ 59
def prefixEnd_1040470 : Nat := 4983230072969 + 3 ^ 40 * 1040470 * 2
def baseEnd_1040470 : Nat := 474898859185466124479975

theorem tailTrace_1040470 : CollatzResearch.WordTrace tailWord_1040470 prefixEnd_1040470 474898859185466124479975 := by
  unfold tailWord_1040470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2371816158785147685864929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25299372360374908649225909 2371816158785147685864929)
  ·
    refine ⟨1778862119088860764398697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2371816158785147685864929 1778862119088860764398697)
    ·
      refine ⟨1334146589316645573299023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1778862119088860764398697 1334146589316645573299023)
      ·
        refine ⟨2001219883974968359948535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334146589316645573299023 2001219883974968359948535)
        ·
          refine ⟨3001829825962452539922803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001219883974968359948535 3001829825962452539922803)
          ·
            refine ⟨4502744738943678809884205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001829825962452539922803 4502744738943678809884205)
            ·
              refine ⟨1688529277103879553706577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4502744738943678809884205 1688529277103879553706577)
              ·
                refine ⟨1266396957827909665279933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1688529277103879553706577 1266396957827909665279933)
                ·
                  refine ⟨474898859185466124479975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266396957827909665279933 474898859185466124479975)
                  ·
                    rfl

theorem cell20_1040470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1040470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040470 prefixEnd_1040470 := by exact prefixLift 1040470
  have htrace : WordTrace (prefixWord ++ tailWord_1040470) baseStart_1040470 baseEnd_1040470 := by
    simpa [prefixWord, tailWord_1040470, baseEnd_1040470] using wordTrace_append hprefix tailTrace_1040470
  have hstable : (prefixWord ++ tailWord_1040470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040470).length < 2 ^ (prefixWord ++ tailWord_1040470).sum := by decide
  have hdescent : baseEnd_1040470 < baseStart_1040470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040477 : List Nat := [1, 4, 4, 1, 1, 1, 2, 4, 2]
def baseStart_1040477 : Nat := 118140960795 + 1040477 * 2 ^ 59
def prefixEnd_1040477 : Nat := 4983230072969 + 3 ^ 40 * 1040477 * 2
def baseEnd_1040477 : Nat := 474902054176205211246613

theorem tailTrace_1040477 : CollatzResearch.WordTrace tailWord_1040477 prefixEnd_1040477 474902054176205211246613 := by
  unfold tailWord_1040477
  simp only [CollatzResearch.WordTrace]
  refine ⟨37949313851537003169343685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25299542567691335446229123 37949313851537003169343685)
  ·
    refine ⟨7115496347163188094251941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37949313851537003169343685 7115496347163188094251941)
    ·
      refine ⟨1334155565093097767672239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7115496347163188094251941 1334155565093097767672239)
      ·
        refine ⟨2001233347639646651508359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334155565093097767672239 2001233347639646651508359)
        ·
          refine ⟨3001850021459469977262539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001233347639646651508359 3001850021459469977262539)
          ·
            refine ⟨4502775032189204965893809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3001850021459469977262539 4502775032189204965893809)
            ·
              refine ⟨3377081274141903724420357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4502775032189204965893809 3377081274141903724420357)
              ·
                refine ⟨633202738901606948328817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3377081274141903724420357 633202738901606948328817)
                ·
                  refine ⟨474902054176205211246613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633202738901606948328817 474902054176205211246613)
                  ·
                    rfl

theorem cell20_1040477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_1040477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040477 prefixEnd_1040477 := by exact prefixLift 1040477
  have htrace : WordTrace (prefixWord ++ tailWord_1040477) baseStart_1040477 baseEnd_1040477 := by
    simpa [prefixWord, tailWord_1040477, baseEnd_1040477] using wordTrace_append hprefix tailTrace_1040477
  have hstable : (prefixWord ++ tailWord_1040477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040477).length < 2 ^ (prefixWord ++ tailWord_1040477).sum := by decide
  have hdescent : baseEnd_1040477 < baseStart_1040477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040505 : List Nat := [1, 2, 1, 3, 4, 3, 2, 4]
def baseStart_1040505 : Nat := 118140960795 + 1040505 * 2 ^ 59
def prefixEnd_1040505 : Nat := 4983230072969 + 3 ^ 40 * 1040505 * 2
def baseEnd_1040505 : Nat := 158304944713053852771055

theorem tailTrace_1040505 : CollatzResearch.WordTrace tailWord_1040505 prefixEnd_1040505 158304944713053852771055 := by
  unfold tailWord_1040505
  simp only [CollatzResearch.WordTrace]
  refine ⟨37950335095435563951362969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25300223396957042634241979 37950335095435563951362969)
  ·
    refine ⟨28462751321576672963522227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37950335095435563951362969 28462751321576672963522227)
    ·
      refine ⟨42694126982365009445283341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28462751321576672963522227 42694126982365009445283341)
      ·
        refine ⟨16010297618386878541981253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42694126982365009445283341 16010297618386878541981253)
        ·
          refine ⟨3001930803447539726621485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16010297618386878541981253 3001930803447539726621485)
          ·
            refine ⟨1125724051292827397483057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3001930803447539726621485 1125724051292827397483057)
            ·
              refine ⟨844293038469620548112293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125724051292827397483057 844293038469620548112293)
              ·
                refine ⟨158304944713053852771055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844293038469620548112293 158304944713053852771055)
                ·
                  rfl

theorem cell20_1040505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_1040505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040505 prefixEnd_1040505 := by exact prefixLift 1040505
  have htrace : WordTrace (prefixWord ++ tailWord_1040505) baseStart_1040505 baseEnd_1040505 := by
    simpa [prefixWord, tailWord_1040505, baseEnd_1040505] using wordTrace_append hprefix tailTrace_1040505
  have hstable : (prefixWord ++ tailWord_1040505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040505).length < 2 ^ (prefixWord ++ tailWord_1040505).sum := by decide
  have hdescent : baseEnd_1040505 < baseStart_1040505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040532 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 4]
def baseStart_1040532 : Nat := 118140960795 + 1040532 * 2 ^ 59
def prefixEnd_1040532 : Nat := 4983230072969 + 3 ^ 40 * 1040532 * 2
def baseEnd_1040532 : Nat := 474927157674869464413055

theorem tailTrace_1040532 : CollatzResearch.WordTrace tailWord_1040532 prefixEnd_1040532 474927157674869464413055 := by
  unfold tailWord_1040532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18975659933168873781297925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25300879910891831708397233 18975659933168873781297925)
  ·
    refine ⟨3557936237469163833993361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18975659933168873781297925 3557936237469163833993361)
    ·
      refine ⟨2668452178101872875495021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3557936237469163833993361 2668452178101872875495021)
      ·
        refine ⟨1000669566788202328310633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2668452178101872875495021 1000669566788202328310633)
        ·
          refine ⟨750502175091151746232975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1000669566788202328310633 750502175091151746232975)
          ·
            refine ⟨1125753262636727619349463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750502175091151746232975 1125753262636727619349463)
            ·
              refine ⟨1688629893955091429024195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125753262636727619349463 1688629893955091429024195)
              ·
                refine ⟨2532944840932637143536293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688629893955091429024195 2532944840932637143536293)
                ·
                  refine ⟨474927157674869464413055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532944840932637143536293 474927157674869464413055)
                  ·
                    rfl

theorem cell20_1040532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_1040532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040532 prefixEnd_1040532 := by exact prefixLift 1040532
  have htrace : WordTrace (prefixWord ++ tailWord_1040532) baseStart_1040532 baseEnd_1040532 := by
    simpa [prefixWord, tailWord_1040532, baseEnd_1040532] using wordTrace_append hprefix tailTrace_1040532
  have hstable : (prefixWord ++ tailWord_1040532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040532).length < 2 ^ (prefixWord ++ tailWord_1040532).sum := by decide
  have hdescent : baseEnd_1040532 < baseStart_1040532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040533 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 3]
def baseStart_1040533 : Nat := 118140960795 + 1040533 * 2 ^ 59
def prefixEnd_1040533 : Nat := 4983230072969 + 3 ^ 40 * 1040533 * 2
def baseEnd_1040533 : Nat := 474927614102117905379717

theorem tailTrace_1040533 : CollatzResearch.WordTrace tailWord_1040533 prefixEnd_1040533 474927614102117905379717 := by
  unfold tailWord_1040533
  simp only [CollatzResearch.WordTrace]
  refine ⟨37951356339334124733382253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25300904226222749822254835 37951356339334124733382253)
  ·
    refine ⟨14231758627250296775018345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37951356339334124733382253 14231758627250296775018345)
    ·
      refine ⟨10673818970437722581263759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14231758627250296775018345 10673818970437722581263759)
      ·
        refine ⟨16010728455656583871895639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10673818970437722581263759 16010728455656583871895639)
        ·
          refine ⟨24016092683484875807843459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16010728455656583871895639 24016092683484875807843459)
          ·
            refine ⟨36024139025227313711765189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24016092683484875807843459 36024139025227313711765189)
            ·
              refine ⟨6754526067230121320955973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36024139025227313711765189 6754526067230121320955973)
              ·
                refine ⟨1266473637605647747679245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6754526067230121320955973 1266473637605647747679245)
                ·
                  refine ⟨474927614102117905379717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266473637605647747679245 474927614102117905379717)
                  ·
                    rfl

theorem cell20_1040533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_1040533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040533 prefixEnd_1040533 := by exact prefixLift 1040533
  have htrace : WordTrace (prefixWord ++ tailWord_1040533) baseStart_1040533 baseEnd_1040533 := by
    simpa [prefixWord, tailWord_1040533, baseEnd_1040533] using wordTrace_append hprefix tailTrace_1040533
  have hstable : (prefixWord ++ tailWord_1040533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040533).length < 2 ^ (prefixWord ++ tailWord_1040533).sum := by decide
  have hdescent : baseEnd_1040533 < baseStart_1040533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040536 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_1040536 : Nat := 118140960795 + 1040536 * 2 ^ 59
def prefixEnd_1040536 : Nat := 4983230072969 + 3 ^ 40 * 1040536 * 2
def baseEnd_1040536 : Nat := 474928983383863228279705

theorem tailTrace_1040536 : CollatzResearch.WordTrace tailWord_1040536 prefixEnd_1040536 474928983383863228279705 := by
  unfold tailWord_1040536
  simp only [CollatzResearch.WordTrace]
  refine ⟨18975732879161628122870731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25300977172215504163827641 18975732879161628122870731)
  ·
    refine ⟨28463599318742442184306097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18975732879161628122870731 28463599318742442184306097)
    ·
      refine ⟨21347699489056831638229573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28463599318742442184306097 21347699489056831638229573)
      ·
        refine ⟨4002693654198155932168045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21347699489056831638229573 4002693654198155932168045)
        ·
          refine ⟨1501010120324308474563017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4002693654198155932168045 1501010120324308474563017)
          ·
            refine ⟨1125757590243231355922263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1501010120324308474563017 1125757590243231355922263)
            ·
              refine ⟨1688636385364847033883395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125757590243231355922263 1688636385364847033883395)
              ·
                refine ⟨2532954578047270550825093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688636385364847033883395 2532954578047270550825093)
                ·
                  refine ⟨474928983383863228279705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2532954578047270550825093 474928983383863228279705)
                  ·
                    rfl

theorem cell20_1040536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_1040536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040536 prefixEnd_1040536 := by exact prefixLift 1040536
  have htrace : WordTrace (prefixWord ++ tailWord_1040536) baseStart_1040536 baseEnd_1040536 := by
    simpa [prefixWord, tailWord_1040536, baseEnd_1040536] using wordTrace_append hprefix tailTrace_1040536
  have hstable : (prefixWord ++ tailWord_1040536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040536).length < 2 ^ (prefixWord ++ tailWord_1040536).sum := by decide
  have hdescent : baseEnd_1040536 < baseStart_1040536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040546 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1040546 : Nat := 118140960795 + 1040546 * 2 ^ 59
def prefixEnd_1040546 : Nat := 4983230072969 + 3 ^ 40 * 1040546 * 2
def baseEnd_1040546 : Nat := 474933547656347637946331

theorem tailTrace_1040546 : CollatzResearch.WordTrace tailWord_1040546 prefixEnd_1040546 474933547656347637946331 := by
  unfold tailWord_1040546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9487957622071756988401373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25301220325524685302403661 9487957622071756988401373)
  ·
    refine ⟨3557984108276908870650515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9487957622071756988401373 3557984108276908870650515)
    ·
      refine ⟨5336976162415363305975773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3557984108276908870650515 5336976162415363305975773)
      ·
        refine ⟨2001366060905761239740915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5336976162415363305975773 2001366060905761239740915)
        ·
          refine ⟨3002049091358641859611373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001366060905761239740915 3002049091358641859611373)
          ·
            refine ⟨1125768409259490697354265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3002049091358641859611373 1125768409259490697354265)
            ·
              refine ⟨844326306944618023015699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1125768409259490697354265 844326306944618023015699)
              ·
                refine ⟨1266489460416927034523549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844326306944618023015699 1266489460416927034523549)
                ·
                  refine ⟨474933547656347637946331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266489460416927034523549 474933547656347637946331)
                  ·
                    rfl

theorem cell20_1040546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1040546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040546 prefixEnd_1040546 := by exact prefixLift 1040546
  have htrace : WordTrace (prefixWord ++ tailWord_1040546) baseStart_1040546 baseEnd_1040546 := by
    simpa [prefixWord, tailWord_1040546, baseEnd_1040546] using wordTrace_append hprefix tailTrace_1040546
  have hstable : (prefixWord ++ tailWord_1040546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040546).length < 2 ^ (prefixWord ++ tailWord_1040546).sum := by decide
  have hdescent : baseEnd_1040546 < baseStart_1040546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040598 : List Nat := [5, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1040598 : Nat := 118140960795 + 1040598 * 2 ^ 59
def prefixEnd_1040598 : Nat := 4983230072969 + 3 ^ 40 * 1040598 * 2
def baseEnd_1040598 : Nat := 158319093957755522737595

theorem tailTrace_1040598 : CollatzResearch.WordTrace tailWord_1040598 prefixEnd_1040598 158319093957755522737595 := by
  unfold tailWord_1040598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2372107942756165052156153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25302484722732427222998965 2372107942756165052156153)
  ·
    refine ⟨1779080957067123789117115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2372107942756165052156153 1779080957067123789117115)
    ·
      refine ⟨2668621435600685683675673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1779080957067123789117115 2668621435600685683675673)
      ·
        refine ⟨2001466076700514262756755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668621435600685683675673 2001466076700514262756755)
        ·
          refine ⟨3002199115050771394135133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2001466076700514262756755 3002199115050771394135133)
          ·
            refine ⟨1125824668144039272800675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3002199115050771394135133 1125824668144039272800675)
            ·
              refine ⟨1688737002216058909201013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125824668144039272800675 1688737002216058909201013)
              ·
                refine ⟨158319093957755522737595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1688737002216058909201013 158319093957755522737595)
                ·
                  rfl

theorem cell20_1040598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1040598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040598 prefixEnd_1040598 := by exact prefixLift 1040598
  have htrace : WordTrace (prefixWord ++ tailWord_1040598) baseStart_1040598 baseEnd_1040598 := by
    simpa [prefixWord, tailWord_1040598, baseEnd_1040598] using wordTrace_append hprefix tailTrace_1040598
  have hstable : (prefixWord ++ tailWord_1040598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040598).length < 2 ^ (prefixWord ++ tailWord_1040598).sum := by decide
  have hdescent : baseEnd_1040598 < baseStart_1040598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040609 : List Nat := [1, 2, 3, 1, 3, 1, 1, 5, 3]
def baseStart_1040609 : Nat := 118140960795 + 1040609 * 2 ^ 59
def prefixEnd_1040609 : Nat := 4983230072969 + 3 ^ 40 * 1040609 * 2
def baseEnd_1040609 : Nat := 474962302572999418846073

theorem tailTrace_1040609 : CollatzResearch.WordTrace tailWord_1040609 prefixEnd_1040609 474962302572999418846073 := by
  unfold tailWord_1040609
  simp only [CollatzResearch.WordTrace]
  refine ⟨37954128287058789713148881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25302752191372526475432587 37954128287058789713148881)
  ·
    refine ⟨28465596215294092284861661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37954128287058789713148881 28465596215294092284861661)
    ·
      refine ⟨10674598580735284606823123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28465596215294092284861661 10674598580735284606823123)
      ·
        refine ⟨16011897871102926910234685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10674598580735284606823123 16011897871102926910234685)
        ·
          refine ⟨6004461701663597591338007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16011897871102926910234685 6004461701663597591338007)
          ·
            refine ⟨9006692552495396387007011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6004461701663597591338007 9006692552495396387007011)
            ·
              refine ⟨13510038828743094580510517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9006692552495396387007011 13510038828743094580510517)
              ·
                refine ⟨1266566140194665116922861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13510038828743094580510517 1266566140194665116922861)
                ·
                  refine ⟨474962302572999418846073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266566140194665116922861 474962302572999418846073)
                  ·
                    rfl

theorem cell20_1040609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_1040609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040609 prefixEnd_1040609 := by exact prefixLift 1040609
  have htrace : WordTrace (prefixWord ++ tailWord_1040609) baseStart_1040609 baseEnd_1040609 := by
    simpa [prefixWord, tailWord_1040609, baseEnd_1040609] using wordTrace_append hprefix tailTrace_1040609
  have hstable : (prefixWord ++ tailWord_1040609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040609).length < 2 ^ (prefixWord ++ tailWord_1040609).sum := by decide
  have hdescent : baseEnd_1040609 < baseStart_1040609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040616 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_1040616 : Nat := 118140960795 + 1040616 * 2 ^ 59
def prefixEnd_1040616 : Nat := 4983230072969 + 3 ^ 40 * 1040616 * 2
def baseEnd_1040616 : Nat := 474965497563738505612711

theorem tailTrace_1040616 : CollatzResearch.WordTrace tailWord_1040616 prefixEnd_1040616 474965497563738505612711 := by
  unfold tailWord_1040616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18977191799016714954326851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25302922398688953272435801 18977191799016714954326851)
  ·
    refine ⟨28465787698525072431490277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18977191799016714954326851 28465787698525072431490277)
    ·
      refine ⟨5337335193473451080904427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28465787698525072431490277 5337335193473451080904427)
      ·
        refine ⟨8006002790210176621356641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5337335193473451080904427 8006002790210176621356641)
        ·
          refine ⟨6004502092657632466017481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8006002790210176621356641 6004502092657632466017481)
          ·
            refine ⟨4503376569493224349513111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6004502092657632466017481 4503376569493224349513111)
            ·
              refine ⟨6755064854239836524269667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4503376569493224349513111 6755064854239836524269667)
              ·
                refine ⟨10132597281359754786404501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6755064854239836524269667 10132597281359754786404501)
                ·
                  refine ⟨474965497563738505612711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10132597281359754786404501 474965497563738505612711)
                  ·
                    rfl

theorem cell20_1040616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_1040616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040616 prefixEnd_1040616 := by exact prefixLift 1040616
  have htrace : WordTrace (prefixWord ++ tailWord_1040616) baseStart_1040616 baseEnd_1040616 := by
    simpa [prefixWord, tailWord_1040616, baseEnd_1040616] using wordTrace_append hprefix tailTrace_1040616
  have hstable : (prefixWord ++ tailWord_1040616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040616).length < 2 ^ (prefixWord ++ tailWord_1040616).sum := by decide
  have hdescent : baseEnd_1040616 < baseStart_1040616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040664 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_1040664 : Nat := 118140960795 + 1040664 * 2 ^ 59
def prefixEnd_1040664 : Nat := 4983230072969 + 3 ^ 40 * 1040664 * 2
def baseEnd_1040664 : Nat := 474987406071663672012515

theorem tailTrace_1040664 : CollatzResearch.WordTrace tailWord_1040664 prefixEnd_1040664 474987406071663672012515 := by
  unfold tailWord_1040664
  simp only [CollatzResearch.WordTrace]
  refine ⟨18978067150929767053200523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25304089534573022737600697 18978067150929767053200523)
  ·
    refine ⟨28467100726394650579800785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18978067150929767053200523 28467100726394650579800785)
    ·
      refine ⟨21350325544795987934850589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28467100726394650579800785 21350325544795987934850589)
      ·
        refine ⟨8006372079298495475568971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21350325544795987934850589 8006372079298495475568971)
        ·
          refine ⟨12009558118947743213353457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8006372079298495475568971 12009558118947743213353457)
          ·
            refine ⟨9007168589210807410015093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12009558118947743213353457 9007168589210807410015093)
            ·
              refine ⟨844422055238513194688915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9007168589210807410015093 844422055238513194688915)
              ·
                refine ⟨1266633082857769792033373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 844422055238513194688915 1266633082857769792033373)
                ·
                  refine ⟨474987406071663672012515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1266633082857769792033373 474987406071663672012515)
                  ·
                    rfl

theorem cell20_1040664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_1040664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040664 prefixEnd_1040664 := by exact prefixLift 1040664
  have htrace : WordTrace (prefixWord ++ tailWord_1040664) baseStart_1040664 baseEnd_1040664 := by
    simpa [prefixWord, tailWord_1040664, baseEnd_1040664] using wordTrace_append hprefix tailTrace_1040664
  have hstable : (prefixWord ++ tailWord_1040664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040664).length < 2 ^ (prefixWord ++ tailWord_1040664).sum := by decide
  have hdescent : baseEnd_1040664 < baseStart_1040664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040705 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 4]
def baseStart_1040705 : Nat := 118140960795 + 1040705 * 2 ^ 59
def prefixEnd_1040705 : Nat := 4983230072969 + 3 ^ 40 * 1040705 * 2
def baseEnd_1040705 : Nat := 475006119588849751645681

theorem tailTrace_1040705 : CollatzResearch.WordTrace tailWord_1040705 prefixEnd_1040705 475006119588849751645681 := by
  unfold tailWord_1040705
  simp only [CollatzResearch.WordTrace]
  refine ⟨37957629694710998108643569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25305086463140665405762379 37957629694710998108643569)
  ·
    refine ⟨28468222271033248581482677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37957629694710998108643569 28468222271033248581482677)
    ·
      refine ⟨2668895837909367054514001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28468222271033248581482677 2668895837909367054514001)
      ·
        refine ⟨2001671878432025290885501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2668895837909367054514001 2001671878432025290885501)
        ·
          refine ⟨750626954412009484082063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2001671878432025290885501 750626954412009484082063)
          ·
            refine ⟨1125940431618014226123095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750626954412009484082063 1125940431618014226123095)
            ·
              refine ⟨1688910647427021339184643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1125940431618014226123095 1688910647427021339184643)
              ·
                refine ⟨2533365971140532008776965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1688910647427021339184643 2533365971140532008776965)
                ·
                  refine ⟨475006119588849751645681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2533365971140532008776965 475006119588849751645681)
                  ·
                    rfl

theorem cell20_1040705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_1040705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040705 prefixEnd_1040705 := by exact prefixLift 1040705
  have htrace : WordTrace (prefixWord ++ tailWord_1040705) baseStart_1040705 baseEnd_1040705 := by
    simpa [prefixWord, tailWord_1040705, baseEnd_1040705] using wordTrace_append hprefix tailTrace_1040705
  have hstable : (prefixWord ++ tailWord_1040705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040705).length < 2 ^ (prefixWord ++ tailWord_1040705).sum := by decide
  have hdescent : baseEnd_1040705 < baseStart_1040705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040751 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_1040751 : Nat := 118140960795 + 1040751 * 2 ^ 59
def prefixEnd_1040751 : Nat := 4983230072969 + 3 ^ 40 * 1040751 * 2
def baseEnd_1040751 : Nat := 475027115242278036112159

theorem tailTrace_1040751 : CollatzResearch.WordTrace tailWord_1040751 prefixEnd_1040751 475027115242278036112159 := by
  unfold tailWord_1040751
  simp only [CollatzResearch.WordTrace]
  refine ⟨37959307452544347964818107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25306204968362898643212071 37959307452544347964818107)
  ·
    refine ⟨56938961178816521947227161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37959307452544347964818107 56938961178816521947227161)
    ·
      refine ⟨42704220884112391460420371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56938961178816521947227161 42704220884112391460420371)
      ·
        refine ⟨64056331326168587190630557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42704220884112391460420371 64056331326168587190630557)
        ·
          refine ⟨24021124247313220196486459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64056331326168587190630557 24021124247313220196486459)
          ·
            refine ⟨36031686370969830294729689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24021124247313220196486459 36031686370969830294729689)
            ·
              refine ⟨27023764778227372721047267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36031686370969830294729689 27023764778227372721047267)
              ·
                refine ⟨40535647167341059081570901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27023764778227372721047267 40535647167341059081570901)
                ·
                  refine ⟨475027115242278036112159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40535647167341059081570901 475027115242278036112159)
                  ·
                    rfl

theorem cell20_1040751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_1040751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040751 prefixEnd_1040751 := by exact prefixLift 1040751
  have htrace : WordTrace (prefixWord ++ tailWord_1040751) baseStart_1040751 baseEnd_1040751 := by
    simpa [prefixWord, tailWord_1040751, baseEnd_1040751] using wordTrace_append hprefix tailTrace_1040751
  have hstable : (prefixWord ++ tailWord_1040751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040751).length < 2 ^ (prefixWord ++ tailWord_1040751).sum := by decide
  have hdescent : baseEnd_1040751 < baseStart_1040751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040771 : List Nat := [1, 1, 1, 3, 7, 1, 1, 5]
def baseStart_1040771 : Nat := 118140960795 + 1040771 * 2 ^ 59
def prefixEnd_1040771 : Nat := 4983230072969 + 3 ^ 40 * 1040771 * 2
def baseEnd_1040771 : Nat := 158345414595748951815137

theorem tailTrace_1040771 : CollatzResearch.WordTrace tailWord_1040771 prefixEnd_1040771 158345414595748951815137 := by
  unfold tailWord_1040771
  simp only [CollatzResearch.WordTrace]
  refine ⟨37960036912471891380546167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25306691274981260920364111 37960036912471891380546167)
  ·
    refine ⟨56940055368707837070819251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37960036912471891380546167 56940055368707837070819251)
    ·
      refine ⟨85410083053061755606228877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56940055368707837070819251 85410083053061755606228877)
      ·
        refine ⟨32028781144898158352335829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85410083053061755606228877 32028781144898158352335829)
        ·
          refine ⟨750674558083550586382871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32028781144898158352335829 750674558083550586382871)
          ·
            refine ⟨1126011837125325879574307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750674558083550586382871 1126011837125325879574307)
            ·
              refine ⟨1689017755687988819361461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126011837125325879574307 1689017755687988819361461)
              ·
                refine ⟨158345414595748951815137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1689017755687988819361461 158345414595748951815137)
                ·
                  rfl

theorem cell20_1040771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 5].length) (baseStart_1040771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040771 prefixEnd_1040771 := by exact prefixLift 1040771
  have htrace : WordTrace (prefixWord ++ tailWord_1040771) baseStart_1040771 baseEnd_1040771 := by
    simpa [prefixWord, tailWord_1040771, baseEnd_1040771] using wordTrace_append hprefix tailTrace_1040771
  have hstable : (prefixWord ++ tailWord_1040771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040771).length < 2 ^ (prefixWord ++ tailWord_1040771).sum := by decide
  have hdescent : baseEnd_1040771 < baseStart_1040771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040802 : List Nat := [3, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_1040802 : Nat := 118140960795 + 1040802 * 2 ^ 59
def prefixEnd_1040802 : Nat := 4983230072969 + 3 ^ 40 * 1040802 * 2
def baseEnd_1040802 : Nat := 475050393031948525411951

theorem tailTrace_1040802 : CollatzResearch.WordTrace tailWord_1040802 prefixEnd_1040802 475050393031948525411951 := by
  unfold tailWord_1040802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490291893839895918731165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25307445050239722449949773 9490291893839895918731165)
  ·
    refine ⟨3558859460189960969524187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9490291893839895918731165 3558859460189960969524187)
    ·
      refine ⟨5338289190284941454286281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3558859460189960969524187 5338289190284941454286281)
      ·
        refine ⟨4003716892713706090714711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5338289190284941454286281 4003716892713706090714711)
        ·
          refine ⟨6005575339070559136072067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4003716892713706090714711 6005575339070559136072067)
          ·
            refine ⟨9008363008605838704108101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6005575339070559136072067 9008363008605838704108101)
            ·
              refine ⟨1689068064113594757020269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9008363008605838704108101 1689068064113594757020269)
              ·
                refine ⟨633400524042598033882601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1689068064113594757020269 633400524042598033882601)
                ·
                  refine ⟨475050393031948525411951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633400524042598033882601 475050393031948525411951)
                  ·
                    rfl

theorem cell20_1040802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_1040802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040802 prefixEnd_1040802 := by exact prefixLift 1040802
  have htrace : WordTrace (prefixWord ++ tailWord_1040802) baseStart_1040802 baseEnd_1040802 := by
    simpa [prefixWord, tailWord_1040802, baseEnd_1040802] using wordTrace_append hprefix tailTrace_1040802
  have hstable : (prefixWord ++ tailWord_1040802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040802).length < 2 ^ (prefixWord ++ tailWord_1040802).sum := by decide
  have hdescent : baseEnd_1040802 < baseStart_1040802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040823 : List Nat := [1, 1, 3, 1, 3, 3, 2, 4, 2]
def baseStart_1040823 : Nat := 118140960795 + 1040823 * 2 ^ 59
def prefixEnd_1040823 : Nat := 4983230072969 + 3 ^ 40 * 1040823 * 2
def baseEnd_1040823 : Nat := 475059978004165785711865

theorem tailTrace_1040823 : CollatzResearch.WordTrace tailWord_1040823 prefixEnd_1040823 475059978004165785711865 := by
  unfold tailWord_1040823
  simp only [CollatzResearch.WordTrace]
  refine ⟨37961933508283504261439123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25307955672189002840959415 37961933508283504261439123)
  ·
    refine ⟨56942900262425256392158685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37961933508283504261439123 56942900262425256392158685)
    ·
      refine ⟨21353587598409471147059507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56942900262425256392158685 21353587598409471147059507)
      ·
        refine ⟨32030381397614206720589261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21353587598409471147059507 32030381397614206720589261)
        ·
          refine ⟨12011393024105327520220973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32030381397614206720589261 12011393024105327520220973)
          ·
            refine ⟨4504272384039497820082865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12011393024105327520220973 4504272384039497820082865)
            ·
              refine ⟨3378204288029623365062149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4504272384039497820082865 3378204288029623365062149)
              ·
                refine ⟨633413304005554380949153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3378204288029623365062149 633413304005554380949153)
                ·
                  refine ⟨475059978004165785711865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633413304005554380949153 475059978004165785711865)
                  ·
                    rfl

theorem cell20_1040823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 4, 2].length) (baseStart_1040823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040823 prefixEnd_1040823 := by exact prefixLift 1040823
  have htrace : WordTrace (prefixWord ++ tailWord_1040823) baseStart_1040823 baseEnd_1040823 := by
    simpa [prefixWord, tailWord_1040823, baseEnd_1040823] using wordTrace_append hprefix tailTrace_1040823
  have hstable : (prefixWord ++ tailWord_1040823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040823).length < 2 ^ (prefixWord ++ tailWord_1040823).sum := by decide
  have hdescent : baseEnd_1040823 < baseStart_1040823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040858 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1040858 : Nat := 118140960795 + 1040858 * 2 ^ 59
def prefixEnd_1040858 : Nat := 4983230072969 + 3 ^ 40 * 1040858 * 2
def baseEnd_1040858 : Nat := 475075952957861219545055

theorem tailTrace_1040858 : CollatzResearch.WordTrace tailWord_1040858 prefixEnd_1040858 475075952957861219545055 := by
  unfold tailWord_1040858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9490802515789176309740807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25308806708771136825975485 9490802515789176309740807)
  ·
    refine ⟨14236203773683764464611211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9490802515789176309740807 14236203773683764464611211)
    ·
      refine ⟨21354305660525646696916817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14236203773683764464611211 21354305660525646696916817)
      ·
        refine ⟨16015729245394235022687613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21354305660525646696916817 16015729245394235022687613)
        ·
          refine ⟨6005898467022838133507855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16015729245394235022687613 6005898467022838133507855)
          ·
            refine ⟨9008847700534257200261783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6005898467022838133507855 9008847700534257200261783)
            ·
              refine ⟨13513271550801385800392675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9008847700534257200261783 13513271550801385800392675)
              ·
                refine ⟨20269907326202078700589013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13513271550801385800392675 20269907326202078700589013)
                ·
                  refine ⟨475075952957861219545055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20269907326202078700589013 475075952957861219545055)
                  ·
                    rfl

theorem cell20_1040858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1040858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040858 prefixEnd_1040858 := by exact prefixLift 1040858
  have htrace : WordTrace (prefixWord ++ tailWord_1040858) baseStart_1040858 baseEnd_1040858 := by
    simpa [prefixWord, tailWord_1040858, baseEnd_1040858] using wordTrace_append hprefix tailTrace_1040858
  have hstable : (prefixWord ++ tailWord_1040858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040858).length < 2 ^ (prefixWord ++ tailWord_1040858).sum := by decide
  have hdescent : baseEnd_1040858 < baseStart_1040858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040885 : List Nat := [1, 3, 5, 1, 2, 1, 2, 5]
def baseStart_1040885 : Nat := 118140960795 + 1040885 * 2 ^ 59
def prefixEnd_1040885 : Nat := 4983230072969 + 3 ^ 40 * 1040885 * 2
def baseEnd_1040885 : Nat := 158362758831189708548315

theorem tailTrace_1040885 : CollatzResearch.WordTrace tailWord_1040885 prefixEnd_1040885 158362758831189708548315 := by
  unfold tailWord_1040885
  simp only [CollatzResearch.WordTrace]
  refine ⟨37964194834058888850196109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25309463222705925900130739 37964194834058888850196109)
  ·
    refine ⟨14236573062772083318823541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37964194834058888850196109 14236573062772083318823541)
    ·
      refine ⟨1334678724634882811139707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14236573062772083318823541 1334678724634882811139707)
      ·
        refine ⟨2002018086952324216709561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334678724634882811139707 2002018086952324216709561)
        ·
          refine ⟨1501513565214243162532171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002018086952324216709561 1501513565214243162532171)
          ·
            refine ⟨2252270347821364743798257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501513565214243162532171 2252270347821364743798257)
            ·
              refine ⟨1689202760866023557848693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2252270347821364743798257 1689202760866023557848693)
              ·
                refine ⟨158362758831189708548315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1689202760866023557848693 158362758831189708548315)
                ·
                  rfl

theorem cell20_1040885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_1040885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040885 prefixEnd_1040885 := by exact prefixLift 1040885
  have htrace : WordTrace (prefixWord ++ tailWord_1040885) baseStart_1040885 baseEnd_1040885 := by
    simpa [prefixWord, tailWord_1040885, baseEnd_1040885] using wordTrace_append hprefix tailTrace_1040885
  have hstable : (prefixWord ++ tailWord_1040885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040885).length < 2 ^ (prefixWord ++ tailWord_1040885).sum := by decide
  have hdescent : baseEnd_1040885 < baseStart_1040885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040902 : List Nat := [6, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1040902 : Nat := 118140960795 + 1040902 * 2 ^ 59
def prefixEnd_1040902 : Nat := 4983230072969 + 3 ^ 40 * 1040902 * 2
def baseEnd_1040902 : Nat := 158365345252264207359403

theorem tailTrace_1040902 : CollatzResearch.WordTrace tailWord_1040902 prefixEnd_1040902 158365345252264207359403 := by
  unfold tailWord_1040902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186400464843665648548905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25309876583331533835709973 1186400464843665648548905)
  ·
    refine ⟨889800348632749236411679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1186400464843665648548905 889800348632749236411679)
    ·
      refine ⟨1334700522949123854617519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 889800348632749236411679 1334700522949123854617519)
      ·
        refine ⟨2002050784423685781926279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1334700522949123854617519 2002050784423685781926279)
        ·
          refine ⟨3003076176635528672889419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002050784423685781926279 3003076176635528672889419)
          ·
            refine ⟨4504614264953293009334129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003076176635528672889419 4504614264953293009334129)
            ·
              refine ⟨3378460698714969757000597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4504614264953293009334129 3378460698714969757000597)
              ·
                refine ⟨158365345252264207359403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3378460698714969757000597 158365345252264207359403)
                ·
                  rfl

theorem cell20_1040902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1040902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040902 prefixEnd_1040902 := by exact prefixLift 1040902
  have htrace : WordTrace (prefixWord ++ tailWord_1040902) baseStart_1040902 baseEnd_1040902 := by
    simpa [prefixWord, tailWord_1040902, baseEnd_1040902] using wordTrace_append hprefix tailTrace_1040902
  have hstable : (prefixWord ++ tailWord_1040902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040902).length < 2 ^ (prefixWord ++ tailWord_1040902).sum := by decide
  have hdescent : baseEnd_1040902 < baseStart_1040902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040972 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1040972 : Nat := 118140960795 + 1040972 * 2 ^ 59
def prefixEnd_1040972 : Nat := 4983230072969 + 3 ^ 40 * 1040972 * 2
def baseEnd_1040972 : Nat := 475127985664183489744589

theorem tailTrace_1040972 : CollatzResearch.WordTrace tailWord_1040972 prefixEnd_1040972 475127985664183489744589 := by
  unfold tailWord_1040972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18983683992371851354306585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25311578656495801805742113 18983683992371851354306585)
  ·
    refine ⟨14237762994278888515729939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18983683992371851354306585 14237762994278888515729939)
    ·
      refine ⟨21356644491418332773594909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14237762994278888515729939 21356644491418332773594909)
      ·
        refine ⟨8008741684281874790098091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21356644491418332773594909 8008741684281874790098091)
        ·
          refine ⟨12013112526422812185147137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8008741684281874790098091 12013112526422812185147137)
          ·
            refine ⟨9009834394817109138860353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12013112526422812185147137 9009834394817109138860353)
            ·
              refine ⟨6757375796112831854145265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9009834394817109138860353 6757375796112831854145265)
              ·
                refine ⟨5068031847084623890608949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6757375796112831854145265 5068031847084623890608949)
                ·
                  refine ⟨475127985664183489744589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5068031847084623890608949 475127985664183489744589)
                  ·
                    rfl

theorem cell20_1040972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1040972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040972 prefixEnd_1040972 := by exact prefixLift 1040972
  have htrace : WordTrace (prefixWord ++ tailWord_1040972) baseStart_1040972 baseEnd_1040972 := by
    simpa [prefixWord, tailWord_1040972, baseEnd_1040972] using wordTrace_append hprefix tailTrace_1040972
  have hstable : (prefixWord ++ tailWord_1040972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040972).length < 2 ^ (prefixWord ++ tailWord_1040972).sum := by decide
  have hdescent : baseEnd_1040972 < baseStart_1040972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1040996 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1040996 : Nat := 118140960795 + 1040996 * 2 ^ 59
def prefixEnd_1040996 : Nat := 4983230072969 + 3 ^ 40 * 1040996 * 2
def baseEnd_1040996 : Nat := 475138939918146072944491

theorem tailTrace_1040996 : CollatzResearch.WordTrace tailWord_1040996 prefixEnd_1040996 475138939918146072944491 := by
  unfold tailWord_1040996
  simp only [CollatzResearch.WordTrace]
  refine ⟨18984121668328377403743421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25312162224437836538324561 18984121668328377403743421)
  ·
    refine ⟨7119045625623141526403783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18984121668328377403743421 7119045625623141526403783)
    ·
      refine ⟨10678568438434712289605675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119045625623141526403783 10678568438434712289605675)
      ·
        refine ⟨16017852657652068434408513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10678568438434712289605675 16017852657652068434408513)
        ·
          refine ⟨12013389493239051325806385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16017852657652068434408513 12013389493239051325806385)
          ·
            refine ⟨9010042119929288494354789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12013389493239051325806385 9010042119929288494354789)
            ·
              refine ⟨1689382897486741592691523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9010042119929288494354789 1689382897486741592691523)
              ·
                refine ⟨2534074346230112389037285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1689382897486741592691523 2534074346230112389037285)
                ·
                  refine ⟨475138939918146072944491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534074346230112389037285 475138939918146072944491)
                  ·
                    rfl

theorem cell20_1040996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1040996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1040996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1040996 prefixEnd_1040996 := by exact prefixLift 1040996
  have htrace : WordTrace (prefixWord ++ tailWord_1040996) baseStart_1040996 baseEnd_1040996 := by
    simpa [prefixWord, tailWord_1040996, baseEnd_1040996] using wordTrace_append hprefix tailTrace_1040996
  have hstable : (prefixWord ++ tailWord_1040996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1040996).length < 2 ^ (prefixWord ++ tailWord_1040996).sum := by decide
  have hdescent : baseEnd_1040996 < baseStart_1040996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1040996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041048 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_1041048 : Nat := 118140960795 + 1041048 * 2 ^ 59
def prefixEnd_1041048 : Nat := 4983230072969 + 3 ^ 40 * 1041048 * 2
def baseEnd_1041048 : Nat := 475162674135065003210945

theorem tailTrace_1041048 : CollatzResearch.WordTrace tailWord_1041048 prefixEnd_1041048 475162674135065003210945 := by
  unfold tailWord_1041048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18985069966234183844189899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25313426621645578458919865 18985069966234183844189899)
  ·
    refine ⟨28477604949351275766284849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18985069966234183844189899 28477604949351275766284849)
    ·
      refine ⟨21358203712013456824713637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28477604949351275766284849 21358203712013456824713637)
      ·
        refine ⟨4004663196002523154633807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21358203712013456824713637 4004663196002523154633807)
        ·
          refine ⟨6006994794003784731950711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4004663196002523154633807 6006994794003784731950711)
          ·
            refine ⟨9010492191005677097926067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6006994794003784731950711 9010492191005677097926067)
            ·
              refine ⟨13515738286508515646889101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9010492191005677097926067 13515738286508515646889101)
              ·
                refine ⟨5068401857440693367583413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13515738286508515646889101 5068401857440693367583413)
                ·
                  refine ⟨475162674135065003210945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5068401857440693367583413 475162674135065003210945)
                  ·
                    rfl

theorem cell20_1041048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_1041048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041048 prefixEnd_1041048 := by exact prefixLift 1041048
  have htrace : WordTrace (prefixWord ++ tailWord_1041048) baseStart_1041048 baseEnd_1041048 := by
    simpa [prefixWord, tailWord_1041048, baseEnd_1041048] using wordTrace_append hprefix tailTrace_1041048
  have hstable : (prefixWord ++ tailWord_1041048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041048).length < 2 ^ (prefixWord ++ tailWord_1041048).sum := by decide
  have hdescent : baseEnd_1041048 < baseStart_1041048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041106 : List Nat := [3, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_1041106 : Nat := 118140960795 + 1041106 * 2 ^ 59
def prefixEnd_1041106 : Nat := 4983230072969 + 3 ^ 40 * 1041106 * 2
def baseEnd_1041106 : Nat := 475189146915474579277375

theorem tailTrace_1041106 : CollatzResearch.WordTrace tailWord_1041106 prefixEnd_1041106 475189146915474579277375 := by
  unfold tailWord_1041106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493063841564560898497793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25314836910838829062660781 9493063841564560898497793)
  ·
    refine ⟨7119797881173420673873345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9493063841564560898497793 7119797881173420673873345)
    ·
      refine ⟨5339848410880065505405009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7119797881173420673873345 5339848410880065505405009)
      ·
        refine ⟨4004886308160049129053757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5339848410880065505405009 4004886308160049129053757)
        ·
          refine ⟨1501832365560018423395159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4004886308160049129053757 1501832365560018423395159)
          ·
            refine ⟨2252748548340027635092739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501832365560018423395159 2252748548340027635092739)
            ·
              refine ⟨3379122822510041452639109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2252748548340027635092739 3379122822510041452639109)
              ·
                refine ⟨633585529220632772369833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3379122822510041452639109 633585529220632772369833)
                ·
                  refine ⟨475189146915474579277375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633585529220632772369833 475189146915474579277375)
                  ·
                    rfl

theorem cell20_1041106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_1041106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041106 prefixEnd_1041106 := by exact prefixLift 1041106
  have htrace : WordTrace (prefixWord ++ tailWord_1041106) baseStart_1041106 baseEnd_1041106 := by
    simpa [prefixWord, tailWord_1041106, baseEnd_1041106] using wordTrace_append hprefix tailTrace_1041106
  have hstable : (prefixWord ++ tailWord_1041106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041106).length < 2 ^ (prefixWord ++ tailWord_1041106).sum := by decide
  have hdescent : baseEnd_1041106 < baseStart_1041106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041134 : List Nat := [4, 1, 2, 1, 1, 4, 3, 4]
def baseStart_1041134 : Nat := 118140960795 + 1041134 * 2 ^ 59
def prefixEnd_1041134 : Nat := 4983230072969 + 3 ^ 40 * 1041134 * 2
def baseEnd_1041134 : Nat := 158400642292810308781309

theorem tailTrace_1041134 : CollatzResearch.WordTrace tailWord_1041134 prefixEnd_1041134 158400642292810308781309 := by
  unfold tailWord_1041134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4746659576269600547001307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25315517740104536250673637 4746659576269600547001307)
  ·
    refine ⟨7119989364404400820501961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4746659576269600547001307 7119989364404400820501961)
    ·
      refine ⟨5339992023303300615376471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7119989364404400820501961 5339992023303300615376471)
      ·
        refine ⟨8009988034954950923064707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5339992023303300615376471 8009988034954950923064707)
        ·
          refine ⟨12014982052432426384597061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8009988034954950923064707 12014982052432426384597061)
          ·
            refine ⟨2252809134831079947111949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12014982052432426384597061 2252809134831079947111949)
            ·
              refine ⟨844803425561654980166981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2252809134831079947111949 844803425561654980166981)
              ·
                refine ⟨158400642292810308781309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844803425561654980166981 158400642292810308781309)
                ·
                  rfl

theorem cell20_1041134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_1041134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041134 prefixEnd_1041134 := by exact prefixLift 1041134
  have htrace : WordTrace (prefixWord ++ tailWord_1041134) baseStart_1041134 baseEnd_1041134 := by
    simpa [prefixWord, tailWord_1041134, baseEnd_1041134] using wordTrace_append hprefix tailTrace_1041134
  have hstable : (prefixWord ++ tailWord_1041134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041134).length < 2 ^ (prefixWord ++ tailWord_1041134).sum := by decide
  have hdescent : baseEnd_1041134 < baseStart_1041134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041140 : List Nat := [2, 6, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1041140 : Nat := 118140960795 + 1041140 * 2 ^ 59
def prefixEnd_1041140 : Nat := 4983230072969 + 3 ^ 40 * 1041140 * 2
def baseEnd_1041140 : Nat := 475204665441921572143903

theorem tailTrace_1041140 : CollatzResearch.WordTrace tailWord_1041140 prefixEnd_1041140 475204665441921572143903 := by
  unfold tailWord_1041140
  simp only [CollatzResearch.WordTrace]
  refine ⟨18986747724067533700364437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25315663632090044933819249 18986747724067533700364437)
  ·
    refine ⟨890003799565665642204583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18986747724067533700364437 890003799565665642204583)
    ·
      refine ⟨1335005699348498463306875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890003799565665642204583 1335005699348498463306875)
      ·
        refine ⟨2002508549022747694960313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335005699348498463306875 2002508549022747694960313)
        ·
          refine ⟨1501881411767060771220235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2002508549022747694960313 1501881411767060771220235)
          ·
            refine ⟨2252822117650591156830353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1501881411767060771220235 2252822117650591156830353)
            ·
              refine ⟨1689616588237943367622765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2252822117650591156830353 1689616588237943367622765)
              ·
                refine ⟨633606220589228762858537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1689616588237943367622765 633606220589228762858537)
                ·
                  refine ⟨475204665441921572143903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633606220589228762858537 475204665441921572143903)
                  ·
                    rfl

theorem cell20_1041140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1041140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041140 prefixEnd_1041140 := by exact prefixLift 1041140
  have htrace : WordTrace (prefixWord ++ tailWord_1041140) baseStart_1041140 baseEnd_1041140 := by
    simpa [prefixWord, tailWord_1041140, baseEnd_1041140] using wordTrace_append hprefix tailTrace_1041140
  have hstable : (prefixWord ++ tailWord_1041140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041140).length < 2 ^ (prefixWord ++ tailWord_1041140).sum := by decide
  have hdescent : baseEnd_1041140 < baseStart_1041140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041162 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_1041162 : Nat := 118140960795 + 1041162 * 2 ^ 59
def prefixEnd_1041162 : Nat := 4983230072969 + 3 ^ 40 * 1041162 * 2
def baseEnd_1041162 : Nat := 475214706841387273410479

theorem tailTrace_1041162 : CollatzResearch.WordTrace tailWord_1041162 prefixEnd_1041162 475214706841387273410479 := by
  unfold tailWord_1041162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493574463513841289507435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25316198569370243438686493 9493574463513841289507435)
  ·
    refine ⟨14240361695270761934261153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9493574463513841289507435 14240361695270761934261153)
    ·
      refine ⟨10680271271453071450695865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14240361695270761934261153 10680271271453071450695865)
      ·
        refine ⟨8010203453589803588021899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10680271271453071450695865 8010203453589803588021899)
        ·
          refine ⟨12015305180384705382032849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010203453589803588021899 12015305180384705382032849)
          ·
            refine ⟨9011478885288529036524637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12015305180384705382032849 9011478885288529036524637)
            ·
              refine ⟨3379304581983198388696739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9011478885288529036524637 3379304581983198388696739)
              ·
                refine ⟨5068956872974797583045109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3379304581983198388696739 5068956872974797583045109)
                ·
                  refine ⟨475214706841387273410479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5068956872974797583045109 475214706841387273410479)
                  ·
                    rfl

theorem cell20_1041162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_1041162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041162 prefixEnd_1041162 := by exact prefixLift 1041162
  have htrace : WordTrace (prefixWord ++ tailWord_1041162) baseStart_1041162 baseEnd_1041162 := by
    simpa [prefixWord, tailWord_1041162, baseEnd_1041162] using wordTrace_append hprefix tailTrace_1041162
  have hstable : (prefixWord ++ tailWord_1041162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041162).length < 2 ^ (prefixWord ++ tailWord_1041162).sum := by decide
  have hdescent : baseEnd_1041162 < baseStart_1041162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041169 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_1041169 : Nat := 118140960795 + 1041169 * 2 ^ 59
def prefixEnd_1041169 : Nat := 4983230072969 + 3 ^ 40 * 1041169 * 2
def baseEnd_1041169 : Nat := 475217901832126360177117

theorem tailTrace_1041169 : CollatzResearch.WordTrace tailWord_1041169 prefixEnd_1041169 475217901832126360177117 := by
  unfold tailWord_1041169
  simp only [CollatzResearch.WordTrace]
  refine ⟨37974553165030005353534561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25316368776686670235689707 37974553165030005353534561)
  ·
    refine ⟨28480914873772504015150921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37974553165030005353534561 28480914873772504015150921)
    ·
      refine ⟨21360686155329378011363191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28480914873772504015150921 21360686155329378011363191)
      ·
        refine ⟨32041029232994067017044787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21360686155329378011363191 32041029232994067017044787)
        ·
          refine ⟨48061543849491100525567181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32041029232994067017044787 48061543849491100525567181)
          ·
            refine ⟨18023078943559162697087693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48061543849491100525567181 18023078943559162697087693)
            ·
              refine ⟨6758654603834686011407885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18023078943559162697087693 6758654603834686011407885)
              ·
                refine ⟨2534495476438007254277957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6758654603834686011407885 2534495476438007254277957)
                ·
                  refine ⟨475217901832126360177117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534495476438007254277957 475217901832126360177117)
                  ·
                    rfl

theorem cell20_1041169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_1041169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041169 prefixEnd_1041169 := by exact prefixLift 1041169
  have htrace : WordTrace (prefixWord ++ tailWord_1041169) baseStart_1041169 baseEnd_1041169 := by
    simpa [prefixWord, tailWord_1041169, baseEnd_1041169] using wordTrace_append hprefix tailTrace_1041169
  have hstable : (prefixWord ++ tailWord_1041169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041169).length < 2 ^ (prefixWord ++ tailWord_1041169).sum := by decide
  have hdescent : baseEnd_1041169 < baseStart_1041169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041176 : List Nat := [2, 1, 2, 3, 1, 1, 1, 9]
def baseStart_1041176 : Nat := 118140960795 + 1041176 * 2 ^ 59
def prefixEnd_1041176 : Nat := 4983230072969 + 3 ^ 40 * 1041176 * 2
def baseEnd_1041176 : Nat := 158407032274288482314585

theorem tailTrace_1041176 : CollatzResearch.WordTrace tailWord_1041176 prefixEnd_1041176 158407032274288482314585 := by
  unfold tailWord_1041176
  simp only [CollatzResearch.WordTrace]
  refine ⟨18987404238002322774519691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25316538984003097032692921 18987404238002322774519691)
  ·
    refine ⟨28481106357003484161779537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18987404238002322774519691 28481106357003484161779537)
    ·
      refine ⟨21360829767752613121334653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28481106357003484161779537 21360829767752613121334653)
      ·
        refine ⟨8010311162907229920500495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21360829767752613121334653 8010311162907229920500495)
        ·
          refine ⟨12015466744360844880750743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010311162907229920500495 12015466744360844880750743)
          ·
            refine ⟨18023200116541267321126115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12015466744360844880750743 18023200116541267321126115)
            ·
              refine ⟨27034800174811900981689173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18023200116541267321126115 27034800174811900981689173)
              ·
                refine ⟨158407032274288482314585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27034800174811900981689173 158407032274288482314585)
                ·
                  rfl

theorem cell20_1041176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_1041176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041176 prefixEnd_1041176 := by exact prefixLift 1041176
  have htrace : WordTrace (prefixWord ++ tailWord_1041176) baseStart_1041176 baseEnd_1041176 := by
    simpa [prefixWord, tailWord_1041176, baseEnd_1041176] using wordTrace_append hprefix tailTrace_1041176
  have hstable : (prefixWord ++ tailWord_1041176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041176).length < 2 ^ (prefixWord ++ tailWord_1041176).sum := by decide
  have hdescent : baseEnd_1041176 < baseStart_1041176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041186 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_1041186 : Nat := 118140960795 + 1041186 * 2 ^ 59
def prefixEnd_1041186 : Nat := 4983230072969 + 3 ^ 40 * 1041186 * 2
def baseEnd_1041186 : Nat := 475225661095349856610381

theorem tailTrace_1041186 : CollatzResearch.WordTrace tailWord_1041186 prefixEnd_1041186 475225661095349856610381 := by
  unfold tailWord_1041186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9493793301492104314225853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25316782137312278171268941 9493793301492104314225853)
  ·
    refine ⟨3560172488059539117834695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9493793301492104314225853 3560172488059539117834695)
    ·
      refine ⟨5340258732089308676752043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3560172488059539117834695 5340258732089308676752043)
      ·
        refine ⟨8010388098133963015128065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340258732089308676752043 8010388098133963015128065)
        ·
          refine ⟨6007791073600472261346049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8010388098133963015128065 6007791073600472261346049)
          ·
            refine ⟨4505843305200354196009537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6007791073600472261346049 4505843305200354196009537)
            ·
              refine ⟨3379382478900265647007153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4505843305200354196009537 3379382478900265647007153)
              ·
                refine ⟨2534536859175199235255365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379382478900265647007153 2534536859175199235255365)
                ·
                  refine ⟨475225661095349856610381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534536859175199235255365 475225661095349856610381)
                  ·
                    rfl

theorem cell20_1041186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_1041186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041186 prefixEnd_1041186 := by exact prefixLift 1041186
  have htrace : WordTrace (prefixWord ++ tailWord_1041186) baseStart_1041186 baseEnd_1041186 := by
    simpa [prefixWord, tailWord_1041186, baseEnd_1041186] using wordTrace_append hprefix tailTrace_1041186
  have hstable : (prefixWord ++ tailWord_1041186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041186).length < 2 ^ (prefixWord ++ tailWord_1041186).sum := by decide
  have hdescent : baseEnd_1041186 < baseStart_1041186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041203 : List Nat := [1, 1, 1, 2, 6, 1, 3, 3, 2]
def baseStart_1041203 : Nat := 118140960795 + 1041203 * 2 ^ 59
def prefixEnd_1041203 : Nat := 4983230072969 + 3 ^ 40 * 1041203 * 2
def baseEnd_1041203 : Nat := 475233420358573353043645

theorem tailTrace_1041203 : CollatzResearch.WordTrace tailWord_1041203 prefixEnd_1041203 475233420358573353043645 := by
  unfold tailWord_1041203
  simp only [CollatzResearch.WordTrace]
  refine ⟨37975793246906829160272263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25317195497937886106848175 37975793246906829160272263)
  ·
    refine ⟨56963689870360243740408395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37975793246906829160272263 56963689870360243740408395)
    ·
      refine ⟨85445534805540365610612593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56963689870360243740408395 85445534805540365610612593)
      ·
        refine ⟨64084151104155274207959445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85445534805540365610612593 64084151104155274207959445)
        ·
          refine ⟨3003944583007278478498099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64084151104155274207959445 3003944583007278478498099)
          ·
            refine ⟨4505916874510917717747149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3003944583007278478498099 4505916874510917717747149)
            ·
              refine ⟨1689718827941594144155181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4505916874510917717747149 1689718827941594144155181)
              ·
                refine ⟨633644560478097804058193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1689718827941594144155181 633644560478097804058193)
                ·
                  refine ⟨475233420358573353043645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633644560478097804058193 475233420358573353043645)
                  ·
                    rfl

theorem cell20_1041203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 2].length) (baseStart_1041203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041203 prefixEnd_1041203 := by exact prefixLift 1041203
  have htrace : WordTrace (prefixWord ++ tailWord_1041203) baseStart_1041203 baseEnd_1041203 := by
    simpa [prefixWord, tailWord_1041203, baseEnd_1041203] using wordTrace_append hprefix tailTrace_1041203
  have hstable : (prefixWord ++ tailWord_1041203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041203).length < 2 ^ (prefixWord ++ tailWord_1041203).sum := by decide
  have hdescent : baseEnd_1041203 < baseStart_1041203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041210 : List Nat := [3, 1, 1, 1, 7, 1, 6]
def baseStart_1041210 : Nat := 118140960795 + 1041210 * 2 ^ 59
def prefixEnd_1041210 : Nat := 4983230072969 + 3 ^ 40 * 1041210 * 2
def baseEnd_1041210 : Nat := 52804068372145826645587

theorem tailTrace_1041210 : CollatzResearch.WordTrace tailWord_1041210 prefixEnd_1041210 52804068372145826645587 := by
  unfold tailWord_1041210
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494012139470367338944271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25317365705254312903851389 9494012139470367338944271)
  ·
    refine ⟨14241018209205551008416407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9494012139470367338944271 14241018209205551008416407)
    ·
      refine ⟨21361527313808326512624611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14241018209205551008416407 21361527313808326512624611)
      ·
        refine ⟨32042290970712489768936917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21361527313808326512624611 32042290970712489768936917)
        ·
          refine ⟨750991194626073978959459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 32042290970712489768936917 750991194626073978959459)
          ·
            refine ⟨1126486791939110968439189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 750991194626073978959459 1126486791939110968439189)
            ·
              refine ⟨52804068372145826645587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1126486791939110968439189 52804068372145826645587)
              ·
                rfl

theorem cell20_1041210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 6].length) (baseStart_1041210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041210 prefixEnd_1041210 := by exact prefixLift 1041210
  have htrace : WordTrace (prefixWord ++ tailWord_1041210) baseStart_1041210 baseEnd_1041210 := by
    simpa [prefixWord, tailWord_1041210, baseEnd_1041210] using wordTrace_append hprefix tailTrace_1041210
  have hstable : (prefixWord ++ tailWord_1041210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041210).length < 2 ^ (prefixWord ++ tailWord_1041210).sum := by decide
  have hdescent : baseEnd_1041210 < baseStart_1041210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041259 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_1041259 : Nat := 118140960795 + 1041259 * 2 ^ 59
def prefixEnd_1041259 : Nat := 4983230072969 + 3 ^ 40 * 1041259 * 2
def baseEnd_1041259 : Nat := 475258980284486047176749

theorem tailTrace_1041259 : CollatzResearch.WordTrace tailWord_1041259 prefixEnd_1041259 475258980284486047176749 := by
  unfold tailWord_1041259
  simp only [CollatzResearch.WordTrace]
  refine ⟨37977835734703950724310831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25318557156469300482873887 37977835734703950724310831)
  ·
    refine ⟨56966753602055926086466247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37977835734703950724310831 56966753602055926086466247)
    ·
      refine ⟨85450130403083889129699371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56966753602055926086466247 85450130403083889129699371)
      ·
        refine ⟨128175195604625833694549057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85450130403083889129699371 128175195604625833694549057)
        ·
          refine ⟨96131396703469375270911793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128175195604625833694549057 96131396703469375270911793)
          ·
            refine ⟨72098547527602031453183845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96131396703469375270911793 72098547527602031453183845)
            ·
              refine ⟨13518477661425380897471971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72098547527602031453183845 13518477661425380897471971)
              ·
                refine ⟨20277716492138071346207957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13518477661425380897471971 20277716492138071346207957)
                ·
                  refine ⟨475258980284486047176749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20277716492138071346207957 475258980284486047176749)
                  ·
                    rfl

theorem cell20_1041259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_1041259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041259 prefixEnd_1041259 := by exact prefixLift 1041259
  have htrace : WordTrace (prefixWord ++ tailWord_1041259) baseStart_1041259 baseEnd_1041259 := by
    simpa [prefixWord, tailWord_1041259, baseEnd_1041259] using wordTrace_append hprefix tailTrace_1041259
  have hstable : (prefixWord ++ tailWord_1041259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041259).length < 2 ^ (prefixWord ++ tailWord_1041259).sum := by decide
  have hdescent : baseEnd_1041259 < baseStart_1041259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041279 : List Nat := [1, 1, 2, 2, 1, 1, 8, 2, 2]
def baseStart_1041279 : Nat := 118140960795 + 1041279 * 2 ^ 59
def prefixEnd_1041279 : Nat := 4983230072969 + 3 ^ 40 * 1041279 * 2
def baseEnd_1041279 : Nat := 475268108829454866510001

theorem tailTrace_1041279 : CollatzResearch.WordTrace tailWord_1041279 prefixEnd_1041279 475268108829454866510001 := by
  unfold tailWord_1041279
  simp only [CollatzResearch.WordTrace]
  refine ⟨37978565194631494140038891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25319043463087662760025927 37978565194631494140038891)
  ·
    refine ⟨56967847791947241210058337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37978565194631494140038891 56967847791947241210058337)
    ·
      refine ⟨42725885843960430907543753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56967847791947241210058337 42725885843960430907543753)
      ·
        refine ⟨32044414382970323180657815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42725885843960430907543753 32044414382970323180657815)
        ·
          refine ⟨48066621574455484770986723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32044414382970323180657815 48066621574455484770986723)
          ·
            refine ⟨72099932361683227156480085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48066621574455484770986723 72099932361683227156480085)
            ·
              refine ⟨844921082363475318240001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 72099932361683227156480085 844921082363475318240001)
              ·
                refine ⟨633690811772606488680001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 844921082363475318240001 633690811772606488680001)
                ·
                  refine ⟨475268108829454866510001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633690811772606488680001 475268108829454866510001)
                  ·
                    rfl

theorem cell20_1041279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 2, 2].length) (baseStart_1041279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041279 prefixEnd_1041279 := by exact prefixLift 1041279
  have htrace : WordTrace (prefixWord ++ tailWord_1041279) baseStart_1041279 baseEnd_1041279 := by
    simpa [prefixWord, tailWord_1041279, baseEnd_1041279] using wordTrace_append hprefix tailTrace_1041279
  have hstable : (prefixWord ++ tailWord_1041279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041279).length < 2 ^ (prefixWord ++ tailWord_1041279).sum := by decide
  have hdescent : baseEnd_1041279 < baseStart_1041279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041282 : List Nat := [3, 4, 2, 2, 1, 2, 1, 5]
def baseStart_1041282 : Nat := 118140960795 + 1041282 * 2 ^ 59
def prefixEnd_1041282 : Nat := 4983230072969 + 3 ^ 40 * 1041282 * 2
def baseEnd_1041282 : Nat := 158423159370400063136663

theorem tailTrace_1041282 : CollatzResearch.WordTrace tailWord_1041282 prefixEnd_1041282 158423159370400063136663 := by
  unfold tailWord_1041282
  simp only [CollatzResearch.WordTrace]
  refine ⟨9494668653405156413099525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25319116409080417101598733 9494668653405156413099525)
  ·
    refine ⟨1780250372513466827456161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9494668653405156413099525 1780250372513466827456161)
    ·
      refine ⟨1335187779385100120592121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1780250372513466827456161 1335187779385100120592121)
      ·
        refine ⟨1001390834538825090444091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1335187779385100120592121 1001390834538825090444091)
        ·
          refine ⟨1502086251808237635666137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1001390834538825090444091 1502086251808237635666137)
          ·
            refine ⟨1126564688856178226749603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1502086251808237635666137 1126564688856178226749603)
            ·
              refine ⟨1689847033284267340124405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126564688856178226749603 1689847033284267340124405)
              ·
                refine ⟨158423159370400063136663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1689847033284267340124405 158423159370400063136663)
                ·
                  rfl

theorem cell20_1041282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_1041282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041282 prefixEnd_1041282 := by exact prefixLift 1041282
  have htrace : WordTrace (prefixWord ++ tailWord_1041282) baseStart_1041282 baseEnd_1041282 := by
    simpa [prefixWord, tailWord_1041282, baseEnd_1041282] using wordTrace_append hprefix tailTrace_1041282
  have hstable : (prefixWord ++ tailWord_1041282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041282).length < 2 ^ (prefixWord ++ tailWord_1041282).sum := by decide
  have hdescent : baseEnd_1041282 < baseStart_1041282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041283 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_1041283 : Nat := 118140960795 + 1041283 * 2 ^ 59
def prefixEnd_1041283 : Nat := 4983230072969 + 3 ^ 40 * 1041283 * 2
def baseEnd_1041283 : Nat := 475269934538448630376651

theorem tailTrace_1041283 : CollatzResearch.WordTrace tailWord_1041283 prefixEnd_1041283 475269934538448630376651 := by
  unfold tailWord_1041283
  simp only [CollatzResearch.WordTrace]
  refine ⟨37978711086617002823184503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25319140724411335215456335 37978711086617002823184503)
  ·
    refine ⟨56968066629925504234776755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37978711086617002823184503 56968066629925504234776755)
    ·
      refine ⟨85452099944888256352165133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56968066629925504234776755 85452099944888256352165133)
      ·
        refine ⟨32044537479333096132061925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85452099944888256352165133 32044537479333096132061925)
        ·
          refine ⟨6008350777374955524761611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32044537479333096132061925 6008350777374955524761611)
          ·
            refine ⟨9012526166062433287142417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008350777374955524761611 9012526166062433287142417)
            ·
              refine ⟨6759394624546824965356813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9012526166062433287142417 6759394624546824965356813)
              ·
                refine ⟨2534772984205059362008805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6759394624546824965356813 2534772984205059362008805)
                ·
                  refine ⟨475269934538448630376651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534772984205059362008805 475269934538448630376651)
                  ·
                    rfl

theorem cell20_1041283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_1041283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041283 prefixEnd_1041283 := by exact prefixLift 1041283
  have htrace : WordTrace (prefixWord ++ tailWord_1041283) baseStart_1041283 baseEnd_1041283 := by
    simpa [prefixWord, tailWord_1041283, baseEnd_1041283] using wordTrace_append hprefix tailTrace_1041283
  have hstable : (prefixWord ++ tailWord_1041283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041283).length < 2 ^ (prefixWord ++ tailWord_1041283).sum := by decide
  have hdescent : baseEnd_1041283 < baseStart_1041283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041297 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_1041297 : Nat := 118140960795 + 1041297 * 2 ^ 59
def prefixEnd_1041297 : Nat := 4983230072969 + 3 ^ 40 * 1041297 * 2
def baseEnd_1041297 : Nat := 475276324519926803909927

theorem tailTrace_1041297 : CollatzResearch.WordTrace tailWord_1041297 prefixEnd_1041297 475276324519926803909927 := by
  unfold tailWord_1041297
  simp only [CollatzResearch.WordTrace]
  refine ⟨37979221708566283214194145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25319481139044188809462763 37979221708566283214194145)
  ·
    refine ⟨28484416281424712410645609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37979221708566283214194145 28484416281424712410645609)
    ·
      refine ⟨21363312211068534307984207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28484416281424712410645609 21363312211068534307984207)
      ·
        refine ⟨32044968316602801461976311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21363312211068534307984207 32044968316602801461976311)
        ·
          refine ⟨48067452474904202192964467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32044968316602801461976311 48067452474904202192964467)
          ·
            refine ⟨72101178712356303289446701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48067452474904202192964467 72101178712356303289446701)
            ·
              refine ⟨27037942017133613733542513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72101178712356303289446701 27037942017133613733542513)
              ·
                refine ⟨20278456512850210300156885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27037942017133613733542513 20278456512850210300156885)
                ·
                  refine ⟨475276324519926803909927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20278456512850210300156885 475276324519926803909927)
                  ·
                    rfl

theorem cell20_1041297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_1041297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041297 prefixEnd_1041297 := by exact prefixLift 1041297
  have htrace : WordTrace (prefixWord ++ tailWord_1041297) baseStart_1041297 baseEnd_1041297 := by
    simpa [prefixWord, tailWord_1041297, baseEnd_1041297] using wordTrace_append hprefix tailTrace_1041297
  have hstable : (prefixWord ++ tailWord_1041297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041297).length < 2 ^ (prefixWord ++ tailWord_1041297).sum := by decide
  have hdescent : baseEnd_1041297 < baseStart_1041297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041300 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1041300 : Nat := 118140960795 + 1041300 * 2 ^ 59
def prefixEnd_1041300 : Nat := 4983230072969 + 3 ^ 40 * 1041300 * 2
def baseEnd_1041300 : Nat := 475277693801672126809915

theorem tailTrace_1041300 : CollatzResearch.WordTrace tailWord_1041300 prefixEnd_1041300 475277693801672126809915 := by
  unfold tailWord_1041300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18989665563777707363276677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25319554085036943151035569 18989665563777707363276677)
  ·
    refine ⟨3560562293208320130614377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18989665563777707363276677 3560562293208320130614377)
    ·
      refine ⟨2670421719906240097960783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3560562293208320130614377 2670421719906240097960783)
      ·
        refine ⟨4005632579859360146941175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2670421719906240097960783 4005632579859360146941175)
        ·
          refine ⟨6008448869789040220411763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4005632579859360146941175 6008448869789040220411763)
          ·
            refine ⟨9012673304683560330617645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008448869789040220411763 9012673304683560330617645)
            ·
              refine ⟨3379752489256335123981617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9012673304683560330617645 3379752489256335123981617)
              ·
                refine ⟨2534814366942251342986213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379752489256335123981617 2534814366942251342986213)
                ·
                  refine ⟨475277693801672126809915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534814366942251342986213 475277693801672126809915)
                  ·
                    rfl

theorem cell20_1041300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1041300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041300 prefixEnd_1041300 := by exact prefixLift 1041300
  have htrace : WordTrace (prefixWord ++ tailWord_1041300) baseStart_1041300 baseEnd_1041300 := by
    simpa [prefixWord, tailWord_1041300, baseEnd_1041300] using wordTrace_append hprefix tailTrace_1041300
  have hstable : (prefixWord ++ tailWord_1041300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041300).length < 2 ^ (prefixWord ++ tailWord_1041300).sum := by decide
  have hdescent : baseEnd_1041300 < baseStart_1041300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041338 : List Nat := [3, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_1041338 : Nat := 118140960795 + 1041338 * 2 ^ 59
def prefixEnd_1041338 : Nat := 4983230072969 + 3 ^ 40 * 1041338 * 2
def baseEnd_1041338 : Nat := 475295038037112883543093

theorem tailTrace_1041338 : CollatzResearch.WordTrace tailWord_1041338 prefixEnd_1041338 475295038037112883543093 := by
  unfold tailWord_1041338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495179275354436804109167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25320478067611831477624445 9495179275354436804109167)
  ·
    refine ⟨14242768913031655206163751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9495179275354436804109167 14242768913031655206163751)
    ·
      refine ⟨21364153369547482809245627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14242768913031655206163751 21364153369547482809245627)
      ·
        refine ⟨32046230054321224213868441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21364153369547482809245627 32046230054321224213868441)
        ·
          refine ⟨24034672540740918160401331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32046230054321224213868441 24034672540740918160401331)
          ·
            refine ⟨36052008811111377240601997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24034672540740918160401331 36052008811111377240601997)
            ·
              refine ⟨13519503304166766465225749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36052008811111377240601997 13519503304166766465225749)
              ·
                refine ⟨633726717382817178057457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13519503304166766465225749 633726717382817178057457)
                ·
                  refine ⟨475295038037112883543093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633726717382817178057457 475295038037112883543093)
                  ·
                    rfl

theorem cell20_1041338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_1041338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041338 prefixEnd_1041338 := by exact prefixLift 1041338
  have htrace : WordTrace (prefixWord ++ tailWord_1041338) baseStart_1041338 baseEnd_1041338 := by
    simpa [prefixWord, tailWord_1041338, baseEnd_1041338] using wordTrace_append hprefix tailTrace_1041338
  have hstable : (prefixWord ++ tailWord_1041338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041338).length < 2 ^ (prefixWord ++ tailWord_1041338).sum := by decide
  have hdescent : baseEnd_1041338 < baseStart_1041338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041359 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_1041359 : Nat := 118140960795 + 1041359 * 2 ^ 59
def prefixEnd_1041359 : Nat := 4983230072969 + 3 ^ 40 * 1041359 * 2
def baseEnd_1041359 : Nat := 475304623009330143843007

theorem tailTrace_1041359 : CollatzResearch.WordTrace tailWord_1041359 prefixEnd_1041359 475304623009330143843007 := by
  unfold tailWord_1041359
  simp only [CollatzResearch.WordTrace]
  refine ⟨37981483034341667802951131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25320988689561111868634087 37981483034341667802951131)
  ·
    refine ⟨56972224551512501704426697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37981483034341667802951131 56972224551512501704426697)
    ·
      refine ⟨42729168413634376278320023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56972224551512501704426697 42729168413634376278320023)
      ·
        refine ⟨64093752620451564417480035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42729168413634376278320023 64093752620451564417480035)
        ·
          refine ⟨96140628930677346626220053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64093752620451564417480035 96140628930677346626220053)
          ·
            refine ⟨4506591981125500623104065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 96140628930677346626220053 4506591981125500623104065)
            ·
              refine ⟨3379943985844125467328049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4506591981125500623104065 3379943985844125467328049)
              ·
                refine ⟨2534957989383094100496037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3379943985844125467328049 2534957989383094100496037)
                ·
                  refine ⟨475304623009330143843007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2534957989383094100496037 475304623009330143843007)
                  ·
                    rfl

theorem cell20_1041359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_1041359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041359 prefixEnd_1041359 := by exact prefixLift 1041359
  have htrace : WordTrace (prefixWord ++ tailWord_1041359) baseStart_1041359 baseEnd_1041359 := by
    simpa [prefixWord, tailWord_1041359, baseEnd_1041359] using wordTrace_append hprefix tailTrace_1041359
  have hstable : (prefixWord ++ tailWord_1041359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041359).length < 2 ^ (prefixWord ++ tailWord_1041359).sum := by decide
  have hdescent : baseEnd_1041359 < baseStart_1041359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041362 : List Nat := [3, 2, 2, 3, 1, 1, 4, 4]
def baseStart_1041362 : Nat := 118140960795 + 1041362 * 2 ^ 59
def prefixEnd_1041362 : Nat := 4983230072969 + 3 ^ 40 * 1041362 * 2
def baseEnd_1041362 : Nat := 158435330763691822247665

theorem tailTrace_1041362 : CollatzResearch.WordTrace tailWord_1041362 prefixEnd_1041362 158435330763691822247665 := by
  unfold tailWord_1041362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9495398113332699828827585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25321061635553866210206893 9495398113332699828827585)
  ·
    refine ⟨7121548584999524871620689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9495398113332699828827585 7121548584999524871620689)
    ·
      refine ⟨5341161438749643653715517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7121548584999524871620689 5341161438749643653715517)
      ·
        refine ⟨2002935539531116370143319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5341161438749643653715517 2002935539531116370143319)
        ·
          refine ⟨3004403309296674555214979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2002935539531116370143319 3004403309296674555214979)
          ·
            refine ⟨4506604963945011832822469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3004403309296674555214979 4506604963945011832822469)
            ·
              refine ⟨844988430739689718654213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4506604963945011832822469 844988430739689718654213)
              ·
                refine ⟨158435330763691822247665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 844988430739689718654213 158435330763691822247665)
                ·
                  rfl

theorem cell20_1041362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_1041362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041362 prefixEnd_1041362 := by exact prefixLift 1041362
  have htrace : WordTrace (prefixWord ++ tailWord_1041362) baseStart_1041362 baseEnd_1041362 := by
    simpa [prefixWord, tailWord_1041362, baseEnd_1041362] using wordTrace_append hprefix tailTrace_1041362
  have hstable : (prefixWord ++ tailWord_1041362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041362).length < 2 ^ (prefixWord ++ tailWord_1041362).sum := by decide
  have hdescent : baseEnd_1041362 < baseStart_1041362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041383 : List Nat := [1, 1, 5, 2, 2, 3, 6]
def baseStart_1041383 : Nat := 118140960795 + 1041383 * 2 ^ 59
def prefixEnd_1041383 : Nat := 4983230072969 + 3 ^ 40 * 1041383 * 2
def baseEnd_1041383 : Nat := 52812841918143636338101

theorem tailTrace_1041383 : CollatzResearch.WordTrace tailWord_1041383 prefixEnd_1041383 52812841918143636338101 := by
  unfold tailWord_1041383
  simp only [CollatzResearch.WordTrace]
  refine ⟨37982358386254719901824803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25321572257503146601216535 37982358386254719901824803)
  ·
    refine ⟨56973537579382079852737205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37982358386254719901824803 56973537579382079852737205)
    ·
      refine ⟨5341269148067069986194113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56973537579382079852737205 5341269148067069986194113)
      ·
        refine ⟨4005951861050302489645585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5341269148067069986194113 4005951861050302489645585)
        ·
          refine ⟨3004463895787726867234189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4005951861050302489645585 3004463895787726867234189)
          ·
            refine ⟨1126673960920397575212821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3004463895787726867234189 1126673960920397575212821)
            ·
              refine ⟨52812841918143636338101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1126673960920397575212821 52812841918143636338101)
              ·
                rfl

theorem cell20_1041383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 6].length) (baseStart_1041383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041383 prefixEnd_1041383 := by exact prefixLift 1041383
  have htrace : WordTrace (prefixWord ++ tailWord_1041383) baseStart_1041383 baseEnd_1041383 := by
    simpa [prefixWord, tailWord_1041383, baseEnd_1041383] using wordTrace_append hprefix tailTrace_1041383
  have hstable : (prefixWord ++ tailWord_1041383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041383).length < 2 ^ (prefixWord ++ tailWord_1041383).sum := by decide
  have hdescent : baseEnd_1041383 < baseStart_1041383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041404 : List Nat := [2, 2, 2, 1, 2, 3, 1, 7]
def baseStart_1041404 : Nat := 118140960795 + 1041404 * 2 ^ 59
def prefixEnd_1041404 : Nat := 4983230072969 + 3 ^ 40 * 1041404 * 2
def baseEnd_1041404 : Nat := 158441720745169995780941

theorem tailTrace_1041404 : CollatzResearch.WordTrace tailWord_1041404 prefixEnd_1041404 158441720745169995780941 := by
  unfold tailWord_1041404
  simp only [CollatzResearch.WordTrace]
  refine ⟨18991562159589320244169633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25322082879452426992226177 18991562159589320244169633)
  ·
    refine ⟨14243671619691990183127225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18991562159589320244169633 14243671619691990183127225)
    ·
      refine ⟨10682753714768992637345419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14243671619691990183127225 10682753714768992637345419)
      ·
        refine ⟨16024130572153488956018129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10682753714768992637345419 16024130572153488956018129)
        ·
          refine ⟨12018097929115116717013597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16024130572153488956018129 12018097929115116717013597)
          ·
            refine ⟨4506786723418168768880099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12018097929115116717013597 4506786723418168768880099)
            ·
              refine ⟨6760180085127253153320149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4506786723418168768880099 6760180085127253153320149)
              ·
                refine ⟨158441720745169995780941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6760180085127253153320149 158441720745169995780941)
                ·
                  rfl

theorem cell20_1041404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_1041404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041404 prefixEnd_1041404 := by exact prefixLift 1041404
  have htrace : WordTrace (prefixWord ++ tailWord_1041404) baseStart_1041404 baseEnd_1041404 := by
    simpa [prefixWord, tailWord_1041404, baseEnd_1041404] using wordTrace_append hprefix tailTrace_1041404
  have hstable : (prefixWord ++ tailWord_1041404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041404).length < 2 ^ (prefixWord ++ tailWord_1041404).sum := by decide
  have hdescent : baseEnd_1041404 < baseStart_1041404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041442 : List Nat := [3, 3, 1, 1, 1, 11]
def baseStart_1041442 : Nat := 118140960795 + 1041442 * 2 ^ 59
def prefixEnd_1041442 : Nat := 4983230072969 + 3 ^ 40 * 1041442 * 2
def baseEnd_1041442 : Nat := 17605278017442620150963

theorem tailTrace_1041442 : CollatzResearch.WordTrace tailWord_1041442 prefixEnd_1041442 17605278017442620150963 := by
  unfold tailWord_1041442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496127573260243244555645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25323006862027315318815053 9496127573260243244555645)
  ·
    refine ⟨3561047839972591216708367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9496127573260243244555645 3561047839972591216708367)
    ·
      refine ⟨5341571759958886825062551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3561047839972591216708367 5341571759958886825062551)
      ·
        refine ⟨8012357639938330237593827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341571759958886825062551 8012357639938330237593827)
        ·
          refine ⟨12018536459907495356390741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012357639938330237593827 12018536459907495356390741)
          ·
            refine ⟨17605278017442620150963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 12018536459907495356390741 17605278017442620150963)
            ·
              rfl

theorem cell20_1041442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 11].length) (baseStart_1041442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041442 prefixEnd_1041442 := by exact prefixLift 1041442
  have htrace : WordTrace (prefixWord ++ tailWord_1041442) baseStart_1041442 baseEnd_1041442 := by
    simpa [prefixWord, tailWord_1041442, baseEnd_1041442] using wordTrace_append hprefix tailTrace_1041442
  have hstable : (prefixWord ++ tailWord_1041442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041442).length < 2 ^ (prefixWord ++ tailWord_1041442).sum := by decide
  have hdescent : baseEnd_1041442 < baseStart_1041442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041452 : List Nat := [2, 2, 1, 1, 1, 2, 5, 4, 2]
def baseStart_1041452 : Nat := 118140960795 + 1041452 * 2 ^ 59
def prefixEnd_1041452 : Nat := 4983230072969 + 3 ^ 40 * 1041452 * 2
def baseEnd_1041452 : Nat := 475347070743435153742627

theorem tailTrace_1041452 : CollatzResearch.WordTrace tailWord_1041452 prefixEnd_1041452 475347070743435153742627 := by
  unfold tailWord_1041452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18992437511502372343043305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25323250015336496457391073 18992437511502372343043305)
  ·
    refine ⟨14244328133626779257282479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18992437511502372343043305 14244328133626779257282479)
    ·
      refine ⟨21366492200440168885923719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14244328133626779257282479 21366492200440168885923719)
      ·
        refine ⟨32049738300660253328885579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21366492200440168885923719 32049738300660253328885579)
        ·
          refine ⟨48074607450990379993328369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32049738300660253328885579 48074607450990379993328369)
          ·
            refine ⟨36055955588242784994996277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48074607450990379993328369 36055955588242784994996277)
            ·
              refine ⟨3380245836397761093280901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36055955588242784994996277 3380245836397761093280901)
              ·
                refine ⟨633796094324580204990169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3380245836397761093280901 633796094324580204990169)
                ·
                  refine ⟨475347070743435153742627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633796094324580204990169 475347070743435153742627)
                  ·
                    rfl

theorem cell20_1041452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_1041452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041452 prefixEnd_1041452 := by exact prefixLift 1041452
  have htrace : WordTrace (prefixWord ++ tailWord_1041452) baseStart_1041452 baseEnd_1041452 := by
    simpa [prefixWord, tailWord_1041452, baseEnd_1041452] using wordTrace_append hprefix tailTrace_1041452
  have hstable : (prefixWord ++ tailWord_1041452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041452).length < 2 ^ (prefixWord ++ tailWord_1041452).sum := by decide
  have hdescent : baseEnd_1041452 < baseStart_1041452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041466 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_1041466 : Nat := 118140960795 + 1041466 * 2 ^ 59
def prefixEnd_1041466 : Nat := 4983230072969 + 3 ^ 40 * 1041466 * 2
def baseEnd_1041466 : Nat := 475353460724913327275903

theorem tailTrace_1041466 : CollatzResearch.WordTrace tailWord_1041466 prefixEnd_1041466 475353460724913327275903 := by
  unfold tailWord_1041466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9496346411238506269274063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25323590429969350051397501 9496346411238506269274063)
  ·
    refine ⟨14244519616857759403911095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9496346411238506269274063 14244519616857759403911095)
    ·
      refine ⟨21366779425286639105866643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14244519616857759403911095 21366779425286639105866643)
      ·
        refine ⟨32050169137929958658799965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21366779425286639105866643 32050169137929958658799965)
        ·
          refine ⟨12018813426723734497049987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32050169137929958658799965 12018813426723734497049987)
          ·
            refine ⟨18028220140085601745574981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018813426723734497049987 18028220140085601745574981)
            ·
              refine ⟨3380291276266050327295309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18028220140085601745574981 3380291276266050327295309)
              ·
                refine ⟨1267609228599768872735741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3380291276266050327295309 1267609228599768872735741)
                ·
                  refine ⟨475353460724913327275903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1267609228599768872735741 475353460724913327275903)
                  ·
                    rfl

theorem cell20_1041466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_1041466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041466 prefixEnd_1041466 := by exact prefixLift 1041466
  have htrace : WordTrace (prefixWord ++ tailWord_1041466) baseStart_1041466 baseEnd_1041466 := by
    simpa [prefixWord, tailWord_1041466, baseEnd_1041466] using wordTrace_append hprefix tailTrace_1041466
  have hstable : (prefixWord ++ tailWord_1041466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041466).length < 2 ^ (prefixWord ++ tailWord_1041466).sum := by decide
  have hdescent : baseEnd_1041466 < baseStart_1041466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041511 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_1041511 : Nat := 118140960795 + 1041511 * 2 ^ 59
def prefixEnd_1041511 : Nat := 4983230072969 + 3 ^ 40 * 1041511 * 2
def baseEnd_1041511 : Nat := 475373999951093170775719

theorem tailTrace_1041511 : CollatzResearch.WordTrace tailWord_1041511 prefixEnd_1041511 475373999951093170775719 := by
  unfold tailWord_1041511
  simp only [CollatzResearch.WordTrace]
  refine ⟨37987026929790997762484387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25324684619860665174989591 37987026929790997762484387)
  ·
    refine ⟨56980540394686496643726581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37987026929790997762484387 56980540394686496643726581)
    ·
      refine ⟨5341925662001859060349367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56980540394686496643726581 5341925662001859060349367)
      ·
        refine ⟨8012888493002788590524051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341925662001859060349367 8012888493002788590524051)
        ·
          refine ⟨12019332739504182885786077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012888493002788590524051 12019332739504182885786077)
          ·
            refine ⟨4507249777314068582169779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12019332739504182885786077 4507249777314068582169779)
            ·
              refine ⟨6760874665971102873254669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4507249777314068582169779 6760874665971102873254669)
              ·
                refine ⟨2535327999739163577470501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6760874665971102873254669 2535327999739163577470501)
                ·
                  refine ⟨475373999951093170775719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2535327999739163577470501 475373999951093170775719)
                  ·
                    rfl

theorem cell20_1041511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_1041511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041511 prefixEnd_1041511 := by exact prefixLift 1041511
  have htrace : WordTrace (prefixWord ++ tailWord_1041511) baseStart_1041511 baseEnd_1041511 := by
    simpa [prefixWord, tailWord_1041511, baseEnd_1041511] using wordTrace_append hprefix tailTrace_1041511
  have hstable : (prefixWord ++ tailWord_1041511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041511).length < 2 ^ (prefixWord ++ tailWord_1041511).sum := by decide
  have hdescent : baseEnd_1041511 < baseStart_1041511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1041545 : List Nat := [1, 2, 1, 1, 4, 5, 1, 3, 2]
def baseStart_1041545 : Nat := 118140960795 + 1041545 * 2 ^ 59
def prefixEnd_1041545 : Nat := 4983230072969 + 3 ^ 40 * 1041545 * 2
def baseEnd_1041545 : Nat := 475389518477540163642247

theorem tailTrace_1041545 : CollatzResearch.WordTrace tailWord_1041545 prefixEnd_1041545 475389518477540163642247 := by
  unfold tailWord_1041545
  simp only [CollatzResearch.WordTrace]
  refine ⟨37988267011667821569222089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25325511341111881046148059 37988267011667821569222089)
  ·
    refine ⟨28491200258750866176916567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37988267011667821569222089 28491200258750866176916567)
    ·
      refine ⟨42736800388126299265374851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28491200258750866176916567 42736800388126299265374851)
      ·
        refine ⟨64105200582189448898062277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42736800388126299265374851 64105200582189448898062277)
        ·
          refine ⟨12019725109160521668386677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64105200582189448898062277 12019725109160521668386677)
          ·
            refine ⟨1126849228983798906411251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12019725109160521668386677 1126849228983798906411251)
            ·
              refine ⟨1690273843475698359616877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1126849228983798906411251 1690273843475698359616877)
              ·
                refine ⟨633852691303386884856329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1690273843475698359616877 633852691303386884856329)
                ·
                  refine ⟨475389518477540163642247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 633852691303386884856329 475389518477540163642247)
                  ·
                    rfl

theorem cell20_1041545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_1041545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1041545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1041545 prefixEnd_1041545 := by exact prefixLift 1041545
  have htrace : WordTrace (prefixWord ++ tailWord_1041545) baseStart_1041545 baseEnd_1041545 := by
    simpa [prefixWord, tailWord_1041545, baseEnd_1041545] using wordTrace_append hprefix tailTrace_1041545
  have hstable : (prefixWord ++ tailWord_1041545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1041545).length < 2 ^ (prefixWord ++ tailWord_1041545).sum := by decide
  have hdescent : baseEnd_1041545 < baseStart_1041545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1041545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
