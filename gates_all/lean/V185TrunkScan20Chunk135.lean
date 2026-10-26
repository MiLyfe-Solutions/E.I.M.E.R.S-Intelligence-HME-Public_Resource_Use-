import V185TrunkScan20Chunk134

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_820037 : List Nat := [1, 3, 1, 1, 1, 2, 2, 7, 2]
def baseStart_820037 : Nat := 118140960795 + 820037 * 2 ^ 59
def prefixEnd_820037 : Nat := 4983230072969 + 3 ^ 40 * 820037 * 2
def baseEnd_820037 : Nat := 374287231529878520147755

theorem tailTrace_820037 : CollatzResearch.WordTrace tailWord_820037 prefixEnd_820037 374287231529878520147755 := by
  unfold tailWord_820037
  simp only [CollatzResearch.WordTrace]
  refine ⟨29909206530153475014666365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19939471020102316676444243 29909206530153475014666365)
  ·
    refine ⟨11215952448807553130499887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29909206530153475014666365 11215952448807553130499887)
    ·
      refine ⟨16823928673211329695749831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11215952448807553130499887 16823928673211329695749831)
      ·
        refine ⟨25235893009816994543624747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16823928673211329695749831 25235893009816994543624747)
        ·
          refine ⟨37853839514725491815437121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25235893009816994543624747 37853839514725491815437121)
          ·
            refine ⟨28390379636044118861577841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37853839514725491815437121 28390379636044118861577841)
            ·
              refine ⟨21292784727033089146183381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28390379636044118861577841 21292784727033089146183381)
              ·
                refine ⟨499049642039838026863673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21292784727033089146183381 499049642039838026863673)
                ·
                  refine ⟨374287231529878520147755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499049642039838026863673 374287231529878520147755)
                  ·
                    rfl

theorem cell20_820037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 2].length) (baseStart_820037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820037 prefixEnd_820037 := by exact prefixLift 820037
  have htrace : WordTrace (prefixWord ++ tailWord_820037) baseStart_820037 baseEnd_820037 := by
    simpa [prefixWord, tailWord_820037, baseEnd_820037] using wordTrace_append hprefix tailTrace_820037
  have hstable : (prefixWord ++ tailWord_820037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820037).length < 2 ^ (prefixWord ++ tailWord_820037).sum := by decide
  have hdescent : baseEnd_820037 < baseStart_820037 := by decide
  rcases family_descends (prefixWord ++ tailWord_820037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820044 : List Nat := [2, 2, 1, 3, 3, 3, 6]
def baseStart_820044 : Nat := 118140960795 + 820044 * 2 ^ 59
def prefixEnd_820044 : Nat := 4983230072969 + 3 ^ 40 * 820044 * 2
def baseEnd_820044 : Nat := 41587825168957511879377

theorem tailTrace_820044 : CollatzResearch.WordTrace tailWord_820044 prefixEnd_820044 41587825168957511879377 := by
  unfold tailWord_820044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954730920564057605085593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19939641227418743473447457 14954730920564057605085593)
  ·
    refine ⟨11216048190423043203814195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14954730920564057605085593 11216048190423043203814195)
    ·
      refine ⟨16824072285634564805721293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11216048190423043203814195 16824072285634564805721293)
      ·
        refine ⟨6309027107112961802145485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16824072285634564805721293 6309027107112961802145485)
        ·
          refine ⟨2365885165167360675804557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6309027107112961802145485 2365885165167360675804557)
          ·
            refine ⟨887206936937760253426709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2365885165167360675804557 887206936937760253426709)
            ·
              refine ⟨41587825168957511879377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 887206936937760253426709 41587825168957511879377)
              ·
                rfl

theorem cell20_820044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 6].length) (baseStart_820044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820044 prefixEnd_820044 := by exact prefixLift 820044
  have htrace : WordTrace (prefixWord ++ tailWord_820044) baseStart_820044 baseEnd_820044 := by
    simpa [prefixWord, tailWord_820044, baseEnd_820044] using wordTrace_append hprefix tailTrace_820044
  have hstable : (prefixWord ++ tailWord_820044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820044).length < 2 ^ (prefixWord ++ tailWord_820044).sum := by decide
  have hdescent : baseEnd_820044 < baseStart_820044 := by decide
  rcases family_descends (prefixWord ++ tailWord_820044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820068 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_820068 : Nat := 118140960795 + 820068 * 2 ^ 59
def prefixEnd_820068 : Nat := 4983230072969 + 3 ^ 40 * 820068 * 2
def baseEnd_820068 : Nat := 374301380774580190114295

theorem tailTrace_820068 : CollatzResearch.WordTrace tailWord_820068 prefixEnd_820068 374301380774580190114295 := by
  unfold tailWord_820068
  simp only [CollatzResearch.WordTrace]
  refine ⟨14955168596520583654522429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19940224795360778206029905 14955168596520583654522429)
  ·
    refine ⟨5608188223695218870445911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14955168596520583654522429 5608188223695218870445911)
    ·
      refine ⟨8412282335542828305668867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5608188223695218870445911 8412282335542828305668867)
      ·
        refine ⟨12618423503314242458503301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8412282335542828305668867 12618423503314242458503301)
        ·
          refine ⟨2365954406871420460969369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12618423503314242458503301 2365954406871420460969369)
          ·
            refine ⟨1774465805153565345727027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2365954406871420460969369 1774465805153565345727027)
            ·
              refine ⟨2661698707730348018590541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774465805153565345727027 2661698707730348018590541)
              ·
                refine ⟨998137015398880506971453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2661698707730348018590541 998137015398880506971453)
                ·
                  refine ⟨374301380774580190114295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998137015398880506971453 374301380774580190114295)
                  ·
                    rfl

theorem cell20_820068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_820068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820068 prefixEnd_820068 := by exact prefixLift 820068
  have htrace : WordTrace (prefixWord ++ tailWord_820068) baseStart_820068 baseEnd_820068 := by
    simpa [prefixWord, tailWord_820068, baseEnd_820068] using wordTrace_append hprefix tailTrace_820068
  have hstable : (prefixWord ++ tailWord_820068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820068).length < 2 ^ (prefixWord ++ tailWord_820068).sum := by decide
  have hdescent : baseEnd_820068 < baseStart_820068 := by decide
  rcases family_descends (prefixWord ++ tailWord_820068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820103 : List Nat := [1, 1, 4, 2, 3, 9]
def baseStart_820103 : Nat := 118140960795 + 820103 * 2 ^ 59
def prefixEnd_820103 : Nat := 4983230072969 + 3 ^ 40 * 820103 * 2
def baseEnd_820103 : Nat := 13863605767713911998055

theorem tailTrace_820103 : CollatzResearch.WordTrace tailWord_820103 prefixEnd_820103 13863605767713911998055 := by
  unfold tailWord_820103
  simp only [CollatzResearch.WordTrace]
  refine ⟨29911613747914368286568963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19941075831942912191045975 29911613747914368286568963)
  ·
    refine ⟨44867420621871552429853445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29911613747914368286568963 44867420621871552429853445)
    ·
      refine ⟨8412641366600916080597521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44867420621871552429853445 8412641366600916080597521)
      ·
        refine ⟨6309481024950687060448141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8412641366600916080597521 6309481024950687060448141)
        ·
          refine ⟨2366055384356507647668053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6309481024950687060448141 2366055384356507647668053)
          ·
            refine ⟨13863605767713911998055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2366055384356507647668053 13863605767713911998055)
            ·
              rfl

theorem cell20_820103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 9].length) (baseStart_820103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820103 prefixEnd_820103 := by exact prefixLift 820103
  have htrace : WordTrace (prefixWord ++ tailWord_820103) baseStart_820103 baseEnd_820103 := by
    simpa [prefixWord, tailWord_820103, baseEnd_820103] using wordTrace_append hprefix tailTrace_820103
  have hstable : (prefixWord ++ tailWord_820103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820103).length < 2 ^ (prefixWord ++ tailWord_820103).sum := by decide
  have hdescent : baseEnd_820103 < baseStart_820103 := by decide
  rcases family_descends (prefixWord ++ tailWord_820103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820106 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_820106 : Nat := 118140960795 + 820106 * 2 ^ 59
def prefixEnd_820106 : Nat := 4983230072969 + 3 ^ 40 * 820106 * 2
def baseEnd_820106 : Nat := 374318725010020946847473

theorem tailTrace_820106 : CollatzResearch.WordTrace tailWord_820106 prefixEnd_820106 374318725010020946847473 := by
  unfold tailWord_820106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7477930791725874949732043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19941148777935666532618781 7477930791725874949732043)
  ·
    refine ⟨11216896187588812424598065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7477930791725874949732043 11216896187588812424598065)
    ·
      refine ⟨8412672140691609318448549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11216896187588812424598065 8412672140691609318448549)
      ·
        refine ⟨1577376026379676747209103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8412672140691609318448549 1577376026379676747209103)
        ·
          refine ⟨2366064039569515120813655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577376026379676747209103 2366064039569515120813655)
          ·
            refine ⟨3549096059354272681220483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366064039569515120813655 3549096059354272681220483)
            ·
              refine ⟨5323644089031409021830725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3549096059354272681220483 5323644089031409021830725)
              ·
                refine ⟨998183266693389191593261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5323644089031409021830725 998183266693389191593261)
                ·
                  refine ⟨374318725010020946847473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998183266693389191593261 374318725010020946847473)
                  ·
                    rfl

theorem cell20_820106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_820106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820106 prefixEnd_820106 := by exact prefixLift 820106
  have htrace : WordTrace (prefixWord ++ tailWord_820106) baseStart_820106 baseEnd_820106 := by
    simpa [prefixWord, tailWord_820106, baseEnd_820106] using wordTrace_append hprefix tailTrace_820106
  have hstable : (prefixWord ++ tailWord_820106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820106).length < 2 ^ (prefixWord ++ tailWord_820106).sum := by decide
  have hdescent : baseEnd_820106 < baseStart_820106 := by decide
  rcases family_descends (prefixWord ++ tailWord_820106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820151 : List Nat := [1, 1, 3, 1, 3, 1, 3, 5, 2]
def baseStart_820151 : Nat := 118140960795 + 820151 * 2 ^ 59
def prefixEnd_820151 : Nat := 4983230072969 + 3 ^ 40 * 820151 * 2
def baseEnd_820151 : Nat := 374339264236200790347289

theorem tailTrace_820151 : CollatzResearch.WordTrace tailWord_820151 prefixEnd_820151 374339264236200790347289 := by
  unfold tailWord_820151
  simp only [CollatzResearch.WordTrace]
  refine ⟨29913364451740472484316307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19942242967826981656210871 29913364451740472484316307)
  ·
    refine ⟨44870046677610708726474461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29913364451740472484316307 44870046677610708726474461)
    ·
      refine ⟨16826267504104015772427923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44870046677610708726474461 16826267504104015772427923)
      ·
        refine ⟨25239401256156023658641885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16826267504104015772427923 25239401256156023658641885)
        ·
          refine ⟨9464775471058508871990707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25239401256156023658641885 9464775471058508871990707)
          ·
            refine ⟨14197163206587763307986061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9464775471058508871990707 14197163206587763307986061)
            ·
              refine ⟨5323936202470411240494773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14197163206587763307986061 5323936202470411240494773)
              ·
                refine ⟨499119018981601053796385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5323936202470411240494773 499119018981601053796385)
                ·
                  refine ⟨374339264236200790347289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499119018981601053796385 374339264236200790347289)
                  ·
                    rfl

theorem cell20_820151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 2].length) (baseStart_820151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820151 prefixEnd_820151 := by exact prefixLift 820151
  have htrace : WordTrace (prefixWord ++ tailWord_820151) baseStart_820151 baseEnd_820151 := by
    simpa [prefixWord, tailWord_820151, baseEnd_820151] using wordTrace_append hprefix tailTrace_820151
  have hstable : (prefixWord ++ tailWord_820151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820151).length < 2 ^ (prefixWord ++ tailWord_820151).sum := by decide
  have hdescent : baseEnd_820151 < baseStart_820151 := by decide
  rcases family_descends (prefixWord ++ tailWord_820151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820189 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_820189 : Nat := 118140960795 + 820189 * 2 ^ 59
def prefixEnd_820189 : Nat := 4983230072969 + 3 ^ 40 * 820189 * 2
def baseEnd_820189 : Nat := 374356608471641547080467

theorem tailTrace_820189 : CollatzResearch.WordTrace tailWord_820189 prefixEnd_820189 374356608471641547080467 := by
  unfold tailWord_820189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29914750425602804974199621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19943166950401869982799747 29914750425602804974199621)
  ·
    refine ⟨5609015704800525932662429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29914750425602804974199621 5609015704800525932662429)
    ·
      refine ⟨2103380889300197224748411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5609015704800525932662429 2103380889300197224748411)
      ·
        refine ⟨3155071333950295837122617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103380889300197224748411 3155071333950295837122617)
        ·
          refine ⟨2366303500462721877841963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3155071333950295837122617 2366303500462721877841963)
          ·
            refine ⟨3549455250694082816762945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366303500462721877841963 3549455250694082816762945)
            ·
              refine ⟨2662091438020562112572209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549455250694082816762945 2662091438020562112572209)
              ·
                refine ⟨1996568578515421584429157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2662091438020562112572209 1996568578515421584429157)
                ·
                  refine ⟨374356608471641547080467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996568578515421584429157 374356608471641547080467)
                  ·
                    rfl

theorem cell20_820189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_820189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820189 prefixEnd_820189 := by exact prefixLift 820189
  have htrace : WordTrace (prefixWord ++ tailWord_820189) baseStart_820189 baseEnd_820189 := by
    simpa [prefixWord, tailWord_820189, baseEnd_820189] using wordTrace_append hprefix tailTrace_820189
  have hstable : (prefixWord ++ tailWord_820189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820189).length < 2 ^ (prefixWord ++ tailWord_820189).sum := by decide
  have hdescent : baseEnd_820189 < baseStart_820189 := by decide
  rcases family_descends (prefixWord ++ tailWord_820189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820234 : List Nat := [3, 1, 2, 2, 3, 2, 2, 5]
def baseStart_820234 : Nat := 118140960795 + 820234 * 2 ^ 59
def prefixEnd_820234 : Nat := 4983230072969 + 3 ^ 40 * 820234 * 2
def baseEnd_820234 : Nat := 124792382565940463526761

theorem tailTrace_820234 : CollatzResearch.WordTrace tailWord_820234 prefixEnd_820234 124792382565940463526761 := by
  unfold tailWord_820234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479097927609944414896939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19944261140293185106391837 7479097927609944414896939)
  ·
    refine ⟨11218646891414916622345409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7479097927609944414896939 11218646891414916622345409)
    ·
      refine ⟨8413985168561187466759057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11218646891414916622345409 8413985168561187466759057)
      ·
        refine ⟨6310488876420890600069293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8413985168561187466759057 6310488876420890600069293)
        ·
          refine ⟨2366433328657833975025985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6310488876420890600069293 2366433328657833975025985)
          ·
            refine ⟨1774824996493375481269489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2366433328657833975025985 1774824996493375481269489)
            ·
              refine ⟨1331118747370031610952117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1774824996493375481269489 1331118747370031610952117)
              ·
                refine ⟨124792382565940463526761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1331118747370031610952117 124792382565940463526761)
                ·
                  rfl

theorem cell20_820234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_820234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820234 prefixEnd_820234 := by exact prefixLift 820234
  have htrace : WordTrace (prefixWord ++ tailWord_820234) baseStart_820234 baseEnd_820234 := by
    simpa [prefixWord, tailWord_820234, baseEnd_820234] using wordTrace_append hprefix tailTrace_820234
  have hstable : (prefixWord ++ tailWord_820234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820234).length < 2 ^ (prefixWord ++ tailWord_820234).sum := by decide
  have hdescent : baseEnd_820234 < baseStart_820234 := by decide
  rcases family_descends (prefixWord ++ tailWord_820234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820255 : List Nat := [1, 1, 2, 4, 1, 3, 2, 6]
def baseStart_820255 : Nat := 118140960795 + 820255 * 2 ^ 59
def prefixEnd_820255 : Nat := 4983230072969 + 3 ^ 40 * 820255 * 2
def baseEnd_820255 : Nat := 124795577556679550293399

theorem tailTrace_820255 : CollatzResearch.WordTrace tailWord_820255 prefixEnd_820255 124795577556679550293399 := by
  unfold tailWord_820255
  simp only [CollatzResearch.WordTrace]
  refine ⟨29917157643363698246102219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19944771762242465497401479 29917157643363698246102219)
  ·
    refine ⟨44875736465045547369153329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29917157643363698246102219 44875736465045547369153329)
    ·
      refine ⟨33656802348784160526864997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44875736465045547369153329 33656802348784160526864997)
      ·
        refine ⟨6310650440397030098787187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33656802348784160526864997 6310650440397030098787187)
        ·
          refine ⟨9465975660595545148180781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310650440397030098787187 9465975660595545148180781)
          ·
            refine ⟨3549740872723329430567793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9465975660595545148180781 3549740872723329430567793)
            ·
              refine ⟨2662305654542497072925845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3549740872723329430567793 2662305654542497072925845)
              ·
                refine ⟨124795577556679550293399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2662305654542497072925845 124795577556679550293399)
                ·
                  rfl

theorem cell20_820255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_820255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820255 prefixEnd_820255 := by exact prefixLift 820255
  have htrace : WordTrace (prefixWord ++ tailWord_820255) baseStart_820255 baseEnd_820255 := by
    simpa [prefixWord, tailWord_820255, baseEnd_820255] using wordTrace_append hprefix tailTrace_820255
  have hstable : (prefixWord ++ tailWord_820255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820255).length < 2 ^ (prefixWord ++ tailWord_820255).sum := by decide
  have hdescent : baseEnd_820255 < baseStart_820255 := by decide
  rcases family_descends (prefixWord ++ tailWord_820255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820278 : List Nat := [5, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_820278 : Nat := 118140960795 + 820278 * 2 ^ 59
def prefixEnd_820278 : Nat := 4983230072969 + 3 ^ 40 * 820278 * 2
def baseEnd_820278 : Nat := 374397230496752793113437

theorem tailTrace_820278 : CollatzResearch.WordTrace tailWord_820278 prefixEnd_820278 374397230496752793113437 := by
  unfold tailWord_820278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869874782642523323386843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19945331014853582116126325 1869874782642523323386843)
  ·
    refine ⟨2804812173963784985080265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1869874782642523323386843 2804812173963784985080265)
    ·
      refine ⟨2103609130472838738810199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2804812173963784985080265 2103609130472838738810199)
      ·
        refine ⟨3155413695709258108215299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103609130472838738810199 3155413695709258108215299)
        ·
          refine ⟨4733120543563887162322949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155413695709258108215299 4733120543563887162322949)
          ·
            refine ⟨887460101918228842935553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4733120543563887162322949 887460101918228842935553)
            ·
              refine ⟨665595076438671632201665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 887460101918228842935553 665595076438671632201665)
              ·
                refine ⟨499196307329003724151249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665595076438671632201665 499196307329003724151249)
                ·
                  refine ⟨374397230496752793113437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499196307329003724151249 374397230496752793113437)
                  ·
                    rfl

theorem cell20_820278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_820278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820278 prefixEnd_820278 := by exact prefixLift 820278
  have htrace : WordTrace (prefixWord ++ tailWord_820278) baseStart_820278 baseEnd_820278 := by
    simpa [prefixWord, tailWord_820278, baseEnd_820278] using wordTrace_append hprefix tailTrace_820278
  have hstable : (prefixWord ++ tailWord_820278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820278).length < 2 ^ (prefixWord ++ tailWord_820278).sum := by decide
  have hdescent : baseEnd_820278 < baseStart_820278 := by decide
  rcases family_descends (prefixWord ++ tailWord_820278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820282 : List Nat := [3, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_820282 : Nat := 118140960795 + 820282 * 2 ^ 59
def prefixEnd_820282 : Nat := 4983230072969 + 3 ^ 40 * 820282 * 2
def baseEnd_820282 : Nat := 374399056205746556980087

theorem tailTrace_820282 : CollatzResearch.WordTrace tailWord_820282 prefixEnd_820282 374399056205746556980087 := by
  unfold tailWord_820282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479535603566470464333775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19945428276177254571556733 7479535603566470464333775)
  ·
    refine ⟨11219303405349705696500663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7479535603566470464333775 11219303405349705696500663)
    ·
      refine ⟨16828955108024558544750995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11219303405349705696500663 16828955108024558544750995)
      ·
        refine ⟨25243432662036837817126493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16828955108024558544750995 25243432662036837817126493)
        ·
          refine ⟨9466287248263814181422435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25243432662036837817126493 9466287248263814181422435)
          ·
            refine ⟨14199430872395721272133653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9466287248263814181422435 14199430872395721272133653)
            ·
              refine ⟨665598322143549434631265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14199430872395721272133653 665598322143549434631265)
              ·
                refine ⟨499198741607662075973449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665598322143549434631265 499198741607662075973449)
                ·
                  refine ⟨374399056205746556980087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499198741607662075973449 374399056205746556980087)
                  ·
                    rfl

theorem cell20_820282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_820282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820282 prefixEnd_820282 := by exact prefixLift 820282
  have htrace : WordTrace (prefixWord ++ tailWord_820282) baseStart_820282 baseEnd_820282 := by
    simpa [prefixWord, tailWord_820282, baseEnd_820282] using wordTrace_append hprefix tailTrace_820282
  have hstable : (prefixWord ++ tailWord_820282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820282).length < 2 ^ (prefixWord ++ tailWord_820282).sum := by decide
  have hdescent : baseEnd_820282 < baseStart_820282 := by decide
  rcases family_descends (prefixWord ++ tailWord_820282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820289 : List Nat := [1, 2, 5, 1, 3, 2, 1, 5]
def baseStart_820289 : Nat := 118140960795 + 820289 * 2 ^ 59
def prefixEnd_820289 : Nat := 4983230072969 + 3 ^ 40 * 820289 * 2
def baseEnd_820289 : Nat := 124800750398828547915575

theorem tailTrace_820289 : CollatzResearch.WordTrace tailWord_820289 prefixEnd_820289 124800750398828547915575 := by
  unfold tailWord_820289
  simp only [CollatzResearch.WordTrace]
  refine ⟨29918397725240522052839921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19945598483493681368559947 29918397725240522052839921)
  ·
    refine ⟨22438798293930391539629941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29918397725240522052839921 22438798293930391539629941)
    ·
      refine ⟨2103637340055974206840307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22438798293930391539629941 2103637340055974206840307)
      ·
        refine ⟨3155456010083961310260461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103637340055974206840307 3155456010083961310260461)
        ·
          refine ⟨1183296003781485491347673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3155456010083961310260461 1183296003781485491347673)
          ·
            refine ⟨887472002836114118510755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183296003781485491347673 887472002836114118510755)
            ·
              refine ⟨1331208004254171177766133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887472002836114118510755 1331208004254171177766133)
              ·
                refine ⟨124800750398828547915575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1331208004254171177766133 124800750398828547915575)
                ·
                  rfl

theorem cell20_820289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_820289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820289 prefixEnd_820289 := by exact prefixLift 820289
  have htrace : WordTrace (prefixWord ++ tailWord_820289) baseStart_820289 baseEnd_820289 := by
    simpa [prefixWord, tailWord_820289, baseEnd_820289] using wordTrace_append hprefix tailTrace_820289
  have hstable : (prefixWord ++ tailWord_820289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820289).length < 2 ^ (prefixWord ++ tailWord_820289).sum := by decide
  have hdescent : baseEnd_820289 < baseStart_820289 := by decide
  rcases family_descends (prefixWord ++ tailWord_820289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820293 : List Nat := [1, 3, 1, 1, 1, 3, 5, 5]
def baseStart_820293 : Nat := 118140960795 + 820293 * 2 ^ 59
def prefixEnd_820293 : Nat := 4983230072969 + 3 ^ 40 * 820293 * 2
def baseEnd_820293 : Nat := 124801358968493135871125

theorem tailTrace_820293 : CollatzResearch.WordTrace tailWord_820293 prefixEnd_820293 124801358968493135871125 := by
  unfold tailWord_820293
  simp only [CollatzResearch.WordTrace]
  refine ⟨29918543617226030735985533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19945695744817353823990355 29918543617226030735985533)
  ·
    refine ⟨11219453856459761525994575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29918543617226030735985533 11219453856459761525994575)
    ·
      refine ⟨16829180784689642288991863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11219453856459761525994575 16829180784689642288991863)
      ·
        refine ⟨25243771177034463433487795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16829180784689642288991863 25243771177034463433487795)
        ·
          refine ⟨37865656765551695150231693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25243771177034463433487795 37865656765551695150231693)
          ·
            refine ⟨14199621287081885681336885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37865656765551695150231693 14199621287081885681336885)
            ·
              refine ⟨1331214495663926782625333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14199621287081885681336885 1331214495663926782625333)
              ·
                refine ⟨124801358968493135871125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1331214495663926782625333 124801358968493135871125)
                ·
                  rfl

theorem cell20_820293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_820293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820293 prefixEnd_820293 := by exact prefixLift 820293
  have htrace : WordTrace (prefixWord ++ tailWord_820293) baseStart_820293 baseEnd_820293 := by
    simpa [prefixWord, tailWord_820293, baseEnd_820293] using wordTrace_append hprefix tailTrace_820293
  have hstable : (prefixWord ++ tailWord_820293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820293).length < 2 ^ (prefixWord ++ tailWord_820293).sum := by decide
  have hdescent : baseEnd_820293 < baseStart_820293 := by decide
  rcases family_descends (prefixWord ++ tailWord_820293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820300 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_820300 : Nat := 118140960795 + 820300 * 2 ^ 59
def prefixEnd_820300 : Nat := 4983230072969 + 3 ^ 40 * 820300 * 2
def baseEnd_820300 : Nat := 374407271896218494380013

theorem tailTrace_820300 : CollatzResearch.WordTrace tailWord_820300 prefixEnd_820300 374407271896218494380013 := by
  unfold tailWord_820300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959399464100335465745177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19945865952133780620993569 14959399464100335465745177)
  ·
    refine ⟨11219549598075251599308883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14959399464100335465745177 11219549598075251599308883)
    ·
      refine ⟨16829324397112877398963325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11219549598075251599308883 16829324397112877398963325)
      ·
        refine ⟨6310996648917329024611247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16829324397112877398963325 6310996648917329024611247)
        ·
          refine ⟨9466494973375993536916871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310996648917329024611247 9466494973375993536916871)
          ·
            refine ⟨14199742460063990305375307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9466494973375993536916871 14199742460063990305375307)
            ·
              refine ⟨21299613690095985458062961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14199742460063990305375307 21299613690095985458062961)
              ·
                refine ⟨15974710267571989093547221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21299613690095985458062961 15974710267571989093547221)
                ·
                  refine ⟨374407271896218494380013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15974710267571989093547221 374407271896218494380013)
                  ·
                    rfl

theorem cell20_820300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_820300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820300 prefixEnd_820300 := by exact prefixLift 820300
  have htrace : WordTrace (prefixWord ++ tailWord_820300) baseStart_820300 baseEnd_820300 := by
    simpa [prefixWord, tailWord_820300, baseEnd_820300] using wordTrace_append hprefix tailTrace_820300
  have hstable : (prefixWord ++ tailWord_820300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820300).length < 2 ^ (prefixWord ++ tailWord_820300).sum := by decide
  have hdescent : baseEnd_820300 < baseStart_820300 := by decide
  rcases family_descends (prefixWord ++ tailWord_820300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820307 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_820307 : Nat := 118140960795 + 820307 * 2 ^ 59
def prefixEnd_820307 : Nat := 4983230072969 + 3 ^ 40 * 820307 * 2
def baseEnd_820307 : Nat := 374410466886957581146651

theorem tailTrace_820307 : CollatzResearch.WordTrace tailWord_820307 prefixEnd_820307 374410466886957581146651 := by
  unfold tailWord_820307
  simp only [CollatzResearch.WordTrace]
  refine ⟨29919054239175311126995175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19946036159450207417996783 29919054239175311126995175)
  ·
    refine ⟨44878581358762966690492763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29919054239175311126995175 44878581358762966690492763)
    ·
      refine ⟨67317872038144450035739145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44878581358762966690492763 67317872038144450035739145)
      ·
        refine ⟨50488404028608337526804359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67317872038144450035739145 50488404028608337526804359)
        ·
          refine ⟨75732606042912506290206539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50488404028608337526804359 75732606042912506290206539)
          ·
            refine ⟨113598909064368759435309809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75732606042912506290206539 113598909064368759435309809)
            ·
              refine ⟨85199181798276569576482357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113598909064368759435309809 85199181798276569576482357)
              ·
                refine ⟨7987423293588428397795221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85199181798276569576482357 7987423293588428397795221)
                ·
                  refine ⟨374410466886957581146651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7987423293588428397795221 374410466886957581146651)
                  ·
                    rfl

theorem cell20_820307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_820307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820307 prefixEnd_820307 := by exact prefixLift 820307
  have htrace : WordTrace (prefixWord ++ tailWord_820307) baseStart_820307 baseEnd_820307 := by
    simpa [prefixWord, tailWord_820307, baseEnd_820307] using wordTrace_append hprefix tailTrace_820307
  have hstable : (prefixWord ++ tailWord_820307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820307).length < 2 ^ (prefixWord ++ tailWord_820307).sum := by decide
  have hdescent : baseEnd_820307 < baseStart_820307 := by decide
  rcases family_descends (prefixWord ++ tailWord_820307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820334 : List Nat := [4, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_820334 : Nat := 118140960795 + 820334 * 2 ^ 59
def prefixEnd_820334 : Nat := 4983230072969 + 3 ^ 40 * 820334 * 2
def baseEnd_820334 : Nat := 374422790422665487246541

theorem tailTrace_820334 : CollatzResearch.WordTrace tailWord_820334 prefixEnd_820334 374422790422665487246541 := by
  unfold tailWord_820334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740004876259686842278507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19946692673384996492152037 3740004876259686842278507)
  ·
    refine ⟨5610007314389530263417761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3740004876259686842278507 5610007314389530263417761)
    ·
      refine ⟨4207505485792147697563321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5610007314389530263417761 4207505485792147697563321)
      ·
        refine ⟨3155629114344110773172491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4207505485792147697563321 3155629114344110773172491)
        ·
          refine ⟨4733443671516166159758737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155629114344110773172491 4733443671516166159758737)
          ·
            refine ⟨3550082753637124619819053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4733443671516166159758737 3550082753637124619819053)
            ·
              refine ⟨1331281032613921732432145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3550082753637124619819053 1331281032613921732432145)
              ·
                refine ⟨998460774460441299324109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331281032613921732432145 998460774460441299324109)
                ·
                  refine ⟨374422790422665487246541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998460774460441299324109 374422790422665487246541)
                  ·
                    rfl

theorem cell20_820334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_820334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820334 prefixEnd_820334 := by exact prefixLift 820334
  have htrace : WordTrace (prefixWord ++ tailWord_820334) baseStart_820334 baseEnd_820334 := by
    simpa [prefixWord, tailWord_820334, baseEnd_820334] using wordTrace_append hprefix tailTrace_820334
  have hstable : (prefixWord ++ tailWord_820334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820334).length < 2 ^ (prefixWord ++ tailWord_820334).sum := by decide
  have hdescent : baseEnd_820334 < baseStart_820334 := by decide
  rcases family_descends (prefixWord ++ tailWord_820334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820362 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_820362 : Nat := 118140960795 + 820362 * 2 ^ 59
def prefixEnd_820362 : Nat := 4983230072969 + 3 ^ 40 * 820362 * 2
def baseEnd_820362 : Nat := 374435570385621834313093

theorem tailTrace_820362 : CollatzResearch.WordTrace tailWord_820362 prefixEnd_820362 374435570385621834313093 := by
  unfold tailWord_820362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480265063494013880061835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19947373502650703680164893 7480265063494013880061835)
  ·
    refine ⟨11220397595241020820092753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480265063494013880061835 11220397595241020820092753)
    ·
      refine ⟨8415298196430765615069565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11220397595241020820092753 8415298196430765615069565)
      ·
        refine ⟨3155736823661537105651087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8415298196430765615069565 3155736823661537105651087)
        ·
          refine ⟨4733605235492305658476631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3155736823661537105651087 4733605235492305658476631)
          ·
            refine ⟨7100407853238458487714947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733605235492305658476631 7100407853238458487714947)
            ·
              refine ⟨10650611779857687731572421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100407853238458487714947 10650611779857687731572421)
              ·
                refine ⟨1996989708723316449669829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10650611779857687731572421 1996989708723316449669829)
                ·
                  refine ⟨374435570385621834313093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1996989708723316449669829 374435570385621834313093)
                  ·
                    rfl

theorem cell20_820362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_820362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820362 prefixEnd_820362 := by exact prefixLift 820362
  have htrace : WordTrace (prefixWord ++ tailWord_820362) baseStart_820362 baseEnd_820362 := by
    simpa [prefixWord, tailWord_820362, baseEnd_820362] using wordTrace_append hprefix tailTrace_820362
  have hstable : (prefixWord ++ tailWord_820362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820362).length < 2 ^ (prefixWord ++ tailWord_820362).sum := by decide
  have hdescent : baseEnd_820362 < baseStart_820362 := by decide
  rcases family_descends (prefixWord ++ tailWord_820362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820406 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_820406 : Nat := 118140960795 + 820406 * 2 ^ 59
def prefixEnd_820406 : Nat := 4983230072969 + 3 ^ 40 * 820406 * 2
def baseEnd_820406 : Nat := 374455653184553236846247

theorem tailTrace_820406 : CollatzResearch.WordTrace tailWord_820406 prefixEnd_820406 374455653184553236846247 := by
  unfold tailWord_820406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870166566613540689678067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19948443377211100689899381 1870166566613540689678067)
  ·
    refine ⟨2805249849920311034517101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1870166566613540689678067 2805249849920311034517101)
    ·
      refine ⟨1051968693720116637943913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2805249849920311034517101 1051968693720116637943913)
      ·
        refine ⟨788976520290087478457935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1051968693720116637943913 788976520290087478457935)
        ·
          refine ⟨1183464780435131217686903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788976520290087478457935 1183464780435131217686903)
          ·
            refine ⟨1775197170652696826530355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183464780435131217686903 1775197170652696826530355)
            ·
              refine ⟨2662795755979045239795533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775197170652696826530355 2662795755979045239795533)
              ·
                refine ⟨998548408492141964923325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2662795755979045239795533 998548408492141964923325)
                ·
                  refine ⟨374455653184553236846247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998548408492141964923325 374455653184553236846247)
                  ·
                    rfl

theorem cell20_820406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_820406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820406 prefixEnd_820406 := by exact prefixLift 820406
  have htrace : WordTrace (prefixWord ++ tailWord_820406) baseStart_820406 baseEnd_820406 := by
    simpa [prefixWord, tailWord_820406, baseEnd_820406] using wordTrace_append hprefix tailTrace_820406
  have hstable : (prefixWord ++ tailWord_820406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820406).length < 2 ^ (prefixWord ++ tailWord_820406).sum := by decide
  have hdescent : baseEnd_820406 < baseStart_820406 := by decide
  rcases family_descends (prefixWord ++ tailWord_820406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820407 : List Nat := [1, 1, 3, 1, 4, 1, 4, 5]
def baseStart_820407 : Nat := 118140960795 + 820407 * 2 ^ 59
def prefixEnd_820407 : Nat := 4983230072969 + 3 ^ 40 * 820407 * 2
def baseEnd_820407 : Nat := 124818703203933892604303

theorem tailTrace_820407 : CollatzResearch.WordTrace tailWord_820407 prefixEnd_820407 124818703203933892604303 := by
  unfold tailWord_820407
  simp only [CollatzResearch.WordTrace]
  refine ⟨29922701538813028205635475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19948467692542018803756983 29922701538813028205635475)
  ·
    refine ⟨44884052308219542308453213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29922701538813028205635475 44884052308219542308453213)
    ·
      refine ⟨16831519615582328365669955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44884052308219542308453213 16831519615582328365669955)
      ·
        refine ⟨25247279423373492548504933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831519615582328365669955 25247279423373492548504933)
        ·
          refine ⟨4733864891882529852844675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25247279423373492548504933 4733864891882529852844675)
          ·
            refine ⟨7100797337823794779267013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733864891882529852844675 7100797337823794779267013)
            ·
              refine ⟨1331399500841961521112565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7100797337823794779267013 1331399500841961521112565)
              ·
                refine ⟨124818703203933892604303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1331399500841961521112565 124818703203933892604303)
                ·
                  rfl

theorem cell20_820407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_820407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820407 prefixEnd_820407 := by exact prefixLift 820407
  have htrace : WordTrace (prefixWord ++ tailWord_820407) baseStart_820407 baseEnd_820407 := by
    simpa [prefixWord, tailWord_820407, baseEnd_820407] using wordTrace_append hprefix tailTrace_820407
  have hstable : (prefixWord ++ tailWord_820407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820407).length < 2 ^ (prefixWord ++ tailWord_820407).sum := by decide
  have hdescent : baseEnd_820407 < baseStart_820407 := by decide
  rcases family_descends (prefixWord ++ tailWord_820407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820421 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_820421 : Nat := 118140960795 + 820421 * 2 ^ 59
def prefixEnd_820421 : Nat := 4983230072969 + 3 ^ 40 * 820421 * 2
def baseEnd_820421 : Nat := 374462499593279851346185

theorem tailTrace_820421 : CollatzResearch.WordTrace tailWord_820421 prefixEnd_820421 374462499593279851346185 := by
  unfold tailWord_820421
  simp only [CollatzResearch.WordTrace]
  refine ⟨29923212160762308596645117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19948808107174872397763411 29923212160762308596645117)
  ·
    refine ⟨11221204560285865723741919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29923212160762308596645117 11221204560285865723741919)
    ·
      refine ⟨16831806840428798585612879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11221204560285865723741919 16831806840428798585612879)
      ·
        refine ⟨25247710260643197878419319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831806840428798585612879 25247710260643197878419319)
        ·
          refine ⟨37871565390964796817628979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25247710260643197878419319 37871565390964796817628979)
          ·
            refine ⟨56807348086447195226443469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37871565390964796817628979 56807348086447195226443469)
            ·
              refine ⟨21302755532417698209916301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56807348086447195226443469 21302755532417698209916301)
              ·
                refine ⟨7988533324656636828718613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21302755532417698209916301 7988533324656636828718613)
                ·
                  refine ⟨374462499593279851346185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7988533324656636828718613 374462499593279851346185)
                  ·
                    rfl

theorem cell20_820421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_820421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820421 prefixEnd_820421 := by exact prefixLift 820421
  have htrace : WordTrace (prefixWord ++ tailWord_820421) baseStart_820421 baseEnd_820421 := by
    simpa [prefixWord, tailWord_820421, baseEnd_820421] using wordTrace_append hprefix tailTrace_820421
  have hstable : (prefixWord ++ tailWord_820421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820421).length < 2 ^ (prefixWord ++ tailWord_820421).sum := by decide
  have hdescent : baseEnd_820421 < baseStart_820421 := by decide
  rcases family_descends (prefixWord ++ tailWord_820421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820445 : List Nat := [1, 4, 3, 2, 10]
def baseStart_820445 : Nat := 118140960795 + 820445 * 2 ^ 59
def prefixEnd_820445 : Nat := 4983230072969 + 3 ^ 40 * 820445 * 2
def baseEnd_820445 : Nat := 4623129059842499191927

theorem tailTrace_820445 : CollatzResearch.WordTrace tailWord_820445 prefixEnd_820445 4623129059842499191927 := by
  unfold tailWord_820445
  simp only [CollatzResearch.WordTrace]
  refine ⟨29924087512675360695518789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19949391675116907130345859 29924087512675360695518789)
  ·
    refine ⟨5610766408626630130409773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29924087512675360695518789 5610766408626630130409773)
    ·
      refine ⟨2104037403234986298903665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5610766408626630130409773 2104037403234986298903665)
      ·
        refine ⟨1578028052426239724177749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2104037403234986298903665 1578028052426239724177749)
        ·
          refine ⟨4623129059842499191927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1578028052426239724177749 4623129059842499191927)
          ·
            rfl

theorem cell20_820445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 10].length) (baseStart_820445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820445 prefixEnd_820445 := by exact prefixLift 820445
  have htrace : WordTrace (prefixWord ++ tailWord_820445) baseStart_820445 baseEnd_820445 := by
    simpa [prefixWord, tailWord_820445, baseEnd_820445] using wordTrace_append hprefix tailTrace_820445
  have hstable : (prefixWord ++ tailWord_820445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820445).length < 2 ^ (prefixWord ++ tailWord_820445).sum := by decide
  have hdescent : baseEnd_820445 < baseStart_820445 := by decide
  rcases family_descends (prefixWord ++ tailWord_820445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820452 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_820452 : Nat := 118140960795 + 820452 * 2 ^ 59
def prefixEnd_820452 : Nat := 4983230072969 + 3 ^ 40 * 820452 * 2
def baseEnd_820452 : Nat := 374476648837981521312725

theorem tailTrace_820452 : CollatzResearch.WordTrace tailWord_820452 prefixEnd_820452 374476648837981521312725 := by
  unfold tailWord_820452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14962171411825000445511805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19949561882433333927349073 14962171411825000445511805)
  ·
    refine ⟨5610814279434375167066927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14962171411825000445511805 5610814279434375167066927)
    ·
      refine ⟨8416221419151562750600391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5610814279434375167066927 8416221419151562750600391)
      ·
        refine ⟨12624332128727344125900587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8416221419151562750600391 12624332128727344125900587)
        ·
          refine ⟨18936498193091016188850881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12624332128727344125900587 18936498193091016188850881)
          ·
            refine ⟨14202373644818262141638161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18936498193091016188850881 14202373644818262141638161)
            ·
              refine ⟨10651780233613696606228621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14202373644818262141638161 10651780233613696606228621)
              ·
                refine ⟨3994417587605136227335733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10651780233613696606228621 3994417587605136227335733)
                ·
                  refine ⟨374476648837981521312725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3994417587605136227335733 374476648837981521312725)
                  ·
                    rfl

theorem cell20_820452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_820452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820452 prefixEnd_820452 := by exact prefixLift 820452
  have htrace : WordTrace (prefixWord ++ tailWord_820452) baseStart_820452 baseEnd_820452 := by
    simpa [prefixWord, tailWord_820452, baseEnd_820452] using wordTrace_append hprefix tailTrace_820452
  have hstable : (prefixWord ++ tailWord_820452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820452).length < 2 ^ (prefixWord ++ tailWord_820452).sum := by decide
  have hdescent : baseEnd_820452 < baseStart_820452 := by decide
  rcases family_descends (prefixWord ++ tailWord_820452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820490 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_820490 : Nat := 118140960795 + 820490 * 2 ^ 59
def prefixEnd_820490 : Nat := 4983230072969 + 3 ^ 40 * 820490 * 2
def baseEnd_820490 : Nat := 374493993073422278045903

theorem tailTrace_820490 : CollatzResearch.WordTrace tailWord_820490 prefixEnd_820490 374493993073422278045903 := by
  unfold tailWord_820490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481432199378083345226731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19950485865008222253937949 7481432199378083345226731)
  ·
    refine ⟨11222148299067125017840097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7481432199378083345226731 11222148299067125017840097)
    ·
      refine ⟨8416611224300343763380073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11222148299067125017840097 8416611224300343763380073)
      ·
        refine ⟨6312458418225257822535055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8416611224300343763380073 6312458418225257822535055)
        ·
          refine ⟨9468687627337886733802583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6312458418225257822535055 9468687627337886733802583)
          ·
            refine ⟨14203031441006830100703875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9468687627337886733802583 14203031441006830100703875)
            ·
              refine ⟨21304547161510245151055813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14203031441006830100703875 21304547161510245151055813)
              ·
                refine ⟨3994602592783170965822965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21304547161510245151055813 3994602592783170965822965)
                ·
                  refine ⟨374493993073422278045903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3994602592783170965822965 374493993073422278045903)
                  ·
                    rfl

theorem cell20_820490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_820490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820490 prefixEnd_820490 := by exact prefixLift 820490
  have htrace : WordTrace (prefixWord ++ tailWord_820490) baseStart_820490 baseEnd_820490 := by
    simpa [prefixWord, tailWord_820490, baseEnd_820490] using wordTrace_append hprefix tailTrace_820490
  have hstable : (prefixWord ++ tailWord_820490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820490).length < 2 ^ (prefixWord ++ tailWord_820490).sum := by decide
  have hdescent : baseEnd_820490 < baseStart_820490 := by decide
  rcases family_descends (prefixWord ++ tailWord_820490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820497 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_820497 : Nat := 118140960795 + 820497 * 2 ^ 59
def prefixEnd_820497 : Nat := 4983230072969 + 3 ^ 40 * 820497 * 2
def baseEnd_820497 : Nat := 374497188064161364812541

theorem tailTrace_820497 : CollatzResearch.WordTrace tailWord_820497 prefixEnd_820497 374497188064161364812541 := by
  unfold tailWord_820497
  simp only [CollatzResearch.WordTrace]
  refine ⟨29925984108486973576411745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19950656072324649050941163 29925984108486973576411745)
  ·
    refine ⟨22444488081365230182308809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29925984108486973576411745 22444488081365230182308809)
    ·
      refine ⟨16833366061023922636731607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22444488081365230182308809 16833366061023922636731607)
      ·
        refine ⟨25250049091535883955097411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16833366061023922636731607 25250049091535883955097411)
        ·
          refine ⟨37875073637303825932646117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25250049091535883955097411 37875073637303825932646117)
          ·
            refine ⟨7101576306994467362371147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37875073637303825932646117 7101576306994467362371147)
            ·
              refine ⟨10652364460491701043556721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101576306994467362371147 10652364460491701043556721)
              ·
                refine ⟨7989273345368775782667541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10652364460491701043556721 7989273345368775782667541)
                ·
                  refine ⟨374497188064161364812541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7989273345368775782667541 374497188064161364812541)
                  ·
                    rfl

theorem cell20_820497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_820497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820497 prefixEnd_820497 := by exact prefixLift 820497
  have htrace : WordTrace (prefixWord ++ tailWord_820497) baseStart_820497 baseEnd_820497 := by
    simpa [prefixWord, tailWord_820497, baseEnd_820497] using wordTrace_append hprefix tailTrace_820497
  have hstable : (prefixWord ++ tailWord_820497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820497).length < 2 ^ (prefixWord ++ tailWord_820497).sum := by decide
  have hdescent : baseEnd_820497 < baseStart_820497 := by decide
  rcases family_descends (prefixWord ++ tailWord_820497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820545 : List Nat := [1, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_820545 : Nat := 118140960795 + 820545 * 2 ^ 59
def prefixEnd_820545 : Nat := 4983230072969 + 3 ^ 40 * 820545 * 2
def baseEnd_820545 : Nat := 374519096572086531212345

theorem tailTrace_820545 : CollatzResearch.WordTrace tailWord_820545 prefixEnd_820545 374519096572086531212345 := by
  unfold tailWord_820545
  simp only [CollatzResearch.WordTrace]
  refine ⟨29927734812313077774159089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19951823208208718516106059 29927734812313077774159089)
  ·
    refine ⟨22445801109234808330619317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29927734812313077774159089 22445801109234808330619317)
    ·
      refine ⟨2104293853990763280995561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22445801109234808330619317 2104293853990763280995561)
      ·
        refine ⟨1578220390493072460746671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2104293853990763280995561 1578220390493072460746671)
        ·
          refine ⟨2367330585739608691120007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578220390493072460746671 2367330585739608691120007)
          ·
            refine ⟨3550995878609413036680011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367330585739608691120007 3550995878609413036680011)
            ·
              refine ⟨5326493817914119555020017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3550995878609413036680011 5326493817914119555020017)
              ·
                refine ⟨3994870363435589666265013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5326493817914119555020017 3994870363435589666265013)
                ·
                  refine ⟨374519096572086531212345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3994870363435589666265013 374519096572086531212345)
                  ·
                    rfl

theorem cell20_820545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_820545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820545 prefixEnd_820545 := by exact prefixLift 820545
  have htrace : WordTrace (prefixWord ++ tailWord_820545) baseStart_820545 baseEnd_820545 := by
    simpa [prefixWord, tailWord_820545, baseEnd_820545] using wordTrace_append hprefix tailTrace_820545
  have hstable : (prefixWord ++ tailWord_820545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820545).length < 2 ^ (prefixWord ++ tailWord_820545).sum := by decide
  have hdescent : baseEnd_820545 < baseStart_820545 := by decide
  rcases family_descends (prefixWord ++ tailWord_820545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820618 : List Nat := [3, 1, 2, 14]
def baseStart_820618 : Nat := 118140960795 + 820618 * 2 ^ 59
def prefixEnd_820618 : Nat := 4983230072969 + 3 ^ 40 * 820618 * 2
def baseEnd_820618 : Nat := 1541367966095566756291

theorem tailTrace_820618 : CollatzResearch.WordTrace tailWord_820618 prefixEnd_820618 1541367966095566756291 := by
  unfold tailWord_820618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482599335262152810391627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19953598227365740827711005 7482599335262152810391627)
  ·
    refine ⟨11223899002893229215587441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7482599335262152810391627 11223899002893229215587441)
    ·
      refine ⟨8417924252169921911690581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11223899002893229215587441 8417924252169921911690581)
      ·
        refine ⟨1541367966095566756291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8417924252169921911690581 1541367966095566756291)
        ·
          rfl

theorem cell20_820618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 14].length) (baseStart_820618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820618 prefixEnd_820618 := by exact prefixLift 820618
  have htrace : WordTrace (prefixWord ++ tailWord_820618) baseStart_820618 baseEnd_820618 := by
    simpa [prefixWord, tailWord_820618, baseEnd_820618] using wordTrace_append hprefix tailTrace_820618
  have hstable : (prefixWord ++ tailWord_820618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820618).length < 2 ^ (prefixWord ++ tailWord_820618).sum := by decide
  have hdescent : baseEnd_820618 < baseStart_820618 := by decide
  rcases family_descends (prefixWord ++ tailWord_820618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820676 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 3]
def baseStart_820676 : Nat := 118140960795 + 820676 * 2 ^ 59
def prefixEnd_820676 : Nat := 4983230072969 + 3 ^ 40 * 820676 * 2
def baseEnd_820676 : Nat := 374578888541632297845143

theorem tailTrace_820676 : CollatzResearch.WordTrace tailWord_820676 prefixEnd_820676 374578888541632297845143 := by
  unfold tailWord_820676
  simp only [CollatzResearch.WordTrace]
  refine ⟨14966256387419243573588941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19955008516558991431451921 14966256387419243573588941)
  ·
    refine ⟨5612346145282216340095853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14966256387419243573588941 5612346145282216340095853)
    ·
      refine ⟨2104629804480831127535945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5612346145282216340095853 2104629804480831127535945)
      ·
        refine ⟨1578472353360623345651959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2104629804480831127535945 1578472353360623345651959)
        ·
          refine ⟨2367708530040935018477939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578472353360623345651959 2367708530040935018477939)
          ·
            refine ⟨3551562795061402527716909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367708530040935018477939 3551562795061402527716909)
            ·
              refine ⟨1331836048148025947893841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3551562795061402527716909 1331836048148025947893841)
              ·
                refine ⟨998877036111019460920381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1331836048148025947893841 998877036111019460920381)
                ·
                  refine ⟨374578888541632297845143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 998877036111019460920381 374578888541632297845143)
                  ·
                    rfl

theorem cell20_820676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_820676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820676 prefixEnd_820676 := by exact prefixLift 820676
  have htrace : WordTrace (prefixWord ++ tailWord_820676) baseStart_820676 baseEnd_820676 := by
    simpa [prefixWord, tailWord_820676, baseEnd_820676] using wordTrace_append hprefix tailTrace_820676
  have hstable : (prefixWord ++ tailWord_820676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820676).length < 2 ^ (prefixWord ++ tailWord_820676).sum := by decide
  have hdescent : baseEnd_820676 < baseStart_820676 := by decide
  rcases family_descends (prefixWord ++ tailWord_820676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820680 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_820680 : Nat := 118140960795 + 820680 * 2 ^ 59
def prefixEnd_820680 : Nat := 4983230072969 + 3 ^ 40 * 820680 * 2
def baseEnd_820680 : Nat := 374580714250626061711793

theorem tailTrace_820680 : CollatzResearch.WordTrace tailWord_820680 prefixEnd_820680 374580714250626061711793 := by
  unfold tailWord_820680
  simp only [CollatzResearch.WordTrace]
  refine ⟨14966329333411997915161747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19955105777882663886882329 14966329333411997915161747)
  ·
    refine ⟨22449494000117996872742621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14966329333411997915161747 22449494000117996872742621)
    ·
      refine ⟨8418560250044248827278483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22449494000117996872742621 8418560250044248827278483)
      ·
        refine ⟨12627840375066373240917725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8418560250044248827278483 12627840375066373240917725)
        ·
          refine ⟨4735440140649889965344147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12627840375066373240917725 4735440140649889965344147)
          ·
            refine ⟨7103160210974834948016221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735440140649889965344147 7103160210974834948016221)
            ·
              refine ⟨2663685079115563105506083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7103160210974834948016221 2663685079115563105506083)
              ·
                refine ⟨3995527618673344658259125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2663685079115563105506083 3995527618673344658259125)
                ·
                  refine ⟨374580714250626061711793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3995527618673344658259125 374580714250626061711793)
                  ·
                    rfl

theorem cell20_820680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_820680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820680 prefixEnd_820680 := by exact prefixLift 820680
  have htrace : WordTrace (prefixWord ++ tailWord_820680) baseStart_820680 baseEnd_820680 := by
    simpa [prefixWord, tailWord_820680, baseEnd_820680] using wordTrace_append hprefix tailTrace_820680
  have hstable : (prefixWord ++ tailWord_820680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820680).length < 2 ^ (prefixWord ++ tailWord_820680).sum := by decide
  have hdescent : baseEnd_820680 < baseStart_820680 := by decide
  rcases family_descends (prefixWord ++ tailWord_820680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820687 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 4]
def baseStart_820687 : Nat := 118140960795 + 820687 * 2 ^ 59
def prefixEnd_820687 : Nat := 4983230072969 + 3 ^ 40 * 820687 * 2
def baseEnd_820687 : Nat := 374583909241365148478431

theorem tailTrace_820687 : CollatzResearch.WordTrace tailWord_820687 prefixEnd_820687 374583909241365148478431 := by
  unfold tailWord_820687
  simp only [CollatzResearch.WordTrace]
  refine ⟨29932913977798636025828315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19955275985199090683885543 29932913977798636025828315)
  ·
    refine ⟨44899370966697954038742473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29932913977798636025828315 44899370966697954038742473)
    ·
      refine ⟨33674528225023465529056855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44899370966697954038742473 33674528225023465529056855)
      ·
        refine ⟨50511792337535198293585283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33674528225023465529056855 50511792337535198293585283)
        ·
          refine ⟨75767688506302797440377925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50511792337535198293585283 75767688506302797440377925)
          ·
            refine ⟨14206441594931774520070861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75767688506302797440377925 14206441594931774520070861)
            ·
              refine ⟨5327415598099415445026573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14206441594931774520070861 5327415598099415445026573)
              ·
                refine ⟨1997780849287280791884965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5327415598099415445026573 1997780849287280791884965)
                ·
                  refine ⟨374583909241365148478431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997780849287280791884965 374583909241365148478431)
                  ·
                    rfl

theorem cell20_820687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_820687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820687 prefixEnd_820687 := by exact prefixLift 820687
  have htrace : WordTrace (prefixWord ++ tailWord_820687) baseStart_820687 baseEnd_820687 := by
    simpa [prefixWord, tailWord_820687, baseEnd_820687] using wordTrace_append hprefix tailTrace_820687
  have hstable : (prefixWord ++ tailWord_820687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820687).length < 2 ^ (prefixWord ++ tailWord_820687).sum := by decide
  have hdescent : baseEnd_820687 < baseStart_820687 := by decide
  rcases family_descends (prefixWord ++ tailWord_820687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820711 : List Nat := [1, 1, 5, 2, 1, 3, 1, 6]
def baseStart_820711 : Nat := 118140960795 + 820711 * 2 ^ 59
def prefixEnd_820711 : Nat := 4983230072969 + 3 ^ 40 * 820711 * 2
def baseEnd_820711 : Nat := 124864954498442577226111

theorem tailTrace_820711 : CollatzResearch.WordTrace tailWord_820711 prefixEnd_820711 124864954498442577226111 := by
  unfold tailWord_820711
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933789329711688124701987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19955859553141125416467991 29933789329711688124701987)
  ·
    refine ⟨44900683994567532187052981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29933789329711688124701987 44900683994567532187052981)
    ·
      refine ⟨4209439124490706142536217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44900683994567532187052981 4209439124490706142536217)
      ·
        refine ⟨3157079343368029606902163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4209439124490706142536217 3157079343368029606902163)
        ·
          refine ⟨4735619015052044410353245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157079343368029606902163 4735619015052044410353245)
          ·
            refine ⟨1775857130644516653882467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4735619015052044410353245 1775857130644516653882467)
            ·
              refine ⟨2663785695966774980823701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775857130644516653882467 2663785695966774980823701)
              ·
                refine ⟨124864954498442577226111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2663785695966774980823701 124864954498442577226111)
                ·
                  rfl

theorem cell20_820711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_820711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820711 prefixEnd_820711 := by exact prefixLift 820711
  have htrace : WordTrace (prefixWord ++ tailWord_820711) baseStart_820711 baseEnd_820711 := by
    simpa [prefixWord, tailWord_820711, baseEnd_820711] using wordTrace_append hprefix tailTrace_820711
  have hstable : (prefixWord ++ tailWord_820711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820711).length < 2 ^ (prefixWord ++ tailWord_820711).sum := by decide
  have hdescent : baseEnd_820711 < baseStart_820711 := by decide
  rcases family_descends (prefixWord ++ tailWord_820711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820717 : List Nat := [1, 5, 1, 3, 2, 2, 1, 3, 2]
def baseStart_820717 : Nat := 118140960795 + 820717 * 2 ^ 59
def prefixEnd_820717 : Nat := 4983230072969 + 3 ^ 40 * 820717 * 2
def baseEnd_820717 : Nat := 374597602058818377478309

theorem tailTrace_820717 : CollatzResearch.WordTrace tailWord_820717 prefixEnd_820717 374597602058818377478309 := by
  unfold tailWord_820717
  simp only [CollatzResearch.WordTrace]
  refine ⟨29934008167689951149420405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19956005445126634099613603 29934008167689951149420405)
  ·
    refine ⟨2806313265720932920258163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29934008167689951149420405 2806313265720932920258163)
    ·
      refine ⟨4209469898581399380387245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2806313265720932920258163 4209469898581399380387245)
      ·
        refine ⟨1578551211968024767645217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4209469898581399380387245 1578551211968024767645217)
        ·
          refine ⟨1183913408976018575733913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1578551211968024767645217 1183913408976018575733913)
          ·
            refine ⟨887935056732013931800435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1183913408976018575733913 887935056732013931800435)
            ·
              refine ⟨1331902585098020897700653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887935056732013931800435 1331902585098020897700653)
              ·
                refine ⟨499463469411757836637745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1331902585098020897700653 499463469411757836637745)
                ·
                  refine ⟨374597602058818377478309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499463469411757836637745 374597602058818377478309)
                  ·
                    rfl

theorem cell20_820717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_820717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820717 prefixEnd_820717 := by exact prefixLift 820717
  have htrace : WordTrace (prefixWord ++ tailWord_820717) baseStart_820717 baseEnd_820717 := by
    simpa [prefixWord, tailWord_820717, baseEnd_820717] using wordTrace_append hprefix tailTrace_820717
  have hstable : (prefixWord ++ tailWord_820717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820717).length < 2 ^ (prefixWord ++ tailWord_820717).sum := by decide
  have hdescent : baseEnd_820717 < baseStart_820717 := by decide
  rcases family_descends (prefixWord ++ tailWord_820717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820718 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_820718 : Nat := 118140960795 + 820718 * 2 ^ 59
def prefixEnd_820718 : Nat := 4983230072969 + 3 ^ 40 * 820718 * 2
def baseEnd_820718 : Nat := 374598058486066818444971

theorem tailTrace_820718 : CollatzResearch.WordTrace tailWord_820718 prefixEnd_820718 374598058486066818444971 := by
  unfold tailWord_820718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741755580085791040025851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19956029760457552213471205 3741755580085791040025851)
  ·
    refine ⟨5612633370128686560038777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3741755580085791040025851 5612633370128686560038777)
    ·
      refine ⟨4209475027596514920029083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5612633370128686560038777 4209475027596514920029083)
      ·
        refine ⟨6314212541394772380043625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209475027596514920029083 6314212541394772380043625)
        ·
          refine ⟨4735659406046079285032719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6314212541394772380043625 4735659406046079285032719)
          ·
            refine ⟨7103489109069118927549079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735659406046079285032719 7103489109069118927549079)
            ·
              refine ⟨10655233663603678391323619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103489109069118927549079 10655233663603678391323619)
              ·
                refine ⟨15982850495405517586985429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10655233663603678391323619 15982850495405517586985429)
                ·
                  refine ⟨374598058486066818444971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15982850495405517586985429 374598058486066818444971)
                  ·
                    rfl

theorem cell20_820718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_820718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820718 prefixEnd_820718 := by exact prefixLift 820718
  have htrace : WordTrace (prefixWord ++ tailWord_820718) baseStart_820718 baseEnd_820718 := by
    simpa [prefixWord, tailWord_820718, baseEnd_820718] using wordTrace_append hprefix tailTrace_820718
  have hstable : (prefixWord ++ tailWord_820718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820718).length < 2 ^ (prefixWord ++ tailWord_820718).sum := by decide
  have hdescent : baseEnd_820718 < baseStart_820718 := by decide
  rcases family_descends (prefixWord ++ tailWord_820718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820721 : List Nat := [1, 2, 2, 2, 3, 2, 3, 3, 2]
def baseStart_820721 : Nat := 118140960795 + 820721 * 2 ^ 59
def prefixEnd_820721 : Nat := 4983230072969 + 3 ^ 40 * 820721 * 2
def baseEnd_820721 : Nat := 374599427767812141344959

theorem tailTrace_820721 : CollatzResearch.WordTrace tailWord_820721 prefixEnd_820721 374599427767812141344959 := by
  unfold tailWord_820721
  simp only [CollatzResearch.WordTrace]
  refine ⟨29934154059675459832566017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19956102706450306555044011 29934154059675459832566017)
  ·
    refine ⟨22450615544756594874424513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29934154059675459832566017 22450615544756594874424513)
    ·
      refine ⟨16837961658567446155818385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22450615544756594874424513 16837961658567446155818385)
      ·
        refine ⟨12628471243925584616863789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16837961658567446155818385 12628471243925584616863789)
        ·
          refine ⟨4735676716472094231323921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12628471243925584616863789 4735676716472094231323921)
          ·
            refine ⟨3551757537354070673492941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735676716472094231323921 3551757537354070673492941)
            ·
              refine ⟨1331909076507776502559853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3551757537354070673492941 1331909076507776502559853)
              ·
                refine ⟨499465903690416188459945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1331909076507776502559853 499465903690416188459945)
                ·
                  refine ⟨374599427767812141344959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499465903690416188459945 374599427767812141344959)
                  ·
                    rfl

theorem cell20_820721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 2].length) (baseStart_820721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820721 prefixEnd_820721 := by exact prefixLift 820721
  have htrace : WordTrace (prefixWord ++ tailWord_820721) baseStart_820721 baseEnd_820721 := by
    simpa [prefixWord, tailWord_820721, baseEnd_820721] using wordTrace_append hprefix tailTrace_820721
  have hstable : (prefixWord ++ tailWord_820721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820721).length < 2 ^ (prefixWord ++ tailWord_820721).sum := by decide
  have hdescent : baseEnd_820721 < baseStart_820721 := by decide
  rcases family_descends (prefixWord ++ tailWord_820721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820732 : List Nat := [2, 2, 2, 1, 2, 1, 10]
def baseStart_820732 : Nat := 118140960795 + 820732 * 2 ^ 59
def prefixEnd_820732 : Nat := 4983230072969 + 3 ^ 40 * 820732 * 2
def baseEnd_820732 : Nat := 41622716496393887997583

theorem tailTrace_820732 : CollatzResearch.WordTrace tailWord_820732 prefixEnd_820732 41622716496393887997583 := by
  unfold tailWord_820732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14967277631317804355608225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19956370175090405807477633 14967277631317804355608225)
  ·
    refine ⟨11225458223488353266706169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14967277631317804355608225 11225458223488353266706169)
    ·
      refine ⟨8419093667616264950029627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11225458223488353266706169 8419093667616264950029627)
      ·
        refine ⟨12628640501424397425044441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8419093667616264950029627 12628640501424397425044441)
        ·
          refine ⟨9471480376068298068783331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12628640501424397425044441 9471480376068298068783331)
          ·
            refine ⟨14207220564102447103174997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9471480376068298068783331 14207220564102447103174997)
            ·
              refine ⟨41622716496393887997583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14207220564102447103174997 41622716496393887997583)
              ·
                rfl

theorem cell20_820732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 10].length) (baseStart_820732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820732 prefixEnd_820732 := by exact prefixLift 820732
  have htrace : WordTrace (prefixWord ++ tailWord_820732) baseStart_820732 baseEnd_820732 := by
    simpa [prefixWord, tailWord_820732, baseEnd_820732] using wordTrace_append hprefix tailTrace_820732
  have hstable : (prefixWord ++ tailWord_820732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820732).length < 2 ^ (prefixWord ++ tailWord_820732).sum := by decide
  have hdescent : baseEnd_820732 < baseStart_820732 := by decide
  rcases family_descends (prefixWord ++ tailWord_820732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820734 : List Nat := [4, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_820734 : Nat := 118140960795 + 820734 * 2 ^ 59
def prefixEnd_820734 : Nat := 4983230072969 + 3 ^ 40 * 820734 * 2
def baseEnd_820734 : Nat := 374605361322041873911573

theorem tailTrace_820734 : CollatzResearch.WordTrace tailWord_820734 prefixEnd_820734 374605361322041873911573 := by
  unfold tailWord_820734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741828526078545381598657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19956418805752242035192837 3741828526078545381598657)
  ·
    refine ⟨2806371394558909036198993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3741828526078545381598657 2806371394558909036198993)
    ·
      refine ⟨2104778545919181777149245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2806371394558909036198993 2104778545919181777149245)
      ·
        refine ⟨789291954719693166430967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2104778545919181777149245 789291954719693166430967)
        ·
          refine ⟨1183937932079539749646451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789291954719693166430967 1183937932079539749646451)
          ·
            refine ⟨1775906898119309624469677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1183937932079539749646451 1775906898119309624469677)
            ·
              refine ⟨665965086794741109176129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1775906898119309624469677 665965086794741109176129)
              ·
                refine ⟨499473815096055831882097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 665965086794741109176129 499473815096055831882097)
                ·
                  refine ⟨374605361322041873911573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499473815096055831882097 374605361322041873911573)
                  ·
                    rfl

theorem cell20_820734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_820734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820734 prefixEnd_820734 := by exact prefixLift 820734
  have htrace : WordTrace (prefixWord ++ tailWord_820734) baseStart_820734 baseEnd_820734 := by
    simpa [prefixWord, tailWord_820734, baseEnd_820734] using wordTrace_append hprefix tailTrace_820734
  have hstable : (prefixWord ++ tailWord_820734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820734).length < 2 ^ (prefixWord ++ tailWord_820734).sum := by decide
  have hdescent : baseEnd_820734 < baseStart_820734 := by decide
  rcases family_descends (prefixWord ++ tailWord_820734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820738 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_820738 : Nat := 118140960795 + 820738 * 2 ^ 59
def prefixEnd_820738 : Nat := 4983230072969 + 3 ^ 40 * 820738 * 2
def baseEnd_820738 : Nat := 374607187031035637778223

theorem tailTrace_820738 : CollatzResearch.WordTrace tailWord_820738 prefixEnd_820738 374607187031035637778223 := by
  unfold tailWord_820738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7483693525153467933983717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19956516067075914490623245 7483693525153467933983717)
  ·
    refine ⟨1403192535966275237621947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7483693525153467933983717 1403192535966275237621947)
    ·
      refine ⟨2104788803949412856432921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403192535966275237621947 2104788803949412856432921)
      ·
        refine ⟨1578591602962059642324691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2104788803949412856432921 1578591602962059642324691)
        ·
          refine ⟨2367887404443089463487037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578591602962059642324691 2367887404443089463487037)
          ·
            refine ⟨887957776666158548807639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2367887404443089463487037 887957776666158548807639)
            ·
              refine ⟨1331936664999237823211459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 887957776666158548807639 1331936664999237823211459)
              ·
                refine ⟨1997904997498856734817189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1331936664999237823211459 1997904997498856734817189)
                ·
                  refine ⟨374607187031035637778223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1997904997498856734817189 374607187031035637778223)
                  ·
                    rfl

theorem cell20_820738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_820738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820738 prefixEnd_820738 := by exact prefixLift 820738
  have htrace : WordTrace (prefixWord ++ tailWord_820738) baseStart_820738 baseEnd_820738 := by
    simpa [prefixWord, tailWord_820738, baseEnd_820738] using wordTrace_append hprefix tailTrace_820738
  have hstable : (prefixWord ++ tailWord_820738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820738).length < 2 ^ (prefixWord ++ tailWord_820738).sum := by decide
  have hdescent : baseEnd_820738 < baseStart_820738 := by decide
  rcases family_descends (prefixWord ++ tailWord_820738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820815 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 7]
def baseStart_820815 : Nat := 118140960795 + 820815 * 2 ^ 59
def prefixEnd_820815 : Nat := 4983230072969 + 3 ^ 40 * 820815 * 2
def baseEnd_820815 : Nat := 374642331929165592211241

theorem tailTrace_820815 : CollatzResearch.WordTrace tailWord_820815 prefixEnd_820815 374642331929165592211241 := by
  unfold tailWord_820815
  simp only [CollatzResearch.WordTrace]
  refine ⟨29937582521334913886487899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19958388347556609257658599 29937582521334913886487899)
  ·
    refine ⟨44906373782002370829731849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29937582521334913886487899 44906373782002370829731849)
    ·
      refine ⟨33679780336501778122298887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44906373782002370829731849 33679780336501778122298887)
      ·
        refine ⟨50519670504752667183448331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33679780336501778122298887 50519670504752667183448331)
        ·
          refine ⟨75779505757129000775172497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50519670504752667183448331 75779505757129000775172497)
          ·
            refine ⟨56834629317846750581379373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75779505757129000775172497 56834629317846750581379373)
            ·
              refine ⟨21312985994192531468017265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56834629317846750581379373 21312985994192531468017265)
              ·
                refine ⟨15984739495644398601012949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21312985994192531468017265 15984739495644398601012949)
                ·
                  refine ⟨374642331929165592211241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15984739495644398601012949 374642331929165592211241)
                  ·
                    rfl

theorem cell20_820815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_820815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820815 prefixEnd_820815 := by exact prefixLift 820815
  have htrace : WordTrace (prefixWord ++ tailWord_820815) baseStart_820815 baseEnd_820815 := by
    simpa [prefixWord, tailWord_820815, baseEnd_820815] using wordTrace_append hprefix tailTrace_820815
  have hstable : (prefixWord ++ tailWord_820815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820815).length < 2 ^ (prefixWord ++ tailWord_820815).sum := by decide
  have hdescent : baseEnd_820815 < baseStart_820815 := by decide
  rcases family_descends (prefixWord ++ tailWord_820815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820818 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_820818 : Nat := 118140960795 + 820818 * 2 ^ 59
def prefixEnd_820818 : Nat := 4983230072969 + 3 ^ 40 * 820818 * 2
def baseEnd_820818 : Nat := 374643701210910915111229

theorem tailTrace_820818 : CollatzResearch.WordTrace tailWord_820818 prefixEnd_820818 374643701210910915111229 := by
  unfold tailWord_820818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7484422985081011349711777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19958461293549363599231405 7484422985081011349711777)
  ·
    refine ⟨5613317238810758512283833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7484422985081011349711777 5613317238810758512283833)
    ·
      refine ⟨4209987929108068884212875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5613317238810758512283833 4209987929108068884212875)
      ·
        refine ⟨6314981893662103326319313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209987929108068884212875 6314981893662103326319313)
        ·
          refine ⟨4736236420246577494739485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6314981893662103326319313 4736236420246577494739485)
          ·
            refine ⟨1776088657592466560527307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4736236420246577494739485 1776088657592466560527307)
            ·
              refine ⟨2664132986388699840790961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776088657592466560527307 2664132986388699840790961)
              ·
                refine ⟨1998099739791524880593221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2664132986388699840790961 1998099739791524880593221)
                ·
                  refine ⟨374643701210910915111229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1998099739791524880593221 374643701210910915111229)
                  ·
                    rfl

theorem cell20_820818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_820818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820818 prefixEnd_820818 := by exact prefixLift 820818
  have htrace : WordTrace (prefixWord ++ tailWord_820818) baseStart_820818 baseEnd_820818 := by
    simpa [prefixWord, tailWord_820818, baseEnd_820818] using wordTrace_append hprefix tailTrace_820818
  have hstable : (prefixWord ++ tailWord_820818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820818).length < 2 ^ (prefixWord ++ tailWord_820818).sum := by decide
  have hdescent : baseEnd_820818 < baseStart_820818 := by decide
  rcases family_descends (prefixWord ++ tailWord_820818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820835 : List Nat := [1, 1, 1, 5, 1, 4, 2, 3, 2]
def baseStart_820835 : Nat := 118140960795 + 820835 * 2 ^ 59
def prefixEnd_820835 : Nat := 4983230072969 + 3 ^ 40 * 820835 * 2
def baseEnd_820835 : Nat := 374651460474134411544493

theorem tailTrace_820835 : CollatzResearch.WordTrace tailWord_820835 prefixEnd_820835 374651460474134411544493 := by
  unfold tailWord_820835
  simp only [CollatzResearch.WordTrace]
  refine ⟨29938311981262457302215959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19958874654174971534810639 29938311981262457302215959)
  ·
    refine ⟨44907467971893685953323939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29938311981262457302215959 44907467971893685953323939)
    ·
      refine ⟨67361201957840528929985909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44907467971893685953323939 67361201957840528929985909)
      ·
        refine ⟨6315112683547549587186179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67361201957840528929985909 6315112683547549587186179)
        ·
          refine ⟨9472669025321324380779269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315112683547549587186179 9472669025321324380779269)
          ·
            refine ⟨1776125442247748321396113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9472669025321324380779269 1776125442247748321396113)
            ·
              refine ⟨1332094081685811241047085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776125442247748321396113 1332094081685811241047085)
              ·
                refine ⟨499535280632179215392657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1332094081685811241047085 499535280632179215392657)
                ·
                  refine ⟨374651460474134411544493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499535280632179215392657 374651460474134411544493)
                  ·
                    rfl

theorem cell20_820835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 3, 2].length) (baseStart_820835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820835 prefixEnd_820835 := by exact prefixLift 820835
  have htrace : WordTrace (prefixWord ++ tailWord_820835) baseStart_820835 baseEnd_820835 := by
    simpa [prefixWord, tailWord_820835, baseEnd_820835] using wordTrace_append hprefix tailTrace_820835
  have hstable : (prefixWord ++ tailWord_820835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820835).length < 2 ^ (prefixWord ++ tailWord_820835).sum := by decide
  have hdescent : baseEnd_820835 < baseStart_820835 := by decide
  rcases family_descends (prefixWord ++ tailWord_820835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820845 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 3]
def baseStart_820845 : Nat := 118140960795 + 820845 * 2 ^ 59
def prefixEnd_820845 : Nat := 4983230072969 + 3 ^ 40 * 820845 * 2
def baseEnd_820845 : Nat := 374656024746618821211119

theorem tailTrace_820845 : CollatzResearch.WordTrace tailWord_820845 prefixEnd_820845 374656024746618821211119 := by
  unfold tailWord_820845
  simp only [CollatzResearch.WordTrace]
  refine ⟨29938676711226229010079989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19959117807484152673386659 29938676711226229010079989)
  ·
    refine ⟨2806750941677458969694999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29938676711226229010079989 2806750941677458969694999)
    ·
      refine ⟨4210126412516188454542499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2806750941677458969694999 4210126412516188454542499)
      ·
        refine ⟨6315189618774282681813749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210126412516188454542499 6315189618774282681813749)
        ·
          refine ⟨592049026760089001420039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6315189618774282681813749 592049026760089001420039)
          ·
            refine ⟨888073540140133502130059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592049026760089001420039 888073540140133502130059)
            ·
              refine ⟨1332110310210200253195089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888073540140133502130059 1332110310210200253195089)
              ·
                refine ⟨999082732657650189896317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332110310210200253195089 999082732657650189896317)
                ·
                  refine ⟨374656024746618821211119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999082732657650189896317 374656024746618821211119)
                  ·
                    rfl

theorem cell20_820845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_820845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820845 prefixEnd_820845 := by exact prefixLift 820845
  have htrace : WordTrace (prefixWord ++ tailWord_820845) baseStart_820845 baseEnd_820845 := by
    simpa [prefixWord, tailWord_820845, baseEnd_820845] using wordTrace_append hprefix tailTrace_820845
  have hstable : (prefixWord ++ tailWord_820845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820845).length < 2 ^ (prefixWord ++ tailWord_820845).sum := by decide
  have hdescent : baseEnd_820845 < baseStart_820845 := by decide
  rcases family_descends (prefixWord ++ tailWord_820845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820911 : List Nat := [1, 1, 2, 1, 2, 4, 5, 2, 2]
def baseStart_820911 : Nat := 118140960795 + 820911 * 2 ^ 59
def prefixEnd_820911 : Nat := 4983230072969 + 3 ^ 40 * 820911 * 2
def baseEnd_820911 : Nat := 374686148945015925010849

theorem tailTrace_820911 : CollatzResearch.WordTrace tailWord_820911 prefixEnd_820911 374686148945015925010849 := by
  unfold tailWord_820911
  simp only [CollatzResearch.WordTrace]
  refine ⟨29941083928987122281982587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19960722619324748187988391 29941083928987122281982587)
  ·
    refine ⟨44911625893480683422973881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29941083928987122281982587 44911625893480683422973881)
    ·
      refine ⟨33683719420110512567230411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44911625893480683422973881 33683719420110512567230411)
      ·
        refine ⟨50525579130165768850845617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33683719420110512567230411 50525579130165768850845617)
        ·
          refine ⟨37894184347624326638134213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50525579130165768850845617 37894184347624326638134213)
          ·
            refine ⟨7105159565179561244650165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37894184347624326638134213 7105159565179561244650165)
            ·
              refine ⟨666108709235583866685953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7105159565179561244650165 666108709235583866685953)
              ·
                refine ⟨499581531926687900014465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666108709235583866685953 499581531926687900014465)
                ·
                  refine ⟨374686148945015925010849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499581531926687900014465 374686148945015925010849)
                  ·
                    rfl

theorem cell20_820911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 2, 2].length) (baseStart_820911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820911 prefixEnd_820911 := by exact prefixLift 820911
  have htrace : WordTrace (prefixWord ++ tailWord_820911) baseStart_820911 baseEnd_820911 := by
    simpa [prefixWord, tailWord_820911, baseEnd_820911] using wordTrace_append hprefix tailTrace_820911
  have hstable : (prefixWord ++ tailWord_820911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820911).length < 2 ^ (prefixWord ++ tailWord_820911).sum := by decide
  have hdescent : baseEnd_820911 < baseStart_820911 := by decide
  rcases family_descends (prefixWord ++ tailWord_820911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820918 : List Nat := [5, 1, 3, 1, 1, 1, 1, 7]
def baseStart_820918 : Nat := 118140960795 + 820918 * 2 ^ 59
def prefixEnd_820918 : Nat := 4983230072969 + 3 ^ 40 * 820918 * 2
def baseEnd_820918 : Nat := 124896447978585003925829

theorem tailTrace_820918 : CollatzResearch.WordTrace tailWord_820918 prefixEnd_820918 124896447978585003925829 := by
  unfold tailWord_820918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871333702497610154842963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19960892826641174984991605 1871333702497610154842963)
  ·
    refine ⟨2807000553746415232264445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871333702497610154842963 2807000553746415232264445)
    ·
      refine ⟨1052625207654905712099167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2807000553746415232264445 1052625207654905712099167)
      ·
        refine ⟨1578937811482358568148751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052625207654905712099167 1578937811482358568148751)
        ·
          refine ⟨2368406717223537852223127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1578937811482358568148751 2368406717223537852223127)
          ·
            refine ⟨3552610075835306778334691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368406717223537852223127 3552610075835306778334691)
            ·
              refine ⟨5328915113752960167502037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552610075835306778334691 5328915113752960167502037)
              ·
                refine ⟨124896447978585003925829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5328915113752960167502037 124896447978585003925829)
                ·
                  rfl

theorem cell20_820918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_820918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820918 prefixEnd_820918 := by exact prefixLift 820918
  have htrace : WordTrace (prefixWord ++ tailWord_820918) baseStart_820918 baseEnd_820918 := by
    simpa [prefixWord, tailWord_820918, baseEnd_820918] using wordTrace_append hprefix tailTrace_820918
  have hstable : (prefixWord ++ tailWord_820918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820918).length < 2 ^ (prefixWord ++ tailWord_820918).sum := by decide
  have hdescent : baseEnd_820918 < baseStart_820918 := by decide
  rcases family_descends (prefixWord ++ tailWord_820918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820922 : List Nat := [3, 1, 1, 1, 2, 4, 1, 7]
def baseStart_820922 : Nat := 118140960795 + 820922 * 2 ^ 59
def prefixEnd_820922 : Nat := 4983230072969 + 3 ^ 40 * 820922 * 2
def baseEnd_820922 : Nat := 124897056548249591881379

theorem tailTrace_820922 : CollatzResearch.WordTrace tailWord_820922 prefixEnd_820922 124897056548249591881379 := by
  unfold tailWord_820922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485371282986817790158255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19960990087964847440422013 7485371282986817790158255)
  ·
    refine ⟨11228056924480226685237383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7485371282986817790158255 11228056924480226685237383)
    ·
      refine ⟨16842085386720340027856075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11228056924480226685237383 16842085386720340027856075)
      ·
        refine ⟨25263128080080510041784113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16842085386720340027856075 25263128080080510041784113)
        ·
          refine ⟨18947346060060382531338085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25263128080080510041784113 18947346060060382531338085)
          ·
            refine ⟨3552627386261321724625891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18947346060060382531338085 3552627386261321724625891)
            ·
              refine ⟨5328941079391982586938837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3552627386261321724625891 5328941079391982586938837)
              ·
                refine ⟨124897056548249591881379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5328941079391982586938837 124897056548249591881379)
                ·
                  rfl

theorem cell20_820922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_820922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820922 prefixEnd_820922 := by exact prefixLift 820922
  have htrace : WordTrace (prefixWord ++ tailWord_820922) baseStart_820922 baseEnd_820922 := by
    simpa [prefixWord, tailWord_820922, baseEnd_820922] using wordTrace_append hprefix tailTrace_820922
  have hstable : (prefixWord ++ tailWord_820922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820922).length < 2 ^ (prefixWord ++ tailWord_820922).sum := by decide
  have hdescent : baseEnd_820922 < baseStart_820922 := by decide
  rcases family_descends (prefixWord ++ tailWord_820922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820956 : List Nat := [2, 2, 5, 1, 3, 7]
def baseStart_820956 : Nat := 118140960795 + 820956 * 2 ^ 59
def prefixEnd_820956 : Nat := 4983230072969 + 3 ^ 40 * 820956 * 2
def baseEnd_820956 : Nat := 13878025487822065500395

theorem tailTrace_820956 : CollatzResearch.WordTrace tailWord_820956 prefixEnd_820956 13878025487822065500395 := by
  unfold tailWord_820956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14971362606912047483685361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19961816809216063311580481 14971362606912047483685361)
  ·
    refine ⟨11228521955184035612764021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14971362606912047483685361 11228521955184035612764021)
    ·
      refine ⟨1052673933298503338696627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11228521955184035612764021 1052673933298503338696627)
      ·
        refine ⟨1579010899947755008044941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052673933298503338696627 1579010899947755008044941)
        ·
          refine ⟨592129087480408128016853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1579010899947755008044941 592129087480408128016853)
          ·
            refine ⟨13878025487822065500395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 592129087480408128016853 13878025487822065500395)
            ·
              rfl

theorem cell20_820956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 7].length) (baseStart_820956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820956 prefixEnd_820956 := by exact prefixLift 820956
  have htrace : WordTrace (prefixWord ++ tailWord_820956) baseStart_820956 baseEnd_820956 := by
    simpa [prefixWord, tailWord_820956, baseEnd_820956] using wordTrace_append hprefix tailTrace_820956
  have hstable : (prefixWord ++ tailWord_820956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820956).length < 2 ^ (prefixWord ++ tailWord_820956).sum := by decide
  have hdescent : baseEnd_820956 < baseStart_820956 := by decide
  rcases family_descends (prefixWord ++ tailWord_820956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820977 : List Nat := [1, 2, 2, 2, 2, 5, 1, 5]
def baseStart_820977 : Nat := 118140960795 + 820977 * 2 ^ 59
def prefixEnd_820977 : Nat := 4983230072969 + 3 ^ 40 * 820977 * 2
def baseEnd_820977 : Nat := 124905424381137676270193

theorem tailTrace_820977 : CollatzResearch.WordTrace tailWord_820977 prefixEnd_820977 124905424381137676270193 := by
  unfold tailWord_820977
  simp only [CollatzResearch.WordTrace]
  refine ⟨29943491146748015553885185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19962327431165343702590123 29943491146748015553885185)
  ·
    refine ⟨22457618360061011665413889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29943491146748015553885185 22457618360061011665413889)
    ·
      refine ⟨16843213770045758749060417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22457618360061011665413889 16843213770045758749060417)
      ·
        refine ⟨12632410327534319061795313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16843213770045758749060417 12632410327534319061795313)
        ·
          refine ⟨9474307745650739296346485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12632410327534319061795313 9474307745650739296346485)
          ·
            refine ⟨888216351154756809032483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9474307745650739296346485 888216351154756809032483)
            ·
              refine ⟨1332324526732135213548725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888216351154756809032483 1332324526732135213548725)
              ·
                refine ⟨124905424381137676270193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332324526732135213548725 124905424381137676270193)
                ·
                  rfl

theorem cell20_820977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_820977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820977 prefixEnd_820977 := by exact prefixLift 820977
  have htrace : WordTrace (prefixWord ++ tailWord_820977) baseStart_820977 baseEnd_820977 := by
    simpa [prefixWord, tailWord_820977, baseEnd_820977] using wordTrace_append hprefix tailTrace_820977
  have hstable : (prefixWord ++ tailWord_820977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820977).length < 2 ^ (prefixWord ++ tailWord_820977).sum := by decide
  have hdescent : baseEnd_820977 < baseStart_820977 := by decide
  rcases family_descends (prefixWord ++ tailWord_820977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_820994 : List Nat := [3, 4, 1, 1, 1, 1, 5, 4]
def baseStart_820994 : Nat := 118140960795 + 820994 * 2 ^ 59
def prefixEnd_820994 : Nat := 4983230072969 + 3 ^ 40 * 820994 * 2
def baseEnd_820994 : Nat := 124908010802212175081281

theorem tailTrace_820994 : CollatzResearch.WordTrace tailWord_820994 prefixEnd_820994 124908010802212175081281 := by
  unfold tailWord_820994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486027796921606864313509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19962740791790951638169357 7486027796921606864313509)
  ·
    refine ⟨1403630211922801287058783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7486027796921606864313509 1403630211922801287058783)
    ·
      refine ⟨2105445317884201930588175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403630211922801287058783 2105445317884201930588175)
      ·
        refine ⟨3158167976826302895882263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105445317884201930588175 3158167976826302895882263)
        ·
          refine ⟨4737251965239454343823395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3158167976826302895882263 4737251965239454343823395)
          ·
            refine ⟨7105877947859181515735093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4737251965239454343823395 7105877947859181515735093)
            ·
              refine ⟨666176057611798267100165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7105877947859181515735093 666176057611798267100165)
              ·
                refine ⟨124908010802212175081281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 666176057611798267100165 124908010802212175081281)
                ·
                  rfl

theorem cell20_820994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_820994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_820994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_820994 prefixEnd_820994 := by exact prefixLift 820994
  have htrace : WordTrace (prefixWord ++ tailWord_820994) baseStart_820994 baseEnd_820994 := by
    simpa [prefixWord, tailWord_820994, baseEnd_820994] using wordTrace_append hprefix tailTrace_820994
  have hstable : (prefixWord ++ tailWord_820994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_820994).length < 2 ^ (prefixWord ++ tailWord_820994).sum := by decide
  have hdescent : baseEnd_820994 < baseStart_820994 := by decide
  rcases family_descends (prefixWord ++ tailWord_820994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821029 : List Nat := [1, 3, 1, 2, 3, 2, 1, 3, 4]
def baseStart_821029 : Nat := 118140960795 + 821029 * 2 ^ 59
def prefixEnd_821029 : Nat := 4983230072969 + 3 ^ 40 * 821029 * 2
def baseEnd_821029 : Nat := 374740007360331959077033

theorem tailTrace_821029 : CollatzResearch.WordTrace tailWord_821029 prefixEnd_821029 374740007360331959077033 := by
  unfold tailWord_821029
  simp only [CollatzResearch.WordTrace]
  refine ⟨29945387742559628434778141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19963591828373085623185427 29945387742559628434778141)
  ·
    refine ⟨11229520403459860663041803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29945387742559628434778141 11229520403459860663041803)
    ·
      refine ⟨16844280605189790994562705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11229520403459860663041803 16844280605189790994562705)
      ·
        refine ⟨12633210453892343245922029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16844280605189790994562705 12633210453892343245922029)
        ·
          refine ⟨4737453920209628717220761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12633210453892343245922029 4737453920209628717220761)
          ·
            refine ⟨3553090440157221537915571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4737453920209628717220761 3553090440157221537915571)
            ·
              refine ⟨5329635660235832306873357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3553090440157221537915571 5329635660235832306873357)
              ·
                refine ⟨1998613372588437115077509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5329635660235832306873357 1998613372588437115077509)
                ·
                  refine ⟨374740007360331959077033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1998613372588437115077509 374740007360331959077033)
                  ·
                    rfl

theorem cell20_821029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_821029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821029 prefixEnd_821029 := by exact prefixLift 821029
  have htrace : WordTrace (prefixWord ++ tailWord_821029) baseStart_821029 baseEnd_821029 := by
    simpa [prefixWord, tailWord_821029, baseEnd_821029] using wordTrace_append hprefix tailTrace_821029
  have hstable : (prefixWord ++ tailWord_821029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821029).length < 2 ^ (prefixWord ++ tailWord_821029).sum := by decide
  have hdescent : baseEnd_821029 < baseStart_821029 := by decide
  rcases family_descends (prefixWord ++ tailWord_821029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821049 : List Nat := [1, 2, 1, 7, 1, 2, 2, 4]
def baseStart_821049 : Nat := 118140960795 + 821049 * 2 ^ 59
def prefixEnd_821049 : Nat := 4983230072969 + 3 ^ 40 * 821049 * 2
def baseEnd_821049 : Nat := 124916378635100259470095

theorem tailTrace_821049 : CollatzResearch.WordTrace tailWord_821049 prefixEnd_821049 124916378635100259470095 := by
  unfold tailWord_821049
  simp only [CollatzResearch.WordTrace]
  refine ⟨29946117202487171850506201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19964078134991447900337467 29946117202487171850506201)
  ·
    refine ⟨22459587901865378887879651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29946117202487171850506201 22459587901865378887879651)
    ·
      refine ⟨33689381852798068331819477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22459587901865378887879651 33689381852798068331819477)
      ·
        refine ⟨789594887174954726527019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33689381852798068331819477 789594887174954726527019)
        ·
          refine ⟨1184392330762432089790529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789594887174954726527019 1184392330762432089790529)
          ·
            refine ⟨888294248071824067342897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184392330762432089790529 888294248071824067342897)
            ·
              refine ⟨666220686053868050507173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888294248071824067342897 666220686053868050507173)
              ·
                refine ⟨124916378635100259470095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 666220686053868050507173 124916378635100259470095)
                ·
                  rfl

theorem cell20_821049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_821049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821049 prefixEnd_821049 := by exact prefixLift 821049
  have htrace : WordTrace (prefixWord ++ tailWord_821049) baseStart_821049 baseEnd_821049 := by
    simpa [prefixWord, tailWord_821049, baseEnd_821049] using wordTrace_append hprefix tailTrace_821049
  have hstable : (prefixWord ++ tailWord_821049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821049).length < 2 ^ (prefixWord ++ tailWord_821049).sum := by decide
  have hdescent : baseEnd_821049 < baseStart_821049 := by decide
  rcases family_descends (prefixWord ++ tailWord_821049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821053 : List Nat := [1, 4, 1, 4, 1, 2, 1, 6]
def baseStart_821053 : Nat := 118140960795 + 821053 * 2 ^ 59
def prefixEnd_821053 : Nat := 4983230072969 + 3 ^ 40 * 821053 * 2
def baseEnd_821053 : Nat := 124916987204764847425645

theorem tailTrace_821053 : CollatzResearch.WordTrace tailWord_821053 prefixEnd_821053 124916987204764847425645 := by
  unfold tailWord_821053
  simp only [CollatzResearch.WordTrace]
  refine ⟨29946263094472680533651813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19964175396315120355767875 29946263094472680533651813)
  ·
    refine ⟨5614924330213627600059715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29946263094472680533651813 5614924330213627600059715)
    ·
      refine ⟨8422386495320441400089573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5614924330213627600059715 8422386495320441400089573)
      ·
        refine ⟨1579197467872582762516795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8422386495320441400089573 1579197467872582762516795)
        ·
          refine ⟨2368796201808874143775193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579197467872582762516795 2368796201808874143775193)
          ·
            refine ⟨1776597151356655607831395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2368796201808874143775193 1776597151356655607831395)
            ·
              refine ⟨2664895727034983411747093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1776597151356655607831395 2664895727034983411747093)
              ·
                refine ⟨124916987204764847425645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2664895727034983411747093 124916987204764847425645)
                ·
                  rfl

theorem cell20_821053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_821053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821053 prefixEnd_821053 := by exact prefixLift 821053
  have htrace : WordTrace (prefixWord ++ tailWord_821053) baseStart_821053 baseEnd_821053 := by
    simpa [prefixWord, tailWord_821053, baseEnd_821053] using wordTrace_append hprefix tailTrace_821053
  have hstable : (prefixWord ++ tailWord_821053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821053).length < 2 ^ (prefixWord ++ tailWord_821053).sum := by decide
  have hdescent : baseEnd_821053 < baseStart_821053 := by decide
  rcases family_descends (prefixWord ++ tailWord_821053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821074 : List Nat := [3, 2, 2, 1, 1, 3, 8]
def baseStart_821074 : Nat := 118140960795 + 821074 * 2 ^ 59
def prefixEnd_821074 : Nat := 4983230072969 + 3 ^ 40 * 821074 * 2
def baseEnd_821074 : Nat := 41640060731834644730761

theorem tailTrace_821074 : CollatzResearch.WordTrace tailWord_821074 prefixEnd_821074 41640060731834644730761 := by
  unfold tailWord_821074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7486757256849150280041569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19964686018264400746777517 7486757256849150280041569)
  ·
    refine ⟨5615067942636862710031177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7486757256849150280041569 5615067942636862710031177)
    ·
      refine ⟨4211300956977647032523383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5615067942636862710031177 4211300956977647032523383)
      ·
        refine ⟨6316951435466470548785075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4211300956977647032523383 6316951435466470548785075)
        ·
          refine ⟨9475427153199705823177613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6316951435466470548785075 9475427153199705823177613)
          ·
            refine ⟨3553285182449889683691605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9475427153199705823177613 3553285182449889683691605)
            ·
              refine ⟨41640060731834644730761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3553285182449889683691605 41640060731834644730761)
              ·
                rfl

theorem cell20_821074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 8].length) (baseStart_821074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821074 prefixEnd_821074 := by exact prefixLift 821074
  have htrace : WordTrace (prefixWord ++ tailWord_821074) baseStart_821074 baseEnd_821074 := by
    simpa [prefixWord, tailWord_821074, baseEnd_821074] using wordTrace_append hprefix tailTrace_821074
  have hstable : (prefixWord ++ tailWord_821074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821074).length < 2 ^ (prefixWord ++ tailWord_821074).sum := by decide
  have hdescent : baseEnd_821074 < baseStart_821074 := by decide
  rcases family_descends (prefixWord ++ tailWord_821074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821081 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_821081 : Nat := 118140960795 + 821081 * 2 ^ 59
def prefixEnd_821081 : Nat := 4983230072969 + 3 ^ 40 * 821081 * 2
def baseEnd_821081 : Nat := 374763741577250889343487

theorem tailTrace_821081 : CollatzResearch.WordTrace tailWord_821081 prefixEnd_821081 374763741577250889343487 := by
  unfold tailWord_821081
  simp only [CollatzResearch.WordTrace]
  refine ⟨29947284338371241315671097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19964856225580827543780731 29947284338371241315671097)
  ·
    refine ⟨22460463253778430986753323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29947284338371241315671097 22460463253778430986753323)
    ·
      refine ⟨33690694880667646480129985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22460463253778430986753323 33690694880667646480129985)
      ·
        refine ⟨25268021160500734860097489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33690694880667646480129985 25268021160500734860097489)
        ·
          refine ⟨18951015870375551145073117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25268021160500734860097489 18951015870375551145073117)
          ·
            refine ⟨7106630951390831679402419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18951015870375551145073117 7106630951390831679402419)
            ·
              refine ⟨10659946427086247519103629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7106630951390831679402419 10659946427086247519103629)
              ·
                refine ⟨3997479910157342819663861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10659946427086247519103629 3997479910157342819663861)
                ·
                  refine ⟨374763741577250889343487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3997479910157342819663861 374763741577250889343487)
                  ·
                    rfl

theorem cell20_821081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_821081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821081 prefixEnd_821081 := by exact prefixLift 821081
  have htrace : WordTrace (prefixWord ++ tailWord_821081) baseStart_821081 baseEnd_821081 := by
    simpa [prefixWord, tailWord_821081, baseEnd_821081] using wordTrace_append hprefix tailTrace_821081
  have hstable : (prefixWord ++ tailWord_821081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821081).length < 2 ^ (prefixWord ++ tailWord_821081).sum := by decide
  have hdescent : baseEnd_821081 < baseStart_821081 := by decide
  rcases family_descends (prefixWord ++ tailWord_821081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821091 : List Nat := [1, 1, 1, 5, 4, 1, 2, 5]
def baseStart_821091 : Nat := 118140960795 + 821091 * 2 ^ 59
def prefixEnd_821091 : Nat := 4983230072969 + 3 ^ 40 * 821091 * 2
def baseEnd_821091 : Nat := 124922768616578433003371

theorem tailTrace_821091 : CollatzResearch.WordTrace tailWord_821091 prefixEnd_821091 124922768616578433003371 := by
  unfold tailWord_821091
  simp only [CollatzResearch.WordTrace]
  refine ⟨29947649068335013023535127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19965099378890008682356751 29947649068335013023535127)
  ·
    refine ⟨44921473602502519535302691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29947649068335013023535127 44921473602502519535302691)
    ·
      refine ⟨67382210403753779302954037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44921473602502519535302691 67382210403753779302954037)
      ·
        refine ⟨6317082225351916809651941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67382210403753779302954037 6317082225351916809651941)
        ·
          refine ⟨1184452917253484401809739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6317082225351916809651941 1184452917253484401809739)
          ·
            refine ⟨1776679375880226602714609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184452917253484401809739 1776679375880226602714609)
            ·
              refine ⟨1332509531910169952035957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1776679375880226602714609 1332509531910169952035957)
              ·
                refine ⟨124922768616578433003371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332509531910169952035957 124922768616578433003371)
                ·
                  rfl

theorem cell20_821091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 5].length) (baseStart_821091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821091 prefixEnd_821091 := by exact prefixLift 821091
  have htrace : WordTrace (prefixWord ++ tailWord_821091) baseStart_821091 baseEnd_821091 := by
    simpa [prefixWord, tailWord_821091, baseEnd_821091] using wordTrace_append hprefix tailTrace_821091
  have hstable : (prefixWord ++ tailWord_821091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821091).length < 2 ^ (prefixWord ++ tailWord_821091).sum := by decide
  have hdescent : baseEnd_821091 < baseStart_821091 := by decide
  rcases family_descends (prefixWord ++ tailWord_821091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821142 : List Nat := [5, 3, 1, 1, 2, 2, 1, 5]
def baseStart_821142 : Nat := 118140960795 + 821142 * 2 ^ 59
def prefixEnd_821142 : Nat := 4983230072969 + 3 ^ 40 * 821142 * 2
def baseEnd_821142 : Nat := 124930527879801929436635

theorem tailTrace_821142 : CollatzResearch.WordTrace tailWord_821142 prefixEnd_821142 124930527879801929436635 := by
  unfold tailWord_821142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871844324446890545852605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19966339460766832489094453 1871844324446890545852605)
  ·
    refine ⟨701941621667583954694727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1871844324446890545852605 701941621667583954694727)
    ·
      refine ⟨1052912432501375932042091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 701941621667583954694727 1052912432501375932042091)
      ·
        refine ⟨1579368648752063898063137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1052912432501375932042091 1579368648752063898063137)
        ·
          refine ⟨1184526486564047923547353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1579368648752063898063137 1184526486564047923547353)
          ·
            refine ⟨888394864923035942660515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184526486564047923547353 888394864923035942660515)
            ·
              refine ⟨1332592297384553913990773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888394864923035942660515 1332592297384553913990773)
              ·
                refine ⟨124930527879801929436635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332592297384553913990773 124930527879801929436635)
                ·
                  rfl

theorem cell20_821142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_821142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821142 prefixEnd_821142 := by exact prefixLift 821142
  have htrace : WordTrace (prefixWord ++ tailWord_821142) baseStart_821142 baseEnd_821142 := by
    simpa [prefixWord, tailWord_821142, baseEnd_821142] using wordTrace_append hprefix tailTrace_821142
  have hstable : (prefixWord ++ tailWord_821142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821142).length < 2 ^ (prefixWord ++ tailWord_821142).sum := by decide
  have hdescent : baseEnd_821142 < baseStart_821142 := by decide
  rcases family_descends (prefixWord ++ tailWord_821142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821195 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_821195 : Nat := 118140960795 + 821195 * 2 ^ 59
def prefixEnd_821195 : Nat := 4983230072969 + 3 ^ 40 * 821195 * 2
def baseEnd_821195 : Nat := 374815774283573159543021

theorem tailTrace_821195 : CollatzResearch.WordTrace tailWord_821195 prefixEnd_821195 374815774283573159543021 := by
  unfold tailWord_821195
  simp only [CollatzResearch.WordTrace]
  refine ⟨29951442259958238785321039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19967628173305492523547359 29951442259958238785321039)
  ·
    refine ⟨44927163389937358177981559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29951442259958238785321039 44927163389937358177981559)
    ·
      refine ⟨67390745084906037266972339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44927163389937358177981559 67390745084906037266972339)
      ·
        refine ⟨101086117627359055900458509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67390745084906037266972339 101086117627359055900458509)
        ·
          refine ⟨37907294110259645962671941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101086117627359055900458509 37907294110259645962671941)
          ·
            refine ⟨7107617645673683618000989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37907294110259645962671941 7107617645673683618000989)
            ·
              refine ⟨2665356617127631356750371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7107617645673683618000989 2665356617127631356750371)
              ·
                refine ⟨3998034925691447035125557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2665356617127631356750371 3998034925691447035125557)
                ·
                  refine ⟨374815774283573159543021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3998034925691447035125557 374815774283573159543021)
                  ·
                    rfl

theorem cell20_821195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_821195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821195 prefixEnd_821195 := by exact prefixLift 821195
  have htrace : WordTrace (prefixWord ++ tailWord_821195) baseStart_821195 baseEnd_821195 := by
    simpa [prefixWord, tailWord_821195, baseEnd_821195] using wordTrace_append hprefix tailTrace_821195
  have hstable : (prefixWord ++ tailWord_821195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821195).length < 2 ^ (prefixWord ++ tailWord_821195).sum := by decide
  have hdescent : baseEnd_821195 < baseStart_821195 := by decide
  rcases family_descends (prefixWord ++ tailWord_821195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821198 : List Nat := [4, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_821198 : Nat := 118140960795 + 821198 * 2 ^ 59
def prefixEnd_821198 : Nat := 4983230072969 + 3 ^ 40 * 821198 * 2
def baseEnd_821198 : Nat := 374817143565318482443009

theorem tailTrace_821198 : CollatzResearch.WordTrace tailWord_821198 prefixEnd_821198 374817143565318482443009 := by
  unfold tailWord_821198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743943959868421287210031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19967701119298246865120165 3743943959868421287210031)
  ·
    refine ⟨5615915939802631930815047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3743943959868421287210031 5615915939802631930815047)
    ·
      refine ⟨8423873909703947896222571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5615915939802631930815047 8423873909703947896222571)
      ·
        refine ⟨12635810864555921844333857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8423873909703947896222571 12635810864555921844333857)
        ·
          refine ⟨9476858148416941383250393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12635810864555921844333857 9476858148416941383250393)
          ·
            refine ⟨7107643611312706037437795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9476858148416941383250393 7107643611312706037437795)
            ·
              refine ⟨10661465416969059056156693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7107643611312706037437795 10661465416969059056156693)
              ·
                refine ⟨499756191420424643257345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10661465416969059056156693 499756191420424643257345)
                ·
                  refine ⟨374817143565318482443009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499756191420424643257345 374817143565318482443009)
                  ·
                    rfl

theorem cell20_821198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_821198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821198 prefixEnd_821198 := by exact prefixLift 821198
  have htrace : WordTrace (prefixWord ++ tailWord_821198) baseStart_821198 baseEnd_821198 := by
    simpa [prefixWord, tailWord_821198, baseEnd_821198] using wordTrace_append hprefix tailTrace_821198
  have hstable : (prefixWord ++ tailWord_821198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821198).length < 2 ^ (prefixWord ++ tailWord_821198).sum := by decide
  have hdescent : baseEnd_821198 < baseStart_821198 := by decide
  rcases family_descends (prefixWord ++ tailWord_821198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821218 : List Nat := [3, 3, 3, 1, 3, 1, 2, 4]
def baseStart_821218 : Nat := 118140960795 + 821218 * 2 ^ 59
def prefixEnd_821218 : Nat := 4983230072969 + 3 ^ 40 * 821218 * 2
def baseEnd_821218 : Nat := 124942090703429100592087

theorem tailTrace_821218 : CollatzResearch.WordTrace tailWord_821218 prefixEnd_821218 124942090703429100592087 := by
  unfold tailWord_821218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7488070284718728428352077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19968187425916609142272205 7488070284718728428352077)
  ·
    refine ⟨2808026356769523160632029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7488070284718728428352077 2808026356769523160632029)
    ·
      refine ⟨1053009883788571185237011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2808026356769523160632029 1053009883788571185237011)
      ·
        refine ⟨1579514825682856777855517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053009883788571185237011 1579514825682856777855517)
        ·
          refine ⟨592318059631071291695819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1579514825682856777855517 592318059631071291695819)
          ·
            refine ⟨888477089446606937543729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592318059631071291695819 888477089446606937543729)
            ·
              refine ⟨666357817084955203157797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888477089446606937543729 666357817084955203157797)
              ·
                refine ⟨124942090703429100592087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 666357817084955203157797 124942090703429100592087)
                ·
                  rfl

theorem cell20_821218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_821218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821218 prefixEnd_821218 := by exact prefixLift 821218
  have htrace : WordTrace (prefixWord ++ tailWord_821218) baseStart_821218 baseEnd_821218 := by
    simpa [prefixWord, tailWord_821218, baseEnd_821218] using wordTrace_append hprefix tailTrace_821218
  have hstable : (prefixWord ++ tailWord_821218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821218).length < 2 ^ (prefixWord ++ tailWord_821218).sum := by decide
  have hdescent : baseEnd_821218 < baseStart_821218 := by decide
  rcases family_descends (prefixWord ++ tailWord_821218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821219 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_821219 : Nat := 118140960795 + 821219 * 2 ^ 59
def prefixEnd_821219 : Nat := 4983230072969 + 3 ^ 40 * 821219 * 2
def baseEnd_821219 : Nat := 374826728537535742742923

theorem tailTrace_821219 : CollatzResearch.WordTrace tailWord_821219 prefixEnd_821219 374826728537535742742923 := by
  unfold tailWord_821219
  simp only [CollatzResearch.WordTrace]
  refine ⟨29952317611871290884194711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19968211741247527256129807 29952317611871290884194711)
  ·
    refine ⟨44928476417806936326292067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29952317611871290884194711 44928476417806936326292067)
    ·
      refine ⟨67392714626710404489438101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44928476417806936326292067 67392714626710404489438101)
      ·
        refine ⟨3159033498127050210442411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67392714626710404489438101 3159033498127050210442411)
        ·
          refine ⟨4738550247190575315663617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3159033498127050210442411 4738550247190575315663617)
          ·
            refine ⟨3553912685392931486747713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4738550247190575315663617 3553912685392931486747713)
            ·
              refine ⟨2665434514044698615060785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3553912685392931486747713 2665434514044698615060785)
              ·
                refine ⟨1999075885533523961295589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665434514044698615060785 1999075885533523961295589)
                ·
                  refine ⟨374826728537535742742923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999075885533523961295589 374826728537535742742923)
                  ·
                    rfl

theorem cell20_821219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_821219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821219 prefixEnd_821219 := by exact prefixLift 821219
  have htrace : WordTrace (prefixWord ++ tailWord_821219) baseStart_821219 baseEnd_821219 := by
    simpa [prefixWord, tailWord_821219, baseEnd_821219] using wordTrace_append hprefix tailTrace_821219
  have hstable : (prefixWord ++ tailWord_821219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821219).length < 2 ^ (prefixWord ++ tailWord_821219).sum := by decide
  have hdescent : baseEnd_821219 < baseStart_821219 := by decide
  rcases family_descends (prefixWord ++ tailWord_821219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821226 : List Nat := [3, 1, 3, 1, 2, 1, 3, 6]
def baseStart_821226 : Nat := 118140960795 + 821226 * 2 ^ 59
def prefixEnd_821226 : Nat := 4983230072969 + 3 ^ 40 * 821226 * 2
def baseEnd_821226 : Nat := 124943307842758276503187

theorem tailTrace_821226 : CollatzResearch.WordTrace tailWord_821226 prefixEnd_821226 124943307842758276503187 := by
  unfold tailWord_821226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7488143230711482769924883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19968381948563954053133021 7488143230711482769924883)
  ·
    refine ⟨11232214846067224154887325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7488143230711482769924883 11232214846067224154887325)
    ·
      refine ⟨4212080567275209058082747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11232214846067224154887325 4212080567275209058082747)
      ·
        refine ⟨6318120850912813587124121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212080567275209058082747 6318120850912813587124121)
        ·
          refine ⟨4738590638184610190343091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6318120850912813587124121 4738590638184610190343091)
          ·
            refine ⟨7107885957276915285514637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4738590638184610190343091 7107885957276915285514637)
            ·
              refine ⟨2665457233978843232067989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7107885957276915285514637 2665457233978843232067989)
              ·
                refine ⟨124943307842758276503187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2665457233978843232067989 124943307842758276503187)
                ·
                  rfl

theorem cell20_821226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 6].length) (baseStart_821226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821226 prefixEnd_821226 := by exact prefixLift 821226
  have htrace : WordTrace (prefixWord ++ tailWord_821226) baseStart_821226 baseEnd_821226 := by
    simpa [prefixWord, tailWord_821226, baseEnd_821226] using wordTrace_append hprefix tailTrace_821226
  have hstable : (prefixWord ++ tailWord_821226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821226).length < 2 ^ (prefixWord ++ tailWord_821226).sum := by decide
  have hdescent : baseEnd_821226 < baseStart_821226 := by decide
  rcases family_descends (prefixWord ++ tailWord_821226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821240 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_821240 : Nat := 118140960795 + 821240 * 2 ^ 59
def prefixEnd_821240 : Nat := 4983230072969 + 3 ^ 40 * 821240 * 2
def baseEnd_821240 : Nat := 374836313509753003042837

theorem tailTrace_821240 : CollatzResearch.WordTrace tailWord_821240 prefixEnd_821240 374836313509753003042837 := by
  unfold tailWord_821240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14976541772397605735354587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19968722363196807647139449 14976541772397605735354587)
  ·
    refine ⟨22464812658596408603031881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14976541772397605735354587 22464812658596408603031881)
    ·
      refine ⟨16848609493947306452273911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22464812658596408603031881 16848609493947306452273911)
      ·
        refine ⟨25272914240920959678410867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16848609493947306452273911 25272914240920959678410867)
        ·
          refine ⟨37909371361381439517616301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25272914240920959678410867 37909371361381439517616301)
          ·
            refine ⟨14216014260518039819106113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37909371361381439517616301 14216014260518039819106113)
            ·
              refine ⟨10662010695388529864329585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14216014260518039819106113 10662010695388529864329585)
              ·
                refine ⟨7996508021541397398247189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10662010695388529864329585 7996508021541397398247189)
                ·
                  refine ⟨374836313509753003042837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7996508021541397398247189 374836313509753003042837)
                  ·
                    rfl

theorem cell20_821240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_821240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821240 prefixEnd_821240 := by exact prefixLift 821240
  have htrace : WordTrace (prefixWord ++ tailWord_821240) baseStart_821240 baseEnd_821240 := by
    simpa [prefixWord, tailWord_821240, baseEnd_821240] using wordTrace_append hprefix tailTrace_821240
  have hstable : (prefixWord ++ tailWord_821240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821240).length < 2 ^ (prefixWord ++ tailWord_821240).sum := by decide
  have hdescent : baseEnd_821240 < baseStart_821240 := by decide
  rcases family_descends (prefixWord ++ tailWord_821240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821253 : List Nat := [1, 3, 1, 1, 2, 5, 3, 2, 2]
def baseStart_821253 : Nat := 118140960795 + 821253 * 2 ^ 59
def prefixEnd_821253 : Nat := 4983230072969 + 3 ^ 40 * 821253 * 2
def baseEnd_821253 : Nat := 374842247063982735609451

theorem tailTrace_821253 : CollatzResearch.WordTrace tailWord_821253 prefixEnd_821253 374842247063982735609451 := by
  unfold tailWord_821253
  simp only [CollatzResearch.WordTrace]
  refine ⟨29953557693748114690932413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19969038462498743127288275 29953557693748114690932413)
  ·
    refine ⟨11232584135155543009099655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29953557693748114690932413 11232584135155543009099655)
    ·
      refine ⟨16848876202733314513649483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11232584135155543009099655 16848876202733314513649483)
      ·
        refine ⟨25273314304099971770474225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16848876202733314513649483 25273314304099971770474225)
        ·
          refine ⟨18954985728074978827855669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25273314304099971770474225 18954985728074978827855669)
          ·
            refine ⟨1777029912007029265111469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18954985728074978827855669 1777029912007029265111469)
            ·
              refine ⟨666386217002635974416801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1777029912007029265111469 666386217002635974416801)
              ·
                refine ⟨499789662751976980812601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666386217002635974416801 499789662751976980812601)
                ·
                  refine ⟨374842247063982735609451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499789662751976980812601 374842247063982735609451)
                  ·
                    rfl

theorem cell20_821253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_821253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821253 prefixEnd_821253 := by exact prefixLift 821253
  have htrace : WordTrace (prefixWord ++ tailWord_821253) baseStart_821253 baseEnd_821253 := by
    simpa [prefixWord, tailWord_821253, baseEnd_821253] using wordTrace_append hprefix tailTrace_821253
  have hstable : (prefixWord ++ tailWord_821253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821253).length < 2 ^ (prefixWord ++ tailWord_821253).sum := by decide
  have hdescent : baseEnd_821253 < baseStart_821253 := by decide
  rcases family_descends (prefixWord ++ tailWord_821253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821305 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 3]
def baseStart_821305 : Nat := 118140960795 + 821305 * 2 ^ 59
def prefixEnd_821305 : Nat := 4983230072969 + 3 ^ 40 * 821305 * 2
def baseEnd_821305 : Nat := 374865981280901665875905

theorem tailTrace_821305 : CollatzResearch.WordTrace tailWord_821305 prefixEnd_821305 374865981280901665875905 := by
  unfold tailWord_821305
  simp only [CollatzResearch.WordTrace]
  refine ⟨29955454289559727571825369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19970302859706485047883579 29955454289559727571825369)
  ·
    refine ⟨22466590717169795678869027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29955454289559727571825369 22466590717169795678869027)
    ·
      refine ⟨33699886075754693518303541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22466590717169795678869027 33699886075754693518303541)
      ·
        refine ⟨3159364319602002517340957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33699886075754693518303541 3159364319602002517340957)
        ·
          refine ⟨1184761619850750944002859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3159364319602002517340957 1184761619850750944002859)
          ·
            refine ⟨1777142429776126416004289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184761619850750944002859 1777142429776126416004289)
            ·
              refine ⟨1332856822332094812003217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777142429776126416004289 1332856822332094812003217)
              ·
                refine ⟨999642616749071109002413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1332856822332094812003217 999642616749071109002413)
                ·
                  refine ⟨374865981280901665875905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999642616749071109002413 374865981280901665875905)
                  ·
                    rfl

theorem cell20_821305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_821305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821305 prefixEnd_821305 := by exact prefixLift 821305
  have htrace : WordTrace (prefixWord ++ tailWord_821305) baseStart_821305 baseEnd_821305 := by
    simpa [prefixWord, tailWord_821305, baseEnd_821305] using wordTrace_append hprefix tailTrace_821305
  have hstable : (prefixWord ++ tailWord_821305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821305).length < 2 ^ (prefixWord ++ tailWord_821305).sum := by decide
  have hdescent : baseEnd_821305 < baseStart_821305 := by decide
  rcases family_descends (prefixWord ++ tailWord_821305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821312 : List Nat := [2, 1, 1, 2, 2, 5, 1, 4, 2]
def baseStart_821312 : Nat := 118140960795 + 821312 * 2 ^ 59
def prefixEnd_821312 : Nat := 4983230072969 + 3 ^ 40 * 821312 * 2
def baseEnd_821312 : Nat := 374869176271640752642543

theorem tailTrace_821312 : CollatzResearch.WordTrace tailWord_821312 prefixEnd_821312 374869176271640752642543 := by
  unfold tailWord_821312
  simp only [CollatzResearch.WordTrace]
  refine ⟨14977854800267183883665095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19970473067022911844886793 14977854800267183883665095)
  ·
    refine ⟨22466782200400775825497643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14977854800267183883665095 22466782200400775825497643)
    ·
      refine ⟨33700173300601163738246465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22466782200400775825497643 33700173300601163738246465)
      ·
        refine ⟨25275129975450872803684849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33700173300601163738246465 25275129975450872803684849)
        ·
          refine ⟨18956347481588154602763637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25275129975450872803684849 18956347481588154602763637)
          ·
            refine ⟨1777157576398889494009091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18956347481588154602763637 1777157576398889494009091)
            ·
              refine ⟨2665736364598334241013637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777157576398889494009091 2665736364598334241013637)
              ·
                refine ⟨499825568362187670190057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2665736364598334241013637 499825568362187670190057)
                ·
                  refine ⟨374869176271640752642543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499825568362187670190057 374869176271640752642543)
                  ·
                    rfl

theorem cell20_821312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_821312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821312 prefixEnd_821312 := by exact prefixLift 821312
  have htrace : WordTrace (prefixWord ++ tailWord_821312) baseStart_821312 baseEnd_821312 := by
    simpa [prefixWord, tailWord_821312, baseEnd_821312] using wordTrace_append hprefix tailTrace_821312
  have hstable : (prefixWord ++ tailWord_821312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821312).length < 2 ^ (prefixWord ++ tailWord_821312).sum := by decide
  have hdescent : baseEnd_821312 < baseStart_821312 := by decide
  rcases family_descends (prefixWord ++ tailWord_821312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821326 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_821326 : Nat := 118140960795 + 821326 * 2 ^ 59
def prefixEnd_821326 : Nat := 4983230072969 + 3 ^ 40 * 821326 * 2
def baseEnd_821326 : Nat := 374875566253118926175819

theorem tailTrace_821326 : CollatzResearch.WordTrace tailWord_821326 prefixEnd_821326 374875566253118926175819 := by
  unfold tailWord_821326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3744527527810456019792479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19970813481655765438893221 3744527527810456019792479)
  ·
    refine ⟨5616791291715684029688719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3744527527810456019792479 5616791291715684029688719)
    ·
      refine ⟨8425186937573526044533079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5616791291715684029688719 8425186937573526044533079)
      ·
        refine ⟨12637780406360289066799619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8425186937573526044533079 12637780406360289066799619)
        ·
          refine ⟨18956670609540433600199429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12637780406360289066799619 18956670609540433600199429)
          ·
            refine ⟨3554375739288831300037393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18956670609540433600199429 3554375739288831300037393)
            ·
              refine ⟨2665781804466623475028045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554375739288831300037393 2665781804466623475028045)
              ·
                refine ⟨999668176674983803135517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2665781804466623475028045 999668176674983803135517)
                ·
                  refine ⟨374875566253118926175819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999668176674983803135517 374875566253118926175819)
                  ·
                    rfl

theorem cell20_821326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_821326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821326 prefixEnd_821326 := by exact prefixLift 821326
  have htrace : WordTrace (prefixWord ++ tailWord_821326) baseStart_821326 baseEnd_821326 := by
    simpa [prefixWord, tailWord_821326, baseEnd_821326] using wordTrace_append hprefix tailTrace_821326
  have hstable : (prefixWord ++ tailWord_821326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821326).length < 2 ^ (prefixWord ++ tailWord_821326).sum := by decide
  have hdescent : baseEnd_821326 < baseStart_821326 := by decide
  rcases family_descends (prefixWord ++ tailWord_821326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821333 : List Nat := [1, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_821333 : Nat := 118140960795 + 821333 * 2 ^ 59
def prefixEnd_821333 : Nat := 4983230072969 + 3 ^ 40 * 821333 * 2
def baseEnd_821333 : Nat := 374878761243858012942457

theorem tailTrace_821333 : CollatzResearch.WordTrace tailWord_821333 prefixEnd_821333 374878761243858012942457 := by
  unfold tailWord_821333
  simp only [CollatzResearch.WordTrace]
  refine ⟨29956475533458288353844653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19970983688972192235896435 29956475533458288353844653)
  ·
    refine ⟨11233678325046858132691745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29956475533458288353844653 11233678325046858132691745)
    ·
      refine ⟨8425258743785143599518809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11233678325046858132691745 8425258743785143599518809)
      ·
        refine ⟨6318944057838857699639107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8425258743785143599518809 6318944057838857699639107)
        ·
          refine ⟨9478416086758286549458661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6318944057838857699639107 9478416086758286549458661)
          ·
            refine ⟨1777203016267178728023499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9478416086758286549458661 1777203016267178728023499)
            ·
              refine ⟨2665804524400768092035249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777203016267178728023499 2665804524400768092035249)
              ·
                refine ⟨1999353393300576069026437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2665804524400768092035249 1999353393300576069026437)
                ·
                  refine ⟨374878761243858012942457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999353393300576069026437 374878761243858012942457)
                  ·
                    rfl

theorem cell20_821333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_821333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821333 prefixEnd_821333 := by exact prefixLift 821333
  have htrace : WordTrace (prefixWord ++ tailWord_821333) baseStart_821333 baseEnd_821333 := by
    simpa [prefixWord, tailWord_821333, baseEnd_821333] using wordTrace_append hprefix tailTrace_821333
  have hstable : (prefixWord ++ tailWord_821333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821333).length < 2 ^ (prefixWord ++ tailWord_821333).sum := by decide
  have hdescent : baseEnd_821333 < baseStart_821333 := by decide
  rcases family_descends (prefixWord ++ tailWord_821333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821346 : List Nat := [3, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_821346 : Nat := 118140960795 + 821346 * 2 ^ 59
def prefixEnd_821346 : Nat := 4983230072969 + 3 ^ 40 * 821346 * 2
def baseEnd_821346 : Nat := 374884694798087745509071

theorem tailTrace_821346 : CollatzResearch.WordTrace tailWord_821346 prefixEnd_821346 374884694798087745509071 := by
  unfold tailWord_821346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7489237420602797893516973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19971299788274127716045261 7489237420602797893516973)
  ·
    refine ⟨2808464032726049210068865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7489237420602797893516973 2808464032726049210068865)
    ·
      refine ⟨2106348024544536907551649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2808464032726049210068865 2106348024544536907551649)
      ·
        refine ⟨1579761018408402680663737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2106348024544536907551649 1579761018408402680663737)
        ·
          refine ⟨1184820763806302010497803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1579761018408402680663737 1184820763806302010497803)
          ·
            refine ⟨1777231145709453015746705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184820763806302010497803 1777231145709453015746705)
            ·
              refine ⟨1332923359282089761810029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777231145709453015746705 1332923359282089761810029)
              ·
                refine ⟨499846259730783660678761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1332923359282089761810029 499846259730783660678761)
                ·
                  refine ⟨374884694798087745509071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499846259730783660678761 374884694798087745509071)
                  ·
                    rfl

theorem cell20_821346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_821346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821346 prefixEnd_821346 := by exact prefixLift 821346
  have htrace : WordTrace (prefixWord ++ tailWord_821346) baseStart_821346 baseEnd_821346 := by
    simpa [prefixWord, tailWord_821346, baseEnd_821346] using wordTrace_append hprefix tailTrace_821346
  have hstable : (prefixWord ++ tailWord_821346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821346).length < 2 ^ (prefixWord ++ tailWord_821346).sum := by decide
  have hdescent : baseEnd_821346 < baseStart_821346 := by decide
  rcases family_descends (prefixWord ++ tailWord_821346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821361 : List Nat := [1, 2, 2, 2, 1, 1, 11]
def baseStart_821361 : Nat := 118140960795 + 821361 * 2 ^ 59
def prefixEnd_821361 : Nat := 4983230072969 + 3 ^ 40 * 821361 * 2
def baseEnd_821361 : Nat := 41654615689646040001001

theorem tailTrace_821361 : CollatzResearch.WordTrace tailWord_821361 prefixEnd_821361 41654615689646040001001 := by
  unfold tailWord_821361
  simp only [CollatzResearch.WordTrace]
  refine ⟨29957496777356849135863937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19971664518237899423909291 29957496777356849135863937)
  ·
    refine ⟨22468122583017636851897953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29957496777356849135863937 22468122583017636851897953)
    ·
      refine ⟨16851091937263227638923465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22468122583017636851897953 16851091937263227638923465)
      ·
        refine ⟨12638318952947420729192599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16851091937263227638923465 12638318952947420729192599)
        ·
          refine ⟨18957478429421131093788899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12638318952947420729192599 18957478429421131093788899)
          ·
            refine ⟨28436217644131696640683349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18957478429421131093788899 28436217644131696640683349)
            ·
              refine ⟨41654615689646040001001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28436217644131696640683349 41654615689646040001001)
              ·
                rfl

theorem cell20_821361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 11].length) (baseStart_821361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821361 prefixEnd_821361 := by exact prefixLift 821361
  have htrace : WordTrace (prefixWord ++ tailWord_821361) baseStart_821361 baseEnd_821361 := by
    simpa [prefixWord, tailWord_821361, baseEnd_821361] using wordTrace_append hprefix tailTrace_821361
  have hstable : (prefixWord ++ tailWord_821361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821361).length < 2 ^ (prefixWord ++ tailWord_821361).sum := by decide
  have hdescent : baseEnd_821361 < baseStart_821361 := by decide
  rcases family_descends (prefixWord ++ tailWord_821361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821381 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 3]
def baseStart_821381 : Nat := 118140960795 + 821381 * 2 ^ 59
def prefixEnd_821381 : Nat := 4983230072969 + 3 ^ 40 * 821381 * 2
def baseEnd_821381 : Nat := 374900669751783179342261

theorem tailTrace_821381 : CollatzResearch.WordTrace tailWord_821381 prefixEnd_821381 374900669751783179342261 := by
  unfold tailWord_821381
  simp only [CollatzResearch.WordTrace]
  refine ⟨29958226237284392551591997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19972150824856261701061331 29958226237284392551591997)
  ·
    refine ⟨11234334838981647206846999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29958226237284392551591997 11234334838981647206846999)
    ·
      refine ⟨16851502258472470810270499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11234334838981647206846999 16851502258472470810270499)
      ·
        refine ⟨25277253387708706215405749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16851502258472470810270499 25277253387708706215405749)
        ·
          refine ⟨2369742505097691207694289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25277253387708706215405749 2369742505097691207694289)
          ·
            refine ⟨1777306878823268405770717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2369742505097691207694289 1777306878823268405770717)
            ·
              refine ⟨666490079558725652164019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1777306878823268405770717 666490079558725652164019)
              ·
                refine ⟨999735119338088478246029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666490079558725652164019 999735119338088478246029)
                ·
                  refine ⟨374900669751783179342261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999735119338088478246029 374900669751783179342261)
                  ·
                    rfl

theorem cell20_821381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_821381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821381 prefixEnd_821381 := by exact prefixLift 821381
  have htrace : WordTrace (prefixWord ++ tailWord_821381) baseStart_821381 baseEnd_821381 := by
    simpa [prefixWord, tailWord_821381, baseEnd_821381] using wordTrace_append hprefix tailTrace_821381
  have hstable : (prefixWord ++ tailWord_821381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821381).length < 2 ^ (prefixWord ++ tailWord_821381).sum := by decide
  have hdescent : baseEnd_821381 < baseStart_821381 := by decide
  rcases family_descends (prefixWord ++ tailWord_821381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821392 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_821392 : Nat := 118140960795 + 821392 * 2 ^ 59
def prefixEnd_821392 : Nat := 4983230072969 + 3 ^ 40 * 821392 * 2
def baseEnd_821392 : Nat := 374905690451516029975549

theorem tailTrace_821392 : CollatzResearch.WordTrace tailWord_821392 prefixEnd_821392 374905690451516029975549 := by
  unfold tailWord_821392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979313720122270715121215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19972418293496360953494953 14979313720122270715121215)
  ·
    refine ⟨22468970580183406072681823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14979313720122270715121215 22468970580183406072681823)
    ·
      refine ⟨33703455870275109109022735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22468970580183406072681823 33703455870275109109022735)
      ·
        refine ⟨50555183805412663663534103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33703455870275109109022735 50555183805412663663534103)
        ·
          refine ⟨75832775708118995495301155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50555183805412663663534103 75832775708118995495301155)
          ·
            refine ⟨113749163562178493242951733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75832775708118995495301155 113749163562178493242951733)
            ·
              refine ⟨10663984083954233741526725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113749163562178493242951733 10663984083954233741526725)
              ·
                refine ⟨1999497015741418826536261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10663984083954233741526725 1999497015741418826536261)
                ·
                  refine ⟨374905690451516029975549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999497015741418826536261 374905690451516029975549)
                  ·
                    rfl

theorem cell20_821392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_821392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821392 prefixEnd_821392 := by exact prefixLift 821392
  have htrace : WordTrace (prefixWord ++ tailWord_821392) baseStart_821392 baseEnd_821392 := by
    simpa [prefixWord, tailWord_821392, baseEnd_821392] using wordTrace_append hprefix tailTrace_821392
  have hstable : (prefixWord ++ tailWord_821392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821392).length < 2 ^ (prefixWord ++ tailWord_821392).sum := by decide
  have hdescent : baseEnd_821392 < baseStart_821392 := by decide
  rcases family_descends (prefixWord ++ tailWord_821392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821405 : List Nat := [1, 4, 2, 1, 1, 5, 1, 3, 2]
def baseStart_821405 : Nat := 118140960795 + 821405 * 2 ^ 59
def prefixEnd_821405 : Nat := 4983230072969 + 3 ^ 40 * 821405 * 2
def baseEnd_821405 : Nat := 374911624005745762542163

theorem tailTrace_821405 : CollatzResearch.WordTrace tailWord_821405 prefixEnd_821405 374911624005745762542163 := by
  unfold tailWord_821405
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959101589197444650465669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19972734392798296433643779 29959101589197444650465669)
  ·
    refine ⟨5617331547974520871962313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29959101589197444650465669 5617331547974520871962313)
    ·
      refine ⟨4212998660980890653971735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5617331547974520871962313 4212998660980890653971735)
      ·
        refine ⟨6319497991471335980957603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4212998660980890653971735 6319497991471335980957603)
        ·
          refine ⟨9479246987207003971436405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6319497991471335980957603 9479246987207003971436405)
          ·
            refine ⟨888679405050656622322163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9479246987207003971436405 888679405050656622322163)
            ·
              refine ⟨1333019107575984933483245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888679405050656622322163 1333019107575984933483245)
              ·
                refine ⟨499882165340994350056217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333019107575984933483245 499882165340994350056217)
                ·
                  refine ⟨374911624005745762542163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499882165340994350056217 374911624005745762542163)
                  ·
                    rfl

theorem cell20_821405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_821405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821405 prefixEnd_821405 := by exact prefixLift 821405
  have htrace : WordTrace (prefixWord ++ tailWord_821405) baseStart_821405 baseEnd_821405 := by
    simpa [prefixWord, tailWord_821405, baseEnd_821405] using wordTrace_append hprefix tailTrace_821405
  have hstable : (prefixWord ++ tailWord_821405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821405).length < 2 ^ (prefixWord ++ tailWord_821405).sum := by decide
  have hdescent : baseEnd_821405 < baseStart_821405 := by decide
  rcases family_descends (prefixWord ++ tailWord_821405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821422 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_821422 : Nat := 118140960795 + 821422 * 2 ^ 59
def prefixEnd_821422 : Nat := 4983230072969 + 3 ^ 40 * 821422 * 2
def baseEnd_821422 : Nat := 374919383268969258975427

theorem tailTrace_821422 : CollatzResearch.WordTrace tailWord_821422 prefixEnd_821422 374919383268969258975427 := by
  unfold tailWord_821422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3744965203766982069229315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19973147753423904369223013 3744965203766982069229315)
  ·
    refine ⟨5617447805650473103843973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3744965203766982069229315 5617447805650473103843973)
    ·
      refine ⟨1053271463559463706970745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5617447805650473103843973 1053271463559463706970745)
      ·
        refine ⟨789953597669597780228059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1053271463559463706970745 789953597669597780228059)
        ·
          refine ⟨1184930396504396670342089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789953597669597780228059 1184930396504396670342089)
          ·
            refine ⟨888697797378297502756567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184930396504396670342089 888697797378297502756567)
            ·
              refine ⟨1333046696067446254134851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888697797378297502756567 1333046696067446254134851)
              ·
                refine ⟨1999570044101169381202277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333046696067446254134851 1999570044101169381202277)
                ·
                  refine ⟨374919383268969258975427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999570044101169381202277 374919383268969258975427)
                  ·
                    rfl

theorem cell20_821422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_821422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821422 prefixEnd_821422 := by exact prefixLift 821422
  have htrace : WordTrace (prefixWord ++ tailWord_821422) baseStart_821422 baseEnd_821422 := by
    simpa [prefixWord, tailWord_821422, baseEnd_821422] using wordTrace_append hprefix tailTrace_821422
  have hstable : (prefixWord ++ tailWord_821422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821422).length < 2 ^ (prefixWord ++ tailWord_821422).sum := by decide
  have hdescent : baseEnd_821422 < baseStart_821422 := by decide
  rcases family_descends (prefixWord ++ tailWord_821422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821423 : List Nat := [1, 1, 2, 1, 2, 3, 1, 6, 3]
def baseStart_821423 : Nat := 118140960795 + 821423 * 2 ^ 59
def prefixEnd_821423 : Nat := 4983230072969 + 3 ^ 40 * 821423 * 2
def baseEnd_821423 : Nat := 374919839696217699942089

theorem tailTrace_821423 : CollatzResearch.WordTrace tailWord_821423 prefixEnd_821423 374919839696217699942089 := by
  unfold tailWord_821423
  simp only [CollatzResearch.WordTrace]
  refine ⟨29959758103132233724620923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19973172068754822483080615 29959758103132233724620923)
  ·
    refine ⟨44939637154698350586931385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29959758103132233724620923 44939637154698350586931385)
    ·
      refine ⟨33704727866023762940198539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44939637154698350586931385 33704727866023762940198539)
      ·
        refine ⟨50557091799035644410297809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33704727866023762940198539 50557091799035644410297809)
        ·
          refine ⟨37917818849276733307723357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50557091799035644410297809 37917818849276733307723357)
          ·
            refine ⟨14219182068478774990396259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37917818849276733307723357 14219182068478774990396259)
            ·
              refine ⟨21328773102718162485594389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14219182068478774990396259 21328773102718162485594389)
              ·
                refine ⟨999786239189913866512237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21328773102718162485594389 999786239189913866512237)
                ·
                  refine ⟨374919839696217699942089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999786239189913866512237 374919839696217699942089)
                  ·
                    rfl

theorem cell20_821423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_821423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821423 prefixEnd_821423 := by exact prefixLift 821423
  have htrace : WordTrace (prefixWord ++ tailWord_821423) baseStart_821423 baseEnd_821423 := by
    simpa [prefixWord, tailWord_821423, baseEnd_821423] using wordTrace_append hprefix tailTrace_821423
  have hstable : (prefixWord ++ tailWord_821423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821423).length < 2 ^ (prefixWord ++ tailWord_821423).sum := by decide
  have hdescent : baseEnd_821423 < baseStart_821423 := by decide
  rcases family_descends (prefixWord ++ tailWord_821423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821436 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_821436 : Nat := 118140960795 + 821436 * 2 ^ 59
def prefixEnd_821436 : Nat := 4983230072969 + 3 ^ 40 * 821436 * 2
def baseEnd_821436 : Nat := 374925773250447432508703

theorem tailTrace_821436 : CollatzResearch.WordTrace tailWord_821436 prefixEnd_821436 374925773250447432508703 := by
  unfold tailWord_821436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14980116126042568472422081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19973488168056757963229441 14980116126042568472422081)
  ·
    refine ⟨11235087094531926354316561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14980116126042568472422081 11235087094531926354316561)
    ·
      refine ⟨8426315320898944765737421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11235087094531926354316561 8426315320898944765737421)
      ·
        refine ⟨3159868245337104287151533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8426315320898944765737421 3159868245337104287151533)
        ·
          refine ⟨1184950592001414107681825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3159868245337104287151533 1184950592001414107681825)
          ·
            refine ⟨888712944001060580761369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1184950592001414107681825 888712944001060580761369)
            ·
              refine ⟨666534708000795435571027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 888712944001060580761369 666534708000795435571027)
              ·
                refine ⟨999802062001193153356541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666534708000795435571027 999802062001193153356541)
                ·
                  refine ⟨374925773250447432508703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999802062001193153356541 374925773250447432508703)
                  ·
                    rfl

theorem cell20_821436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_821436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821436 prefixEnd_821436 := by exact prefixLift 821436
  have htrace : WordTrace (prefixWord ++ tailWord_821436) baseStart_821436 baseEnd_821436 := by
    simpa [prefixWord, tailWord_821436, baseEnd_821436] using wordTrace_append hprefix tailTrace_821436
  have hstable : (prefixWord ++ tailWord_821436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821436).length < 2 ^ (prefixWord ++ tailWord_821436).sum := by decide
  have hdescent : baseEnd_821436 < baseStart_821436 := by decide
  rcases family_descends (prefixWord ++ tailWord_821436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821440 : List Nat := [2, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_821440 : Nat := 118140960795 + 821440 * 2 ^ 59
def prefixEnd_821440 : Nat := 4983230072969 + 3 ^ 40 * 821440 * 2
def baseEnd_821440 : Nat := 374927598959441196375353

theorem tailTrace_821440 : CollatzResearch.WordTrace tailWord_821440 prefixEnd_821440 374927598959441196375353 := by
  unfold tailWord_821440
  simp only [CollatzResearch.WordTrace]
  refine ⟨14980189072035322813994887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19973585429380430418659849 14980189072035322813994887)
  ·
    refine ⟨22470283608052984220992331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14980189072035322813994887 22470283608052984220992331)
    ·
      refine ⟨33705425412079476331488497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22470283608052984220992331 33705425412079476331488497)
      ·
        refine ⟨25279069059059607248616373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33705425412079476331488497 25279069059059607248616373)
        ·
          refine ⟨2369912724286838179557785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25279069059059607248616373 2369912724286838179557785)
          ·
            refine ⟨1777434543215128634668339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2369912724286838179557785 1777434543215128634668339)
            ·
              refine ⟨2666151814822692952002509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1777434543215128634668339 2666151814822692952002509)
              ·
                refine ⟨999806930558509857000941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2666151814822692952002509 999806930558509857000941)
                ·
                  refine ⟨374927598959441196375353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 999806930558509857000941 374927598959441196375353)
                  ·
                    rfl

theorem cell20_821440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_821440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821440 prefixEnd_821440 := by exact prefixLift 821440
  have htrace : WordTrace (prefixWord ++ tailWord_821440) baseStart_821440 baseEnd_821440 := by
    simpa [prefixWord, tailWord_821440, baseEnd_821440] using wordTrace_append hprefix tailTrace_821440
  have hstable : (prefixWord ++ tailWord_821440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821440).length < 2 ^ (prefixWord ++ tailWord_821440).sum := by decide
  have hdescent : baseEnd_821440 < baseStart_821440 := by decide
  rcases family_descends (prefixWord ++ tailWord_821440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821454 : List Nat := [4, 1, 1, 1, 4, 1, 2, 6]
def baseStart_821454 : Nat := 118140960795 + 821454 * 2 ^ 59
def prefixEnd_821454 : Nat := 4983230072969 + 3 ^ 40 * 821454 * 2
def baseEnd_821454 : Nat := 124977996313639789969543

theorem tailTrace_821454 : CollatzResearch.WordTrace tailWord_821454 prefixEnd_821454 124977996313639789969543 := by
  unfold tailWord_821454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745111095752490752374927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19973925844013284012666277 3745111095752490752374927)
  ·
    refine ⟨5617666643628736128562391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3745111095752490752374927 5617666643628736128562391)
    ·
      refine ⟨8426499965443104192843587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5617666643628736128562391 8426499965443104192843587)
      ·
        refine ⟨12639749948164656289265381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426499965443104192843587 12639749948164656289265381)
        ·
          refine ⟨2369953115280873054237259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12639749948164656289265381 2369953115280873054237259)
          ·
            refine ⟨3554929672921309581355889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2369953115280873054237259 3554929672921309581355889)
            ·
              refine ⟨2666197254690982186016917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3554929672921309581355889 2666197254690982186016917)
              ·
                refine ⟨124977996313639789969543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2666197254690982186016917 124977996313639789969543)
                ·
                  rfl

theorem cell20_821454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_821454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821454 prefixEnd_821454 := by exact prefixLift 821454
  have htrace : WordTrace (prefixWord ++ tailWord_821454) baseStart_821454 baseEnd_821454 := by
    simpa [prefixWord, tailWord_821454, baseEnd_821454] using wordTrace_append hprefix tailTrace_821454
  have hstable : (prefixWord ++ tailWord_821454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821454).length < 2 ^ (prefixWord ++ tailWord_821454).sum := by decide
  have hdescent : baseEnd_821454 < baseStart_821454 := by decide
  rcases family_descends (prefixWord ++ tailWord_821454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821530 : List Nat := [3, 1, 1, 3, 4, 1, 7]
def baseStart_821530 : Nat := 118140960795 + 821530 * 2 ^ 59
def prefixEnd_821530 : Nat := 4983230072969 + 3 ^ 40 * 821530 * 2
def baseEnd_821530 : Nat := 41663186379088987041665

theorem tailTrace_821530 : CollatzResearch.WordTrace tailWord_821530 prefixEnd_821530 41663186379088987041665 := by
  unfold tailWord_821530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7490915178436147749691511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19975773809163060665844029 7490915178436147749691511)
  ·
    refine ⟨11236372767654221624537267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7490915178436147749691511 11236372767654221624537267)
    ·
      refine ⟨16854559151481332436805901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11236372767654221624537267 16854559151481332436805901)
      ·
        refine ⟨6320459681805499663802213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16854559151481332436805901 6320459681805499663802213)
        ·
          refine ⟨1185086190338531186962915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6320459681805499663802213 1185086190338531186962915)
          ·
            refine ⟨1777629285507796780444373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185086190338531186962915 1777629285507796780444373)
            ·
              refine ⟨41663186379088987041665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1777629285507796780444373 41663186379088987041665)
              ·
                rfl

theorem cell20_821530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 7].length) (baseStart_821530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821530 prefixEnd_821530 := by exact prefixLift 821530
  have htrace : WordTrace (prefixWord ++ tailWord_821530) baseStart_821530 baseEnd_821530 := by
    simpa [prefixWord, tailWord_821530, baseEnd_821530] using wordTrace_append hprefix tailTrace_821530
  have hstable : (prefixWord ++ tailWord_821530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821530).length < 2 ^ (prefixWord ++ tailWord_821530).sum := by decide
  have hdescent : baseEnd_821530 < baseStart_821530 := by decide
  rcases family_descends (prefixWord ++ tailWord_821530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821540 : List Nat := [2, 3, 1, 3, 1, 2, 2, 4, 2]
def baseStart_821540 : Nat := 118140960795 + 821540 * 2 ^ 59
def prefixEnd_821540 : Nat := 4983230072969 + 3 ^ 40 * 821540 * 2
def baseEnd_821540 : Nat := 374973241684285293041611

theorem tailTrace_821540 : CollatzResearch.WordTrace tailWord_821540 prefixEnd_821540 374973241684285293041611 := by
  unfold tailWord_821540
  simp only [CollatzResearch.WordTrace]
  refine ⟨14982012721854181353315037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19976016962472241804420049 14982012721854181353315037)
  ·
    refine ⟨5618254770695318007493139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14982012721854181353315037 5618254770695318007493139)
    ·
      refine ⟨8427382156042977011239709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5618254770695318007493139 8427382156042977011239709)
      ·
        refine ⟨3160268308516116379214891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8427382156042977011239709 3160268308516116379214891)
        ·
          refine ⟨4740402462774174568822337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160268308516116379214891 4740402462774174568822337)
          ·
            refine ⟨3555301847080630926616753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4740402462774174568822337 3555301847080630926616753)
            ·
              refine ⟨2666476385310473194962565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555301847080630926616753 2666476385310473194962565)
              ·
                refine ⟨499964322245713724055481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2666476385310473194962565 499964322245713724055481)
                ·
                  refine ⟨374973241684285293041611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499964322245713724055481 374973241684285293041611)
                  ·
                    rfl

theorem cell20_821540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_821540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821540 prefixEnd_821540 := by exact prefixLift 821540
  have htrace : WordTrace (prefixWord ++ tailWord_821540) baseStart_821540 baseEnd_821540 := by
    simpa [prefixWord, tailWord_821540, baseEnd_821540] using wordTrace_append hprefix tailTrace_821540
  have hstable : (prefixWord ++ tailWord_821540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821540).length < 2 ^ (prefixWord ++ tailWord_821540).sum := by decide
  have hdescent : baseEnd_821540 < baseStart_821540 := by decide
  rcases family_descends (prefixWord ++ tailWord_821540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821561 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 4]
def baseStart_821561 : Nat := 118140960795 + 821561 * 2 ^ 59
def prefixEnd_821561 : Nat := 4983230072969 + 3 ^ 40 * 821561 * 2
def baseEnd_821561 : Nat := 374982826656502553341525

theorem tailTrace_821561 : CollatzResearch.WordTrace tailWord_821561 prefixEnd_821561 374982826656502553341525 := by
  unfold tailWord_821561
  simp only [CollatzResearch.WordTrace]
  refine ⟨29964791376632283293144537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19976527584421522195429691 29964791376632283293144537)
  ·
    refine ⟨22473593532474212469858403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29964791376632283293144537 22473593532474212469858403)
    ·
      refine ⟨33710390298711318704787605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22473593532474212469858403 33710390298711318704787605)
      ·
        refine ⟨1580174545252093064286919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33710390298711318704787605 1580174545252093064286919)
        ·
          refine ⟨2370261817878139596430379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580174545252093064286919 2370261817878139596430379)
          ·
            refine ⟨3555392726817209394645569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370261817878139596430379 3555392726817209394645569)
            ·
              refine ⟨2666544545112907045984177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555392726817209394645569 2666544545112907045984177)
              ·
                refine ⟨1999908408834680284488133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2666544545112907045984177 1999908408834680284488133)
                ·
                  refine ⟨374982826656502553341525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1999908408834680284488133 374982826656502553341525)
                  ·
                    rfl

theorem cell20_821561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_821561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821561 prefixEnd_821561 := by exact prefixLift 821561
  have htrace : WordTrace (prefixWord ++ tailWord_821561) baseStart_821561 baseEnd_821561 := by
    simpa [prefixWord, tailWord_821561, baseEnd_821561] using wordTrace_append hprefix tailTrace_821561
  have hstable : (prefixWord ++ tailWord_821561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821561).length < 2 ^ (prefixWord ++ tailWord_821561).sum := by decide
  have hdescent : baseEnd_821561 < baseStart_821561 := by decide
  rcases family_descends (prefixWord ++ tailWord_821561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821598 : List Nat := [4, 4, 2, 1, 1, 1, 2, 5]
def baseStart_821598 : Nat := 118140960795 + 821598 * 2 ^ 59
def prefixEnd_821598 : Nat := 4983230072969 + 3 ^ 40 * 821598 * 2
def baseEnd_821598 : Nat := 124999904821564956369347

theorem tailTrace_821598 : CollatzResearch.WordTrace tailWord_821598 prefixEnd_821598 124999904821564956369347 := by
  unfold tailWord_821598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3745767609687279826530181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19977427251665492408160965 3745767609687279826530181)
  ·
    refine ⟨702331426816364967474409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3745767609687279826530181 702331426816364967474409)
    ·
      refine ⟨526748570112273725605807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 702331426816364967474409 526748570112273725605807)
      ·
        refine ⟨790122855168410588408711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526748570112273725605807 790122855168410588408711)
        ·
          refine ⟨1185184282752615882613067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790122855168410588408711 1185184282752615882613067)
          ·
            refine ⟨1777776424128923823919601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1185184282752615882613067 1777776424128923823919601)
            ·
              refine ⟨1333332318096692867939701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777776424128923823919601 1333332318096692867939701)
              ·
                refine ⟨124999904821564956369347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333332318096692867939701 124999904821564956369347)
                ·
                  rfl

theorem cell20_821598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_821598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821598 prefixEnd_821598 := by exact prefixLift 821598
  have htrace : WordTrace (prefixWord ++ tailWord_821598) baseStart_821598 baseEnd_821598 := by
    simpa [prefixWord, tailWord_821598, baseEnd_821598] using wordTrace_append hprefix tailTrace_821598
  have hstable : (prefixWord ++ tailWord_821598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821598).length < 2 ^ (prefixWord ++ tailWord_821598).sum := by decide
  have hdescent : baseEnd_821598 < baseStart_821598 := by decide
  rcases family_descends (prefixWord ++ tailWord_821598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821599 : List Nat := [1, 1, 2, 3, 1, 2, 2, 6, 2]
def baseStart_821599 : Nat := 118140960795 + 821599 * 2 ^ 59
def prefixEnd_821599 : Nat := 4983230072969 + 3 ^ 40 * 821599 * 2
def baseEnd_821599 : Nat := 375000170891943310074703

theorem tailTrace_821599 : CollatzResearch.WordTrace tailWord_821599 prefixEnd_821599 375000170891943310074703 := by
  unfold tailWord_821599
  simp only [CollatzResearch.WordTrace]
  refine ⟨29966177350494615783027851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19977451566996410522018567 29966177350494615783027851)
  ·
    refine ⟨44949266025741923674541777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29966177350494615783027851 44949266025741923674541777)
    ·
      refine ⟨33711949519306442755906333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44949266025741923674541777 33711949519306442755906333)
      ·
        refine ⟨12641981069739916033464875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33711949519306442755906333 12641981069739916033464875)
        ·
          refine ⟨18962971604609874050197313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12641981069739916033464875 18962971604609874050197313)
          ·
            refine ⟨14222228703457405537647985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18962971604609874050197313 14222228703457405537647985)
            ·
              refine ⟨10666671527593054153235989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14222228703457405537647985 10666671527593054153235989)
              ·
                refine ⟨500000227855924413432937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10666671527593054153235989 500000227855924413432937)
                ·
                  refine ⟨375000170891943310074703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500000227855924413432937 375000170891943310074703)
                  ·
                    rfl

theorem cell20_821599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 2].length) (baseStart_821599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821599 prefixEnd_821599 := by exact prefixLift 821599
  have htrace : WordTrace (prefixWord ++ tailWord_821599) baseStart_821599 baseEnd_821599 := by
    simpa [prefixWord, tailWord_821599, baseEnd_821599] using wordTrace_append hprefix tailTrace_821599
  have hstable : (prefixWord ++ tailWord_821599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821599).length < 2 ^ (prefixWord ++ tailWord_821599).sum := by decide
  have hdescent : baseEnd_821599 < baseStart_821599 := by decide
  rcases family_descends (prefixWord ++ tailWord_821599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821627 : List Nat := [1, 1, 1, 1, 1, 7, 2, 6]
def baseStart_821627 : Nat := 118140960795 + 821627 * 2 ^ 59
def prefixEnd_821627 : Nat := 4983230072969 + 3 ^ 40 * 821627 * 2
def baseEnd_821627 : Nat := 125004316951633219047085

theorem tailTrace_821627 : CollatzResearch.WordTrace tailWord_821627 prefixEnd_821627 125004316951633219047085 := by
  unfold tailWord_821627
  simp only [CollatzResearch.WordTrace]
  refine ⟨29967198594393176565047135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19978132396262117710031423 29967198594393176565047135)
  ·
    refine ⟨44950797891589764847570703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29967198594393176565047135 44950797891589764847570703)
    ·
      refine ⟨67426196837384647271356055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44950797891589764847570703 67426196837384647271356055)
      ·
        refine ⟨101139295256076970907034083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67426196837384647271356055 101139295256076970907034083)
        ·
          refine ⟨151708942884115456360551125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101139295256076970907034083 151708942884115456360551125)
          ·
            refine ⟨3555678348846456008450417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 151708942884115456360551125 3555678348846456008450417)
            ·
              refine ⟨2666758761634842006337813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3555678348846456008450417 2666758761634842006337813)
              ·
                refine ⟨125004316951633219047085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2666758761634842006337813 125004316951633219047085)
                ·
                  rfl

theorem cell20_821627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_821627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821627 prefixEnd_821627 := by exact prefixLift 821627
  have htrace : WordTrace (prefixWord ++ tailWord_821627) baseStart_821627 baseEnd_821627 := by
    simpa [prefixWord, tailWord_821627, baseEnd_821627] using wordTrace_append hprefix tailTrace_821627
  have hstable : (prefixWord ++ tailWord_821627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821627).length < 2 ^ (prefixWord ++ tailWord_821627).sum := by decide
  have hdescent : baseEnd_821627 < baseStart_821627 := by decide
  rcases family_descends (prefixWord ++ tailWord_821627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821637 : List Nat := [1, 3, 1, 1, 3, 1, 1, 7, 2]
def baseStart_821637 : Nat := 118140960795 + 821637 * 2 ^ 59
def prefixEnd_821637 : Nat := 4983230072969 + 3 ^ 40 * 821637 * 2
def baseEnd_821637 : Nat := 375017515127384066807881

theorem tailTrace_821637 : CollatzResearch.WordTrace tailWord_821637 prefixEnd_821637 375017515127384066807881 := by
  unfold tailWord_821637
  simp only [CollatzResearch.WordTrace]
  refine ⟨29967563324356948272911165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19978375549571298848607443 29967563324356948272911165)
  ·
    refine ⟨11237836246633855602341687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29967563324356948272911165 11237836246633855602341687)
    ·
      refine ⟨16856754369950783403512531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11237836246633855602341687 16856754369950783403512531)
      ·
        refine ⟨25285131554926175105268797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16856754369950783403512531 25285131554926175105268797)
        ·
          refine ⟨9481924333097315664475799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25285131554926175105268797 9481924333097315664475799)
          ·
            refine ⟨14222886499645973496713699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9481924333097315664475799 14222886499645973496713699)
            ·
              refine ⟨21334329749468960245070549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14222886499645973496713699 21334329749468960245070549)
              ·
                refine ⟨500023353503178755743841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21334329749468960245070549 500023353503178755743841)
                ·
                  refine ⟨375017515127384066807881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500023353503178755743841 375017515127384066807881)
                  ·
                    rfl

theorem cell20_821637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_821637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821637 prefixEnd_821637 := by exact prefixLift 821637
  have htrace : WordTrace (prefixWord ++ tailWord_821637) baseStart_821637 baseEnd_821637 := by
    simpa [prefixWord, tailWord_821637, baseEnd_821637] using wordTrace_append hprefix tailTrace_821637
  have hstable : (prefixWord ++ tailWord_821637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821637).length < 2 ^ (prefixWord ++ tailWord_821637).sum := by decide
  have hdescent : baseEnd_821637 < baseStart_821637 := by decide
  rcases family_descends (prefixWord ++ tailWord_821637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821661 : List Nat := [1, 4, 2, 1, 4, 2, 1, 5]
def baseStart_821661 : Nat := 118140960795 + 821661 * 2 ^ 59
def prefixEnd_821661 : Nat := 4983230072969 + 3 ^ 40 * 821661 * 2
def baseEnd_821661 : Nat := 125009489793782216669261

theorem tailTrace_821661 : CollatzResearch.WordTrace tailWord_821661 prefixEnd_821661 125009489793782216669261 := by
  unfold tailWord_821661
  simp only [CollatzResearch.WordTrace]
  refine ⟨29968438676270000371784837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19978959117513333581189891 29968438676270000371784837)
  ·
    refine ⟨5619082251800625069709657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29968438676270000371784837 5619082251800625069709657)
    ·
      refine ⟨4214311688850468802282243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5619082251800625069709657 4214311688850468802282243)
      ·
        refine ⟨6321467533275703203423365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4214311688850468802282243 6321467533275703203423365)
        ·
          refine ⟨1185275162489194350641881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6321467533275703203423365 1185275162489194350641881)
          ·
            refine ⟨888956371866895762981411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185275162489194350641881 888956371866895762981411)
            ·
              refine ⟨1333434557800343644472117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888956371866895762981411 1333434557800343644472117)
              ·
                refine ⟨125009489793782216669261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333434557800343644472117 125009489793782216669261)
                ·
                  rfl

theorem cell20_821661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_821661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821661 prefixEnd_821661 := by exact prefixLift 821661
  have htrace : WordTrace (prefixWord ++ tailWord_821661) baseStart_821661 baseEnd_821661 := by
    simpa [prefixWord, tailWord_821661, baseEnd_821661] using wordTrace_append hprefix tailTrace_821661
  have hstable : (prefixWord ++ tailWord_821661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821661).length < 2 ^ (prefixWord ++ tailWord_821661).sum := by decide
  have hdescent : baseEnd_821661 < baseStart_821661 := by decide
  rcases family_descends (prefixWord ++ tailWord_821661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821682 : List Nat := [3, 2, 1, 1, 1, 1, 7, 4]
def baseStart_821682 : Nat := 118140960795 + 821682 * 2 ^ 59
def prefixEnd_821682 : Nat := 4983230072969 + 3 ^ 40 * 821682 * 2
def baseEnd_821682 : Nat := 125012684784521303435899

theorem tailTrace_821682 : CollatzResearch.WordTrace tailWord_821682 prefixEnd_821682 125012684784521303435899 := by
  unfold tailWord_821682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7492301152298480239574825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19979469739462613972199533 7492301152298480239574825)
  ·
    refine ⟨5619225864223860179681119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7492301152298480239574825 5619225864223860179681119)
    ·
      refine ⟨8428838796335790269521679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5619225864223860179681119 8428838796335790269521679)
      ·
        refine ⟨12643258194503685404282519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8428838796335790269521679 12643258194503685404282519)
        ·
          refine ⟨18964887291755528106423779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643258194503685404282519 18964887291755528106423779)
          ·
            refine ⟨28447330937633292159635669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18964887291755528106423779 28447330937633292159635669)
            ·
              refine ⟨666734318850780284991461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28447330937633292159635669 666734318850780284991461)
              ·
                refine ⟨125012684784521303435899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 666734318850780284991461 125012684784521303435899)
                ·
                  rfl

theorem cell20_821682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_821682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821682 prefixEnd_821682 := by exact prefixLift 821682
  have htrace : WordTrace (prefixWord ++ tailWord_821682) baseStart_821682 baseEnd_821682 := by
    simpa [prefixWord, tailWord_821682, baseEnd_821682] using wordTrace_append hprefix tailTrace_821682
  have hstable : (prefixWord ++ tailWord_821682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821682).length < 2 ^ (prefixWord ++ tailWord_821682).sum := by decide
  have hdescent : baseEnd_821682 < baseStart_821682 := by decide
  rcases family_descends (prefixWord ++ tailWord_821682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821692 : List Nat := [2, 2, 2, 4, 1, 1, 1, 5, 2]
def baseStart_821692 : Nat := 118140960795 + 821692 * 2 ^ 59
def prefixEnd_821692 : Nat := 4983230072969 + 3 ^ 40 * 821692 * 2
def baseEnd_821692 : Nat := 375042618626048319974323

theorem tailTrace_821692 : CollatzResearch.WordTrace tailWord_821692 prefixEnd_821692 375042618626048319974323 := by
  unfold tailWord_821692
  simp only [CollatzResearch.WordTrace]
  refine ⟨14984784669578846333081665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19979712892771795110775553 14984784669578846333081665)
  ·
    refine ⟨11238588502184134749811249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14984784669578846333081665 11238588502184134749811249)
    ·
      refine ⟨8428941376638101062358437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11238588502184134749811249 8428941376638101062358437)
      ·
        refine ⟨1580426508119643949192207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8428941376638101062358437 1580426508119643949192207)
        ·
          refine ⟨2370639762179465923788311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580426508119643949192207 2370639762179465923788311)
          ·
            refine ⟨3555959643269198885682467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370639762179465923788311 3555959643269198885682467)
            ·
              refine ⟨5333939464903798328523701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3555959643269198885682467 5333939464903798328523701)
              ·
                refine ⟨500056824834731093299097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5333939464903798328523701 500056824834731093299097)
                ·
                  refine ⟨375042618626048319974323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500056824834731093299097 375042618626048319974323)
                  ·
                    rfl

theorem cell20_821692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_821692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821692 prefixEnd_821692 := by exact prefixLift 821692
  have htrace : WordTrace (prefixWord ++ tailWord_821692) baseStart_821692 baseEnd_821692 := by
    simpa [prefixWord, tailWord_821692, baseEnd_821692] using wordTrace_append hprefix tailTrace_821692
  have hstable : (prefixWord ++ tailWord_821692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821692).length < 2 ^ (prefixWord ++ tailWord_821692).sum := by decide
  have hdescent : baseEnd_821692 < baseStart_821692 := by decide
  rcases family_descends (prefixWord ++ tailWord_821692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821703 : List Nat := [1, 1, 4, 1, 1, 5, 7]
def baseStart_821703 : Nat := 118140960795 + 821703 * 2 ^ 59
def prefixEnd_821703 : Nat := 4983230072969 + 3 ^ 40 * 821703 * 2
def baseEnd_821703 : Nat := 41671959925086796734179

theorem tailTrace_821703 : CollatzResearch.WordTrace tailWord_821703 prefixEnd_821703 41671959925086796734179 := by
  unfold tailWord_821703
  simp only [CollatzResearch.WordTrace]
  refine ⟨29969970542117841544813763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19979980361411894363209175 29969970542117841544813763)
  ·
    refine ⟨44954955813176762317220645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29969970542117841544813763 44954955813176762317220645)
    ·
      refine ⟨8429054214970642934478871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44954955813176762317220645 8429054214970642934478871)
      ·
        refine ⟨12643581322455964401718307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8429054214970642934478871 12643581322455964401718307)
        ·
          refine ⟨18965371983683946602577461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12643581322455964401718307 18965371983683946602577461)
          ·
            refine ⟨1778003623470369993991637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18965371983683946602577461 1778003623470369993991637)
            ·
              refine ⟨41671959925086796734179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1778003623470369993991637 41671959925086796734179)
              ·
                rfl

theorem cell20_821703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 7].length) (baseStart_821703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821703 prefixEnd_821703 := by exact prefixLift 821703
  have htrace : WordTrace (prefixWord ++ tailWord_821703) baseStart_821703 baseEnd_821703 := by
    simpa [prefixWord, tailWord_821703, baseEnd_821703] using wordTrace_append hprefix tailTrace_821703
  have hstable : (prefixWord ++ tailWord_821703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821703).length < 2 ^ (prefixWord ++ tailWord_821703).sum := by decide
  have hdescent : baseEnd_821703 < baseStart_821703 := by decide
  rcases family_descends (prefixWord ++ tailWord_821703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821779 : List Nat := [1, 1, 1, 2, 1, 5, 4, 5]
def baseStart_821779 : Nat := 118140960795 + 821779 * 2 ^ 59
def prefixEnd_821779 : Nat := 4983230072969 + 3 ^ 40 * 821779 * 2
def baseEnd_821779 : Nat := 125027442598887561357989

theorem tailTrace_821779 : CollatzResearch.WordTrace tailWord_821779 prefixEnd_821779 125027442598887561357989 := by
  unfold tailWord_821779
  simp only [CollatzResearch.WordTrace]
  refine ⟨29972742489842506524580391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19981828326561671016386927 29972742489842506524580391)
  ·
    refine ⟨44959113734763759786870587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29972742489842506524580391 44959113734763759786870587)
    ·
      refine ⟨67438670602145639680305881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44959113734763759786870587 67438670602145639680305881)
      ·
        refine ⟨50579002951609229760229411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67438670602145639680305881 50579002951609229760229411)
        ·
          refine ⟨75868504427413844640344117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50579002951609229760229411 75868504427413844640344117)
          ·
            refine ⟨7112672290070047935032261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75868504427413844640344117 7112672290070047935032261)
            ·
              refine ⟨1333626054388133987818549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7112672290070047935032261 1333626054388133987818549)
              ·
                refine ⟨125027442598887561357989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333626054388133987818549 125027442598887561357989)
                ·
                  rfl

theorem cell20_821779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_821779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821779 prefixEnd_821779 := by exact prefixLift 821779
  have htrace : WordTrace (prefixWord ++ tailWord_821779) baseStart_821779 baseEnd_821779 := by
    simpa [prefixWord, tailWord_821779, baseEnd_821779] using wordTrace_append hprefix tailTrace_821779
  have hstable : (prefixWord ++ tailWord_821779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821779).length < 2 ^ (prefixWord ++ tailWord_821779).sum := by decide
  have hdescent : baseEnd_821779 < baseStart_821779 := by decide
  rcases family_descends (prefixWord ++ tailWord_821779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821820 : List Nat := [2, 2, 2, 2, 3, 2, 2, 2, 3]
def baseStart_821820 : Nat := 118140960795 + 821820 * 2 ^ 59
def prefixEnd_821820 : Nat := 4983230072969 + 3 ^ 40 * 821820 * 2
def baseEnd_821820 : Nat := 375101041313848763707133

theorem tailTrace_821820 : CollatzResearch.WordTrace tailWord_821820 prefixEnd_821820 375101041313848763707133 := by
  unfold tailWord_821820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14987118941346985263411457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19982825255129313684548609 14987118941346985263411457)
  ·
    refine ⟨11240339206010238947558593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14987118941346985263411457 11240339206010238947558593)
    ·
      refine ⟨8430254404507679210668945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11240339206010238947558593 8430254404507679210668945)
      ·
        refine ⟨6322690803380759408001709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8430254404507679210668945 6322690803380759408001709)
        ·
          refine ⟨2371009051267784778000641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6322690803380759408001709 2371009051267784778000641)
          ·
            refine ⟨1778256788450838583500481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2371009051267784778000641 1778256788450838583500481)
            ·
              refine ⟨1333692591338128937625361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1778256788450838583500481 1333692591338128937625361)
              ·
                refine ⟨1000269443503596703219021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333692591338128937625361 1000269443503596703219021)
                ·
                  refine ⟨375101041313848763707133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1000269443503596703219021 375101041313848763707133)
                  ·
                    rfl

theorem cell20_821820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_821820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821820 prefixEnd_821820 := by exact prefixLift 821820
  have htrace : WordTrace (prefixWord ++ tailWord_821820) baseStart_821820 baseEnd_821820 := by
    simpa [prefixWord, tailWord_821820, baseEnd_821820] using wordTrace_append hprefix tailTrace_821820
  have hstable : (prefixWord ++ tailWord_821820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821820).length < 2 ^ (prefixWord ++ tailWord_821820).sum := by decide
  have hdescent : baseEnd_821820 < baseStart_821820 := by decide
  rcases family_descends (prefixWord ++ tailWord_821820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821824 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_821824 : Nat := 118140960795 + 821824 * 2 ^ 59
def prefixEnd_821824 : Nat := 4983230072969 + 3 ^ 40 * 821824 * 2
def baseEnd_821824 : Nat := 375102867022842527573783

theorem tailTrace_821824 : CollatzResearch.WordTrace tailWord_821824 prefixEnd_821824 375102867022842527573783 := by
  unfold tailWord_821824
  simp only [CollatzResearch.WordTrace]
  refine ⟨14987191887339739604984263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19982922516452986139979017 14987191887339739604984263)
  ·
    refine ⟨22480787831009609407476395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14987191887339739604984263 22480787831009609407476395)
    ·
      refine ⟨33721181746514414111214593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22480787831009609407476395 33721181746514414111214593)
      ·
        refine ⟨25290886309885810583410945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33721181746514414111214593 25290886309885810583410945)
        ·
          refine ⟨18968164732414357937558209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25290886309885810583410945 18968164732414357937558209)
          ·
            refine ⟨14226123549310768453168657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18968164732414357937558209 14226123549310768453168657)
            ·
              refine ⟨10669592661983076339876493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14226123549310768453168657 10669592661983076339876493)
              ·
                refine ⟨4001097248243653627453685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10669592661983076339876493 4001097248243653627453685)
                ·
                  refine ⟨375102867022842527573783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4001097248243653627453685 375102867022842527573783)
                  ·
                    rfl

theorem cell20_821824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_821824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821824 prefixEnd_821824 := by exact prefixLift 821824
  have htrace : WordTrace (prefixWord ++ tailWord_821824) baseStart_821824 baseEnd_821824 := by
    simpa [prefixWord, tailWord_821824, baseEnd_821824] using wordTrace_append hprefix tailTrace_821824
  have hstable : (prefixWord ++ tailWord_821824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821824).length < 2 ^ (prefixWord ++ tailWord_821824).sum := by decide
  have hdescent : baseEnd_821824 < baseStart_821824 := by decide
  rcases family_descends (prefixWord ++ tailWord_821824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821830 : List Nat := [6, 1, 1, 1, 2, 3, 1, 5]
def baseStart_821830 : Nat := 118140960795 + 821830 * 2 ^ 59
def prefixEnd_821830 : Nat := 4983230072969 + 3 ^ 40 * 821830 * 2
def baseEnd_821830 : Nat := 125035201862111057791253

theorem tailTrace_821830 : CollatzResearch.WordTrace tailWord_821830 prefixEnd_821830 125035201862111057791253 := by
  unfold tailWord_821830
  simp only [CollatzResearch.WordTrace]
  refine ⟨936706331645554444833967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19983068408438494823124629 936706331645554444833967)
  ·
    refine ⟨1405059497468331667250951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 936706331645554444833967 1405059497468331667250951)
    ·
      refine ⟨2107589246202497500876427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405059497468331667250951 2107589246202497500876427)
      ·
        refine ⟨3161383869303746251314641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2107589246202497500876427 3161383869303746251314641)
        ·
          refine ⟨2371037901977809688485981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3161383869303746251314641 2371037901977809688485981)
          ·
            refine ⟨889139213241678633182243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2371037901977809688485981 889139213241678633182243)
            ·
              refine ⟨1333708819862517949773365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889139213241678633182243 1333708819862517949773365)
              ·
                refine ⟨125035201862111057791253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333708819862517949773365 125035201862111057791253)
                ·
                  rfl

theorem cell20_821830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_821830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821830 prefixEnd_821830 := by exact prefixLift 821830
  have htrace : WordTrace (prefixWord ++ tailWord_821830) baseStart_821830 baseEnd_821830 := by
    simpa [prefixWord, tailWord_821830, baseEnd_821830] using wordTrace_append hprefix tailTrace_821830
  have hstable : (prefixWord ++ tailWord_821830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821830).length < 2 ^ (prefixWord ++ tailWord_821830).sum := by decide
  have hdescent : baseEnd_821830 < baseStart_821830 := by decide
  rcases family_descends (prefixWord ++ tailWord_821830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821834 : List Nat := [3, 1, 2, 1, 1, 6, 1, 5]
def baseStart_821834 : Nat := 118140960795 + 821834 * 2 ^ 59
def prefixEnd_821834 : Nat := 4983230072969 + 3 ^ 40 * 821834 * 2
def baseEnd_821834 : Nat := 125035810431775645746803

theorem tailTrace_821834 : CollatzResearch.WordTrace tailWord_821834 prefixEnd_821834 125035810431775645746803 := by
  unfold tailWord_821834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7493687126160812729458139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19983165669762167278555037 7493687126160812729458139)
  ·
    refine ⟨11240530689241219094187209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7493687126160812729458139 11240530689241219094187209)
    ·
      refine ⟨8430398016930914320640407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11240530689241219094187209 8430398016930914320640407)
      ·
        refine ⟨12645597025396371480960611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8430398016930914320640407 12645597025396371480960611)
        ·
          refine ⟨18968395538094557221440917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12645597025396371480960611 18968395538094557221440917)
          ·
            refine ⟨889143540848182369755043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18968395538094557221440917 889143540848182369755043)
            ·
              refine ⟨1333715311272273554632565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889143540848182369755043 1333715311272273554632565)
              ·
                refine ⟨125035810431775645746803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333715311272273554632565 125035810431775645746803)
                ·
                  rfl

theorem cell20_821834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_821834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821834 prefixEnd_821834 := by exact prefixLift 821834
  have htrace : WordTrace (prefixWord ++ tailWord_821834) baseStart_821834 baseEnd_821834 := by
    simpa [prefixWord, tailWord_821834, baseEnd_821834] using wordTrace_append hprefix tailTrace_821834
  have hstable : (prefixWord ++ tailWord_821834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821834).length < 2 ^ (prefixWord ++ tailWord_821834).sum := by decide
  have hdescent : baseEnd_821834 < baseStart_821834 := by decide
  rcases family_descends (prefixWord ++ tailWord_821834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821841 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 3]
def baseStart_821841 : Nat := 118140960795 + 821841 * 2 ^ 59
def prefixEnd_821841 : Nat := 4983230072969 + 3 ^ 40 * 821841 * 2
def baseEnd_821841 : Nat := 375110626286066024007047

theorem tailTrace_821841 : CollatzResearch.WordTrace tailWord_821841 prefixEnd_821841 375110626286066024007047 := by
  unfold tailWord_821841
  simp only [CollatzResearch.WordTrace]
  refine ⟨29975003815617891113337377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19983335877078594075558251 29975003815617891113337377)
  ·
    refine ⟨22481252861713418335003033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29975003815617891113337377 22481252861713418335003033)
    ·
      refine ⟨16860939646285063751252275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22481252861713418335003033 16860939646285063751252275)
      ·
        refine ⟨25291409469427595626878413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16860939646285063751252275 25291409469427595626878413)
        ·
          refine ⟨9484278551035348360079405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25291409469427595626878413 9484278551035348360079405)
          ·
            refine ⟨3556604456638255635029777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9484278551035348360079405 3556604456638255635029777)
            ·
              refine ⟨2667453342478691726272333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3556604456638255635029777 2667453342478691726272333)
              ·
                refine ⟨1000295003429509397352125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2667453342478691726272333 1000295003429509397352125)
                ·
                  refine ⟨375110626286066024007047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1000295003429509397352125 375110626286066024007047)
                  ·
                    rfl

theorem cell20_821841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_821841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821841 prefixEnd_821841 := by exact prefixLift 821841
  have htrace : WordTrace (prefixWord ++ tailWord_821841) baseStart_821841 baseEnd_821841 := by
    simpa [prefixWord, tailWord_821841, baseEnd_821841] using wordTrace_append hprefix tailTrace_821841
  have hstable : (prefixWord ++ tailWord_821841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821841).length < 2 ^ (prefixWord ++ tailWord_821841).sum := by decide
  have hdescent : baseEnd_821841 < baseStart_821841 := by decide
  rcases family_descends (prefixWord ++ tailWord_821841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821879 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 3]
def baseStart_821879 : Nat := 118140960795 + 821879 * 2 ^ 59
def prefixEnd_821879 : Nat := 4983230072969 + 3 ^ 40 * 821879 * 2
def baseEnd_821879 : Nat := 375127970521506780740225

theorem tailTrace_821879 : CollatzResearch.WordTrace tailWord_821879 prefixEnd_821879 375127970521506780740225 := by
  unfold tailWord_821879
  simp only [CollatzResearch.WordTrace]
  refine ⟨29976389789480223603220691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19984259859653482402147127 29976389789480223603220691)
  ·
    refine ⟨44964584684220335404831037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29976389789480223603220691 44964584684220335404831037)
    ·
      refine ⟨16861719256582625776811639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44964584684220335404831037 16861719256582625776811639)
      ·
        refine ⟨25292578884873938665217459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16861719256582625776811639 25292578884873938665217459)
        ·
          refine ⟨37938868327310907997826189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25292578884873938665217459 37938868327310907997826189)
          ·
            refine ⟨14227075622741590499184821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37938868327310907997826189 14227075622741590499184821)
            ·
              refine ⟨1333788339632024109298577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14227075622741590499184821 1333788339632024109298577)
              ·
                refine ⟨1000341254724018081973933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1333788339632024109298577 1000341254724018081973933)
                ·
                  refine ⟨375127970521506780740225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1000341254724018081973933 375127970521506780740225)
                  ·
                    rfl

theorem cell20_821879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_821879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821879 prefixEnd_821879 := by exact prefixLift 821879
  have htrace : WordTrace (prefixWord ++ tailWord_821879) baseStart_821879 baseEnd_821879 := by
    simpa [prefixWord, tailWord_821879, baseEnd_821879] using wordTrace_append hprefix tailTrace_821879
  have hstable : (prefixWord ++ tailWord_821879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821879).length < 2 ^ (prefixWord ++ tailWord_821879).sum := by decide
  have hdescent : baseEnd_821879 < baseStart_821879 := by decide
  rcases family_descends (prefixWord ++ tailWord_821879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821927 : List Nat := [1, 1, 6, 3, 1, 2, 6]
def baseStart_821927 : Nat := 118140960795 + 821927 * 2 ^ 59
def prefixEnd_821927 : Nat := 4983230072969 + 3 ^ 40 * 821927 * 2
def baseEnd_821927 : Nat := 41683319892159105237781

theorem tailTrace_821927 : CollatzResearch.WordTrace tailWord_821927 prefixEnd_821927 41683319892159105237781 := by
  unfold tailWord_821927
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978140493306327800968035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19985426995537551867312023 29978140493306327800968035)
  ·
    refine ⟨44967210739959491701452053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29978140493306327800968035 44967210739959491701452053)
    ·
      refine ⟨2107838003435601173505565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44967210739959491701452053 2107838003435601173505565)
      ·
        refine ⟨790439251288350440064587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2107838003435601173505565 790439251288350440064587)
        ·
          refine ⟨1185658876932525660096881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790439251288350440064587 1185658876932525660096881)
          ·
            refine ⟨889244157699394245072661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185658876932525660096881 889244157699394245072661)
            ·
              refine ⟨41683319892159105237781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 889244157699394245072661 41683319892159105237781)
              ·
                rfl

theorem cell20_821927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 6].length) (baseStart_821927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821927 prefixEnd_821927 := by exact prefixLift 821927
  have htrace : WordTrace (prefixWord ++ tailWord_821927) baseStart_821927 baseEnd_821927 := by
    simpa [prefixWord, tailWord_821927, baseEnd_821927] using wordTrace_append hprefix tailTrace_821927
  have hstable : (prefixWord ++ tailWord_821927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821927).length < 2 ^ (prefixWord ++ tailWord_821927).sum := by decide
  have hdescent : baseEnd_821927 < baseStart_821927 := by decide
  rcases family_descends (prefixWord ++ tailWord_821927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821934 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_821934 : Nat := 118140960795 + 821934 * 2 ^ 59
def prefixEnd_821934 : Nat := 4983230072969 + 3 ^ 40 * 821934 * 2
def baseEnd_821934 : Nat := 375153074020171033906667

theorem tailTrace_821934 : CollatzResearch.WordTrace tailWord_821934 prefixEnd_821934 375153074020171033906667 := by
  unfold tailWord_821934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747299475535120999559107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19985597202853978664315237 3747299475535120999559107)
  ·
    refine ⟨5620949213302681499338661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3747299475535120999559107 5620949213302681499338661)
    ·
      refine ⟨1053927977494252781125999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5620949213302681499338661 1053927977494252781125999)
      ·
        refine ⟨1580891966241379171688999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053927977494252781125999 1580891966241379171688999)
        ·
          refine ⟨2371337949362068757533499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580891966241379171688999 2371337949362068757533499)
          ·
            refine ⟨3557006924043103136300249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371337949362068757533499 3557006924043103136300249)
            ·
              refine ⟨2667755193032327352225187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3557006924043103136300249 2667755193032327352225187)
              ·
                refine ⟨4001632789548491028337781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2667755193032327352225187 4001632789548491028337781)
                ·
                  refine ⟨375153074020171033906667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4001632789548491028337781 375153074020171033906667)
                  ·
                    rfl

theorem cell20_821934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_821934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821934 prefixEnd_821934 := by exact prefixLift 821934
  have htrace : WordTrace (prefixWord ++ tailWord_821934) baseStart_821934 baseEnd_821934 := by
    simpa [prefixWord, tailWord_821934, baseEnd_821934] using wordTrace_append hprefix tailTrace_821934
  have hstable : (prefixWord ++ tailWord_821934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821934).length < 2 ^ (prefixWord ++ tailWord_821934).sum := by decide
  have hdescent : baseEnd_821934 < baseStart_821934 := by decide
  rcases family_descends (prefixWord ++ tailWord_821934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821937 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 4]
def baseStart_821937 : Nat := 118140960795 + 821937 * 2 ^ 59
def prefixEnd_821937 : Nat := 4983230072969 + 3 ^ 40 * 821937 * 2
def baseEnd_821937 : Nat := 375154443301916356806655

theorem tailTrace_821937 : CollatzResearch.WordTrace tailWord_821937 prefixEnd_821937 375154443301916356806655 := by
  unfold tailWord_821937
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978505223270099508832065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19985670148846733005888043 29978505223270099508832065)
  ·
    refine ⟨22483878917452574631624049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29978505223270099508832065 22483878917452574631624049)
    ·
      refine ⟨16862909188089430973718037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22483878917452574631624049 16862909188089430973718037)
      ·
        refine ⟨790448868191692076893033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16862909188089430973718037 790448868191692076893033)
        ·
          refine ⟨592836651143769057669775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790448868191692076893033 592836651143769057669775)
          ·
            refine ⟨889254976715653586504663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592836651143769057669775 889254976715653586504663)
            ·
              refine ⟨1333882465073480379756995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889254976715653586504663 1333882465073480379756995)
              ·
                refine ⟨2000823697610220569635493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333882465073480379756995 2000823697610220569635493)
                ·
                  refine ⟨375154443301916356806655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000823697610220569635493 375154443301916356806655)
                  ·
                    rfl

theorem cell20_821937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_821937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821937 prefixEnd_821937 := by exact prefixLift 821937
  have htrace : WordTrace (prefixWord ++ tailWord_821937) baseStart_821937 baseEnd_821937 := by
    simpa [prefixWord, tailWord_821937, baseEnd_821937] using wordTrace_append hprefix tailTrace_821937
  have hstable : (prefixWord ++ tailWord_821937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821937).length < 2 ^ (prefixWord ++ tailWord_821937).sum := by decide
  have hdescent : baseEnd_821937 < baseStart_821937 := by decide
  rcases family_descends (prefixWord ++ tailWord_821937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821941 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_821941 : Nat := 118140960795 + 821941 * 2 ^ 59
def prefixEnd_821941 : Nat := 4983230072969 + 3 ^ 40 * 821941 * 2
def baseEnd_821941 : Nat := 375156269010910120673305

theorem tailTrace_821941 : CollatzResearch.WordTrace tailWord_821941 prefixEnd_821941 375156269010910120673305 := by
  unfold tailWord_821941
  simp only [CollatzResearch.WordTrace]
  refine ⟨29978651115255608191977677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19985767410170405461318451 29978651115255608191977677)
  ·
    refine ⟨11241994168220853071991629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29978651115255608191977677 11241994168220853071991629)
    ·
      refine ⟨4215747813082819901996861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11241994168220853071991629 4215747813082819901996861)
      ·
        refine ⟨1580905429906057463248823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4215747813082819901996861 1580905429906057463248823)
        ·
          refine ⟨2371358144859086194873235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1580905429906057463248823 2371358144859086194873235)
          ·
            refine ⟨3557037217288629292309853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2371358144859086194873235 3557037217288629292309853)
            ·
              refine ⟨1333888956483235984616195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3557037217288629292309853 1333888956483235984616195)
              ·
                refine ⟨2000833434724853976924293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1333888956483235984616195 2000833434724853976924293)
                ·
                  refine ⟨375156269010910120673305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2000833434724853976924293 375156269010910120673305)
                  ·
                    rfl

theorem cell20_821941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_821941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821941 prefixEnd_821941 := by exact prefixLift 821941
  have htrace : WordTrace (prefixWord ++ tailWord_821941) baseStart_821941 baseEnd_821941 := by
    simpa [prefixWord, tailWord_821941, baseEnd_821941] using wordTrace_append hprefix tailTrace_821941
  have hstable : (prefixWord ++ tailWord_821941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821941).length < 2 ^ (prefixWord ++ tailWord_821941).sum := by decide
  have hdescent : baseEnd_821941 < baseStart_821941 := by decide
  rcases family_descends (prefixWord ++ tailWord_821941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_821992 : List Nat := [2, 1, 4, 1, 5, 1, 2, 2, 2]
def baseStart_821992 : Nat := 118140960795 + 821992 * 2 ^ 59
def prefixEnd_821992 : Nat := 4983230072969 + 3 ^ 40 * 821992 * 2
def baseEnd_821992 : Nat := 375179546800580609973097

theorem tailTrace_821992 : CollatzResearch.WordTrace tailWord_821992 prefixEnd_821992 375179546800580609973097 := by
  unfold tailWord_821992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990255619035421951042115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19987007492047229268056153 14990255619035421951042115)
  ·
    refine ⟨22485383428553132926563173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14990255619035421951042115 22485383428553132926563173)
    ·
      refine ⟨4216009392853712423730595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22485383428553132926563173 4216009392853712423730595)
      ·
        refine ⟨6324014089280568635595893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216009392853712423730595 6324014089280568635595893)
        ·
          refine ⟨592876320870053309587115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6324014089280568635595893 592876320870053309587115)
          ·
            refine ⟨889314481305079964380673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592876320870053309587115 889314481305079964380673)
            ·
              refine ⟨666985860978809973285505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889314481305079964380673 666985860978809973285505)
              ·
                refine ⟨500239395734107479964129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 666985860978809973285505 500239395734107479964129)
                ·
                  refine ⟨375179546800580609973097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500239395734107479964129 375179546800580609973097)
                  ·
                    rfl

theorem cell20_821992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_821992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_821992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_821992 prefixEnd_821992 := by exact prefixLift 821992
  have htrace : WordTrace (prefixWord ++ tailWord_821992) baseStart_821992 baseEnd_821992 := by
    simpa [prefixWord, tailWord_821992, baseEnd_821992] using wordTrace_append hprefix tailTrace_821992
  have hstable : (prefixWord ++ tailWord_821992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_821992).length < 2 ^ (prefixWord ++ tailWord_821992).sum := by decide
  have hdescent : baseEnd_821992 < baseStart_821992 := by decide
  rcases family_descends (prefixWord ++ tailWord_821992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822024 : List Nat := [2, 1, 3, 2, 2, 3, 3, 4]
def baseStart_822024 : Nat := 118140960795 + 822024 * 2 ^ 59
def prefixEnd_822024 : Nat := 4983230072969 + 3 ^ 40 * 822024 * 2
def baseEnd_822024 : Nat := 125064717490843573635433

theorem tailTrace_822024 : CollatzResearch.WordTrace tailWord_822024 prefixEnd_822024 125064717490843573635433 := by
  unfold tailWord_822024
  simp only [CollatzResearch.WordTrace]
  refine ⟨14990839186977456683624563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19987785582636608911499417 14990839186977456683624563)
  ·
    refine ⟨22486258780466185025436845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14990839186977456683624563 22486258780466185025436845)
    ·
      refine ⟨8432347042674819384538817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22486258780466185025436845 8432347042674819384538817)
      ·
        refine ⟨6324260282006114538404113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8432347042674819384538817 6324260282006114538404113)
        ·
          refine ⟨4743195211504585903803085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6324260282006114538404113 4743195211504585903803085)
          ·
            refine ⟨1778698204314219713926157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4743195211504585903803085 1778698204314219713926157)
            ·
              refine ⟨667011826617832392722309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1778698204314219713926157 667011826617832392722309)
              ·
                refine ⟨125064717490843573635433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 667011826617832392722309 125064717490843573635433)
                ·
                  rfl

theorem cell20_822024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_822024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822024 prefixEnd_822024 := by exact prefixLift 822024
  have htrace : WordTrace (prefixWord ++ tailWord_822024) baseStart_822024 baseEnd_822024 := by
    simpa [prefixWord, tailWord_822024, baseEnd_822024] using wordTrace_append hprefix tailTrace_822024
  have hstable : (prefixWord ++ tailWord_822024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822024).length < 2 ^ (prefixWord ++ tailWord_822024).sum := by decide
  have hdescent : baseEnd_822024 < baseStart_822024 := by decide
  rcases family_descends (prefixWord ++ tailWord_822024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822048 : List Nat := [2, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_822048 : Nat := 118140960795 + 822048 * 2 ^ 59
def prefixEnd_822048 : Nat := 4983230072969 + 3 ^ 40 * 822048 * 2
def baseEnd_822048 : Nat := 375205106726493304106201

theorem tailTrace_822048 : CollatzResearch.WordTrace tailWord_822048 prefixEnd_822048 375205106726493304106201 := by
  unfold tailWord_822048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14991276862933982733061399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19988369150578643644081865 14991276862933982733061399)
  ·
    refine ⟨22486915294400974099592099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14991276862933982733061399 22486915294400974099592099)
    ·
      refine ⟨33730372941601461149388149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22486915294400974099592099 33730372941601461149388149)
      ·
        refine ⟨3162222463275136982755139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33730372941601461149388149 3162222463275136982755139)
        ·
          refine ⟨4743333694912705474132709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162222463275136982755139 4743333694912705474132709)
          ·
            refine ⟨889375067796132276399883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4743333694912705474132709 889375067796132276399883)
            ·
              refine ⟨1334062601694198414599825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889375067796132276399883 1334062601694198414599825)
              ·
                refine ⟨1000546951270648810949869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334062601694198414599825 1000546951270648810949869)
                ·
                  refine ⟨375205106726493304106201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1000546951270648810949869 375205106726493304106201)
                  ·
                    rfl

theorem cell20_822048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_822048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822048 prefixEnd_822048 := by exact prefixLift 822048
  have htrace : WordTrace (prefixWord ++ tailWord_822048) baseStart_822048 baseEnd_822048 := by
    simpa [prefixWord, tailWord_822048, baseEnd_822048] using wordTrace_append hprefix tailTrace_822048
  have hstable : (prefixWord ++ tailWord_822048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822048).length < 2 ^ (prefixWord ++ tailWord_822048).sum := by decide
  have hdescent : baseEnd_822048 < baseStart_822048 := by decide
  rcases family_descends (prefixWord ++ tailWord_822048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822059 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_822059 : Nat := 118140960795 + 822059 * 2 ^ 59
def prefixEnd_822059 : Nat := 4983230072969 + 3 ^ 40 * 822059 * 2
def baseEnd_822059 : Nat := 375210127426226154739489

theorem tailTrace_822059 : CollatzResearch.WordTrace tailWord_822059 prefixEnd_822059 375210127426226154739489 := by
  unfold tailWord_822059
  simp only [CollatzResearch.WordTrace]
  refine ⟨29982954928828114344773231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19988636619218742896515487 29982954928828114344773231)
  ·
    refine ⟨44974432393242171517159847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29982954928828114344773231 44974432393242171517159847)
    ·
      refine ⟨67461648589863257275739771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44974432393242171517159847 67461648589863257275739771)
      ·
        refine ⟨101192472884794885913609657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67461648589863257275739771 101192472884794885913609657)
        ·
          refine ⟨75894354663596164435207243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101192472884794885913609657 75894354663596164435207243)
          ·
            refine ⟨113841531995394246652810865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75894354663596164435207243 113841531995394246652810865)
            ·
              refine ⟨85381148996545684989608149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113841531995394246652810865 85381148996545684989608149)
              ·
                refine ⟨2001120679606539491943941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85381148996545684989608149 2001120679606539491943941)
                ·
                  refine ⟨375210127426226154739489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001120679606539491943941 375210127426226154739489)
                  ·
                    rfl

theorem cell20_822059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_822059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822059 prefixEnd_822059 := by exact prefixLift 822059
  have htrace : WordTrace (prefixWord ++ tailWord_822059) baseStart_822059 baseEnd_822059 := by
    simpa [prefixWord, tailWord_822059, baseEnd_822059] using wordTrace_append hprefix tailTrace_822059
  have hstable : (prefixWord ++ tailWord_822059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822059).length < 2 ^ (prefixWord ++ tailWord_822059).sum := by decide
  have hdescent : baseEnd_822059 < baseStart_822059 := by decide
  rcases family_descends (prefixWord ++ tailWord_822059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822100 : List Nat := [2, 4, 1, 1, 4, 2, 6]
def baseStart_822100 : Nat := 118140960795 + 822100 * 2 ^ 59
def prefixEnd_822100 : Nat := 4983230072969 + 3 ^ 40 * 822100 * 2
def baseEnd_822100 : Nat := 41692093438156914930295

theorem tailTrace_822100 : CollatzResearch.WordTrace tailWord_822100 prefixEnd_822100 41692093438156914930295 := by
  unfold tailWord_822100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14992225160839789173507877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19989633547786385564677169 14992225160839789173507877)
  ·
    refine ⟨2811042217657460470032727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14992225160839789173507877 2811042217657460470032727)
    ·
      refine ⟨4216563326486190705049091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2811042217657460470032727 4216563326486190705049091)
      ·
        refine ⟨6324844989729286057573637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4216563326486190705049091 6324844989729286057573637)
        ·
          refine ⟨1185908435574241135795057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6324844989729286057573637 1185908435574241135795057)
          ·
            refine ⟨889431326680680851846293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185908435574241135795057 889431326680680851846293)
            ·
              refine ⟨41692093438156914930295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 889431326680680851846293 41692093438156914930295)
              ·
                rfl

theorem cell20_822100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 6].length) (baseStart_822100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822100 prefixEnd_822100 := by exact prefixLift 822100
  have htrace : WordTrace (prefixWord ++ tailWord_822100) baseStart_822100 baseEnd_822100 := by
    simpa [prefixWord, tailWord_822100, baseEnd_822100] using wordTrace_append hprefix tailTrace_822100
  have hstable : (prefixWord ++ tailWord_822100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822100).length < 2 ^ (prefixWord ++ tailWord_822100).sum := by decide
  have hdescent : baseEnd_822100 < baseStart_822100 := by decide
  rcases family_descends (prefixWord ++ tailWord_822100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822135 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 4]
def baseStart_822135 : Nat := 118140960795 + 822135 * 2 ^ 59
def prefixEnd_822135 : Nat := 4983230072969 + 3 ^ 40 * 822135 * 2
def baseEnd_822135 : Nat := 375244815897107668205845

theorem tailTrace_822135 : CollatzResearch.WordTrace tailWord_822135 prefixEnd_822135 375244815897107668205845 := by
  unfold tailWord_822135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29985726876552779324539859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19990484584368519549693239 29985726876552779324539859)
  ·
    refine ⟨44978590314829168986809789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29985726876552779324539859 44978590314829168986809789)
    ·
      refine ⟨16866971368060938370053671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44978590314829168986809789 16866971368060938370053671)
      ·
        refine ⟨25300457052091407555080507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16866971368060938370053671 25300457052091407555080507)
        ·
          refine ⟨37950685578137111332620761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25300457052091407555080507 37950685578137111332620761)
          ·
            refine ⟨28463014183602833499465571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37950685578137111332620761 28463014183602833499465571)
            ·
              refine ⟨42694521275404250249198357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28463014183602833499465571 42694521275404250249198357)
              ·
                refine ⟨2001305684784574230431173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42694521275404250249198357 2001305684784574230431173)
                ·
                  refine ⟨375244815897107668205845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001305684784574230431173 375244815897107668205845)
                  ·
                    rfl

theorem cell20_822135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_822135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822135 prefixEnd_822135 := by exact prefixLift 822135
  have htrace : WordTrace (prefixWord ++ tailWord_822135) baseStart_822135 baseEnd_822135 := by
    simpa [prefixWord, tailWord_822135, baseEnd_822135] using wordTrace_append hprefix tailTrace_822135
  have hstable : (prefixWord ++ tailWord_822135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822135).length < 2 ^ (prefixWord ++ tailWord_822135).sum := by decide
  have hdescent : baseEnd_822135 < baseStart_822135 := by decide
  rcases family_descends (prefixWord ++ tailWord_822135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822228 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_822228 : Nat := 118140960795 + 822228 * 2 ^ 59
def prefixEnd_822228 : Nat := 4983230072969 + 3 ^ 40 * 822228 * 2
def baseEnd_822228 : Nat := 375287263631212678105465

theorem tailTrace_822228 : CollatzResearch.WordTrace tailWord_822228 prefixEnd_822228 375287263631212678105465 := by
  unfold tailWord_822228
  simp only [CollatzResearch.WordTrace]
  refine ⟨14994559432607928103837669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19992745910143904138450225 14994559432607928103837669)
  ·
    refine ⟨2811479893613986519469563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14994559432607928103837669 2811479893613986519469563)
    ·
      refine ⟨4217219840420979779204345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2811479893613986519469563 4217219840420979779204345)
      ·
        refine ⟨3162914880315734834403259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4217219840420979779204345 3162914880315734834403259)
        ·
          refine ⟨4744372320473602251604889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3162914880315734834403259 4744372320473602251604889)
          ·
            refine ⟨3558279240355201688703667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4744372320473602251604889 3558279240355201688703667)
            ·
              refine ⟨5337418860532802533055501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3558279240355201688703667 5337418860532802533055501)
              ·
                refine ⟨2001532072699800949895813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5337418860532802533055501 2001532072699800949895813)
                ·
                  refine ⟨375287263631212678105465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001532072699800949895813 375287263631212678105465)
                  ·
                    rfl

theorem cell20_822228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_822228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822228 prefixEnd_822228 := by exact prefixLift 822228
  have htrace : WordTrace (prefixWord ++ tailWord_822228) baseStart_822228 baseEnd_822228 := by
    simpa [prefixWord, tailWord_822228, baseEnd_822228] using wordTrace_append hprefix tailTrace_822228
  have hstable : (prefixWord ++ tailWord_822228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822228).length < 2 ^ (prefixWord ++ tailWord_822228).sum := by decide
  have hdescent : baseEnd_822228 < baseStart_822228 := by decide
  rcases family_descends (prefixWord ++ tailWord_822228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822258 : List Nat := [3, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_822258 : Nat := 118140960795 + 822258 * 2 ^ 59
def prefixEnd_822258 : Nat := 4983230072969 + 3 ^ 40 * 822258 * 2
def baseEnd_822258 : Nat := 375300956448665907105343

theorem tailTrace_822258 : CollatzResearch.WordTrace tailWord_822258 prefixEnd_822258 375300956448665907105343 := by
  unfold tailWord_822258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7497553263776792832816857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19993475370071447554178285 7497553263776792832816857)
  ·
    refine ⟨5623164947832594624612643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7497553263776792832816857 5623164947832594624612643)
    ·
      refine ⟨8434747421748891936918965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5623164947832594624612643 8434747421748891936918965)
      ·
        refine ⟨790757570788958619086153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8434747421748891936918965 790757570788958619086153)
        ·
          refine ⟨593068178091718964314615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790757570788958619086153 593068178091718964314615)
          ·
            refine ⟨889602267137578446471923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593068178091718964314615 889602267137578446471923)
            ·
              refine ⟨1334403400706367669707885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889602267137578446471923 1334403400706367669707885)
              ·
                refine ⟨500401275264887876140457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1334403400706367669707885 500401275264887876140457)
                ·
                  refine ⟨375300956448665907105343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500401275264887876140457 375300956448665907105343)
                  ·
                    rfl

theorem cell20_822258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_822258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822258 prefixEnd_822258 := by exact prefixLift 822258
  have htrace : WordTrace (prefixWord ++ tailWord_822258) baseStart_822258 baseEnd_822258 := by
    simpa [prefixWord, tailWord_822258, baseEnd_822258] using wordTrace_append hprefix tailTrace_822258
  have hstable : (prefixWord ++ tailWord_822258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822258).length < 2 ^ (prefixWord ++ tailWord_822258).sum := by decide
  have hdescent : baseEnd_822258 < baseStart_822258 := by decide
  rcases family_descends (prefixWord ++ tailWord_822258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822262 : List Nat := [5, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_822262 : Nat := 118140960795 + 822262 * 2 ^ 59
def prefixEnd_822262 : Nat := 4983230072969 + 3 ^ 40 * 822262 * 2
def baseEnd_822262 : Nat := 375302782157659670971993

theorem tailTrace_822262 : CollatzResearch.WordTrace tailWord_822262 prefixEnd_822262 375302782157659670971993 := by
  unfold tailWord_822262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1874397434193292500900815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19993572631395120009608693 1874397434193292500900815)
  ·
    refine ⟨2811596151289938751351223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1874397434193292500900815 2811596151289938751351223)
    ·
      refine ⟨4217394226934908127026835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2811596151289938751351223 4217394226934908127026835)
      ·
        refine ⟨6326091340402362190540253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4217394226934908127026835 6326091340402362190540253)
        ·
          refine ⟨2372284252650885821452595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6326091340402362190540253 2372284252650885821452595)
          ·
            refine ⟨3558426378976328732178893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2372284252650885821452595 3558426378976328732178893)
            ·
              refine ⟨1334409892116123274567085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3558426378976328732178893 1334409892116123274567085)
              ·
                refine ⟨500403709543546227962657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1334409892116123274567085 500403709543546227962657)
                ·
                  refine ⟨375302782157659670971993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500403709543546227962657 375302782157659670971993)
                  ·
                    rfl

theorem cell20_822262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_822262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822262 prefixEnd_822262 := by exact prefixLift 822262
  have htrace : WordTrace (prefixWord ++ tailWord_822262) baseStart_822262 baseEnd_822262 := by
    simpa [prefixWord, tailWord_822262, baseEnd_822262] using wordTrace_append hprefix tailTrace_822262
  have hstable : (prefixWord ++ tailWord_822262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822262).length < 2 ^ (prefixWord ++ tailWord_822262).sum := by decide
  have hdescent : baseEnd_822262 < baseStart_822262 := by decide
  rcases family_descends (prefixWord ++ tailWord_822262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822273 : List Nat := [1, 2, 4, 1, 2, 4, 6]
def baseStart_822273 : Nat := 118140960795 + 822273 * 2 ^ 59
def prefixEnd_822273 : Nat := 4983230072969 + 3 ^ 40 * 822273 * 2
def baseEnd_822273 : Nat := 41700866984154724622809

theorem tailTrace_822273 : CollatzResearch.WordTrace tailWord_822273 prefixEnd_822273 41700866984154724622809 := by
  unfold tailWord_822273
  simp only [CollatzResearch.WordTrace]
  refine ⟨29990760150052828893063473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19993840100035219262042315 29990760150052828893063473)
  ·
    refine ⟨22493070112539621669797605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29990760150052828893063473 22493070112539621669797605)
    ·
      refine ⟨4217450646101179063087051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22493070112539621669797605 4217450646101179063087051)
      ·
        refine ⟨6326175969151768594630577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4217450646101179063087051 6326175969151768594630577)
        ·
          refine ⟨4744631976863826445972933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6326175969151768594630577 4744631976863826445972933)
          ·
            refine ⟨889618495661967458619925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4744631976863826445972933 889618495661967458619925)
            ·
              refine ⟨41700866984154724622809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 889618495661967458619925 41700866984154724622809)
              ·
                rfl

theorem cell20_822273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 6].length) (baseStart_822273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822273 prefixEnd_822273 := by exact prefixLift 822273
  have htrace : WordTrace (prefixWord ++ tailWord_822273) baseStart_822273 baseEnd_822273 := by
    simpa [prefixWord, tailWord_822273, baseEnd_822273] using wordTrace_append hprefix tailTrace_822273
  have hstable : (prefixWord ++ tailWord_822273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822273).length < 2 ^ (prefixWord ++ tailWord_822273).sum := by decide
  have hdescent : baseEnd_822273 < baseStart_822273 := by decide
  rcases family_descends (prefixWord ++ tailWord_822273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822280 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_822280 : Nat := 118140960795 + 822280 * 2 ^ 59
def prefixEnd_822280 : Nat := 4983230072969 + 3 ^ 40 * 822280 * 2
def baseEnd_822280 : Nat := 375310997848131608371919

theorem tailTrace_822280 : CollatzResearch.WordTrace tailWord_822280 prefixEnd_822280 375310997848131608371919 := by
  unfold tailWord_822280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14995507730513734544284147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19994010307351646059045529 14995507730513734544284147)
  ·
    refine ⟨22493261595770601816426221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14995507730513734544284147 22493261595770601816426221)
    ·
      refine ⟨8434973098413975681159833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22493261595770601816426221 8434973098413975681159833)
      ·
        refine ⟨6326229823810481760869875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8434973098413975681159833 6326229823810481760869875)
        ·
          refine ⟨9489344735715722641304813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6326229823810481760869875 9489344735715722641304813)
          ·
            refine ⟨3558504275893395990489305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9489344735715722641304813 3558504275893395990489305)
            ·
              refine ⟨2668878206920046992866979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3558504275893395990489305 2668878206920046992866979)
              ·
                refine ⟨4003317310380070489300469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2668878206920046992866979 4003317310380070489300469)
                ·
                  refine ⟨375310997848131608371919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4003317310380070489300469 375310997848131608371919)
                  ·
                    rfl

theorem cell20_822280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_822280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822280 prefixEnd_822280 := by exact prefixLift 822280
  have htrace : WordTrace (prefixWord ++ tailWord_822280) baseStart_822280 baseEnd_822280 := by
    simpa [prefixWord, tailWord_822280, baseEnd_822280] using wordTrace_append hprefix tailTrace_822280
  have hstable : (prefixWord ++ tailWord_822280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822280).length < 2 ^ (prefixWord ++ tailWord_822280).sum := by decide
  have hdescent : baseEnd_822280 < baseStart_822280 := by decide
  rcases family_descends (prefixWord ++ tailWord_822280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822297 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 3]
def baseStart_822297 : Nat := 118140960795 + 822297 * 2 ^ 59
def prefixEnd_822297 : Nat := 4983230072969 + 3 ^ 40 * 822297 * 2
def baseEnd_822297 : Nat := 375318757111355104805183

theorem tailTrace_822297 : CollatzResearch.WordTrace tailWord_822297 prefixEnd_822297 375318757111355104805183 := by
  unfold tailWord_822297
  simp only [CollatzResearch.WordTrace]
  refine ⟨29991635501965880991937145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19994423667977253994624763 29991635501965880991937145)
  ·
    refine ⟨22493726626474410743952859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29991635501965880991937145 22493726626474410743952859)
    ·
      refine ⟨33740589939711616115929289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22493726626474410743952859 33740589939711616115929289)
      ·
        refine ⟨25305442454783712086946967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33740589939711616115929289 25305442454783712086946967)
        ·
          refine ⟨37958163682175568130420451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25305442454783712086946967 37958163682175568130420451)
          ·
            refine ⟨56937245523263352195630677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37958163682175568130420451 56937245523263352195630677)
            ·
              refine ⟨667233345975742408542547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 56937245523263352195630677 667233345975742408542547)
              ·
                refine ⟨1000850018963613612813821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667233345975742408542547 1000850018963613612813821)
                ·
                  refine ⟨375318757111355104805183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1000850018963613612813821 375318757111355104805183)
                  ·
                    rfl

theorem cell20_822297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_822297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822297 prefixEnd_822297 := by exact prefixLift 822297
  have htrace : WordTrace (prefixWord ++ tailWord_822297) baseStart_822297 baseEnd_822297 := by
    simpa [prefixWord, tailWord_822297, baseEnd_822297] using wordTrace_append hprefix tailTrace_822297
  have hstable : (prefixWord ++ tailWord_822297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822297).length < 2 ^ (prefixWord ++ tailWord_822297).sum := by decide
  have hdescent : baseEnd_822297 < baseStart_822297 := by decide
  rcases family_descends (prefixWord ++ tailWord_822297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822332 : List Nat := [2, 2, 2, 2, 2, 10]
def baseStart_822332 : Nat := 118140960795 + 822332 * 2 ^ 59
def prefixEnd_822332 : Nat := 4983230072969 + 3 ^ 40 * 822332 * 2
def baseEnd_822332 : Nat := 13901286372779649579199

theorem tailTrace_822332 : CollatzResearch.WordTrace tailWord_822332 prefixEnd_822332 13901286372779649579199 := by
  unfold tailWord_822332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14996456028419540984730625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19995274704559387979640833 14996456028419540984730625)
  ·
    refine ⟨11247342021314655738547969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14996456028419540984730625 11247342021314655738547969)
    ·
      refine ⟨8435506515985991803910977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11247342021314655738547969 8435506515985991803910977)
      ·
        refine ⟨6326629886989493852933233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8435506515985991803910977 6326629886989493852933233)
        ·
          refine ⟨4744972415242120389699925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6326629886989493852933233 4744972415242120389699925)
          ·
            refine ⟨13901286372779649579199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4744972415242120389699925 13901286372779649579199)
            ·
              rfl

theorem cell20_822332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 10].length) (baseStart_822332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822332 prefixEnd_822332 := by exact prefixLift 822332
  have htrace : WordTrace (prefixWord ++ tailWord_822332) baseStart_822332 baseEnd_822332 := by
    simpa [prefixWord, tailWord_822332, baseEnd_822332] using wordTrace_append hprefix tailTrace_822332
  have hstable : (prefixWord ++ tailWord_822332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822332).length < 2 ^ (prefixWord ++ tailWord_822332).sum := by decide
  have hdescent : baseEnd_822332 < baseStart_822332 := by decide
  rcases family_descends (prefixWord ++ tailWord_822332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822418 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_822418 : Nat := 118140960795 + 822418 * 2 ^ 59
def prefixEnd_822418 : Nat := 4983230072969 + 3 ^ 40 * 822418 * 2
def baseEnd_822418 : Nat := 375373984808416461771355

theorem tailTrace_822418 : CollatzResearch.WordTrace tailWord_822418 prefixEnd_822418 375373984808416461771355 := by
  unfold tailWord_822418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7499012183631879664272977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19997365823018345771394605 7499012183631879664272977)
  ·
    refine ⟨5624259137723909748204733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7499012183631879664272977 5624259137723909748204733)
    ·
      refine ⟨2109097176646466155576775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5624259137723909748204733 2109097176646466155576775)
      ·
        refine ⟨3163645764969699233365163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109097176646466155576775 3163645764969699233365163)
        ·
          refine ⟨4745468647454548850047745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163645764969699233365163 4745468647454548850047745)
          ·
            refine ⟨3559101485590911637535809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4745468647454548850047745 3559101485590911637535809)
            ·
              refine ⟨2669326114193183728151857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3559101485590911637535809 2669326114193183728151857)
              ·
                refine ⟨2001994585644887796113893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669326114193183728151857 2001994585644887796113893)
                ·
                  refine ⟨375373984808416461771355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2001994585644887796113893 375373984808416461771355)
                  ·
                    rfl

theorem cell20_822418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_822418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822418 prefixEnd_822418 := by exact prefixLift 822418
  have htrace : WordTrace (prefixWord ++ tailWord_822418) baseStart_822418 baseEnd_822418 := by
    simpa [prefixWord, tailWord_822418, baseEnd_822418] using wordTrace_append hprefix tailTrace_822418
  have hstable : (prefixWord ++ tailWord_822418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822418).length < 2 ^ (prefixWord ++ tailWord_822418).sum := by decide
  have hdescent : baseEnd_822418 < baseStart_822418 := by decide
  rcases family_descends (prefixWord ++ tailWord_822418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822431 : List Nat := [1, 1, 2, 6, 3, 1, 1, 3, 2]
def baseStart_822431 : Nat := 118140960795 + 822431 * 2 ^ 59
def prefixEnd_822431 : Nat := 4983230072969 + 3 ^ 40 * 822431 * 2
def baseEnd_822431 : Nat := 375379918362646194337969

theorem tailTrace_822431 : CollatzResearch.WordTrace tailWord_822431 prefixEnd_822431 375379918362646194337969 := by
  unfold tailWord_822431
  simp only [CollatzResearch.WordTrace]
  refine ⟨29996522883480421877315147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19997681922320281251543431 29996522883480421877315147)
  ·
    refine ⟨44994784325220632815972721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29996522883480421877315147 44994784325220632815972721)
    ·
      refine ⟨33746088243915474611979541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44994784325220632815972721 33746088243915474611979541)
      ·
        refine ⟨1581847886433537872436541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33746088243915474611979541 1581847886433537872436541)
        ·
          refine ⟨593192957412576702163703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1581847886433537872436541 593192957412576702163703)
          ·
            refine ⟨889789436118865053245555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593192957412576702163703 889789436118865053245555)
            ·
              refine ⟨1334684154178297579868333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889789436118865053245555 1334684154178297579868333)
              ·
                refine ⟨500506557816861592450625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1334684154178297579868333 500506557816861592450625)
                ·
                  refine ⟨375379918362646194337969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500506557816861592450625 375379918362646194337969)
                  ·
                    rfl

theorem cell20_822431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 2].length) (baseStart_822431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822431 prefixEnd_822431 := by exact prefixLift 822431
  have htrace : WordTrace (prefixWord ++ tailWord_822431) baseStart_822431 baseEnd_822431 := by
    simpa [prefixWord, tailWord_822431, baseEnd_822431] using wordTrace_append hprefix tailTrace_822431
  have hstable : (prefixWord ++ tailWord_822431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822431).length < 2 ^ (prefixWord ++ tailWord_822431).sum := by decide
  have hdescent : baseEnd_822431 < baseStart_822431 := by decide
  rcases family_descends (prefixWord ++ tailWord_822431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822442 : List Nat := [3, 1, 5, 1, 1, 3, 6]
def baseStart_822442 : Nat := 118140960795 + 822442 * 2 ^ 59
def prefixEnd_822442 : Nat := 4983230072969 + 3 ^ 40 * 822442 * 2
def baseEnd_822442 : Nat := 41709437673597671663473

theorem tailTrace_822442 : CollatzResearch.WordTrace tailWord_822442 prefixEnd_822442 41709437673597671663473 := by
  unfold tailWord_822442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7499231021610142688991395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19997949390960380503977053 7499231021610142688991395)
  ·
    refine ⟨11248846532415214033487093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7499231021610142688991395 11248846532415214033487093)
    ·
      refine ⟨1054579362413926315639415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11248846532415214033487093 1054579362413926315639415)
      ·
        refine ⟨1581869043620889473459123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1054579362413926315639415 1581869043620889473459123)
        ·
          refine ⟨2372803565431334210188685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1581869043620889473459123 2372803565431334210188685)
          ·
            refine ⟨889801337036750328820757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2372803565431334210188685 889801337036750328820757)
            ·
              refine ⟨41709437673597671663473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 889801337036750328820757 41709437673597671663473)
              ·
                rfl

theorem cell20_822442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 6].length) (baseStart_822442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822442 prefixEnd_822442 := by exact prefixLift 822442
  have htrace : WordTrace (prefixWord ++ tailWord_822442) baseStart_822442 baseEnd_822442 := by
    simpa [prefixWord, tailWord_822442, baseEnd_822442] using wordTrace_append hprefix tailTrace_822442
  have hstable : (prefixWord ++ tailWord_822442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822442).length < 2 ^ (prefixWord ++ tailWord_822442).sum := by decide
  have hdescent : baseEnd_822442 < baseStart_822442 := by decide
  rcases family_descends (prefixWord ++ tailWord_822442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822501 : List Nat := [1, 3, 1, 4, 4, 7]
def baseStart_822501 : Nat := 118140960795 + 822501 * 2 ^ 59
def prefixEnd_822501 : Nat := 4983230072969 + 3 ^ 40 * 822501 * 2
def baseEnd_822501 : Nat := 13904143269260631926087

theorem tailTrace_822501 : CollatzResearch.WordTrace tailWord_822501 prefixEnd_822501 13904143269260631926087 := by
  unfold tailWord_822501
  simp only [CollatzResearch.WordTrace]
  refine ⟨29999075993226823832363357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19999383995484549221575571 29999075993226823832363357)
  ·
    refine ⟨11249653497460058937136259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29999075993226823832363357 11249653497460058937136259)
    ·
      refine ⟨16874480246190088405704389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11249653497460058937136259 16874480246190088405704389)
      ·
        refine ⟨3163965046160641576069573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16874480246190088405704389 3163965046160641576069573)
        ·
          refine ⟨593243446155120295513045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3163965046160641576069573 593243446155120295513045)
          ·
            refine ⟨13904143269260631926087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 593243446155120295513045 13904143269260631926087)
            ·
              rfl

theorem cell20_822501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 7].length) (baseStart_822501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822501 prefixEnd_822501 := by exact prefixLift 822501
  have htrace : WordTrace (prefixWord ++ tailWord_822501) baseStart_822501 baseEnd_822501 := by
    simpa [prefixWord, tailWord_822501, baseEnd_822501] using wordTrace_append hprefix tailTrace_822501
  have hstable : (prefixWord ++ tailWord_822501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822501).length < 2 ^ (prefixWord ++ tailWord_822501).sum := by decide
  have hdescent : baseEnd_822501 < baseStart_822501 := by decide
  rcases family_descends (prefixWord ++ tailWord_822501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822508 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_822508 : Nat := 118140960795 + 822508 * 2 ^ 59
def prefixEnd_822508 : Nat := 4983230072969 + 3 ^ 40 * 822508 * 2
def baseEnd_822508 : Nat := 375415063260776148770987

theorem tailTrace_822508 : CollatzResearch.WordTrace tailWord_822508 prefixEnd_822508 375415063260776148770987 := by
  unfold tailWord_822508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14999665652100732013934089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19999554202800976018578785 14999665652100732013934089)
  ·
    refine ⟨11249749239075549010450567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14999665652100732013934089 11249749239075549010450567)
    ·
      refine ⟨16874623858613323515675851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11249749239075549010450567 16874623858613323515675851)
      ·
        refine ⟨25311935787919985273513777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16874623858613323515675851 25311935787919985273513777)
        ·
          refine ⟨18983951840939988955135333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25311935787919985273513777 18983951840939988955135333)
          ·
            refine ⟨3559490970176247929087875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18983951840939988955135333 3559490970176247929087875)
            ·
              refine ⟨5339236455264371893631813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559490970176247929087875 5339236455264371893631813)
              ·
                refine ⟨1001106835362069730055965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5339236455264371893631813 1001106835362069730055965)
                ·
                  refine ⟨375415063260776148770987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001106835362069730055965 375415063260776148770987)
                  ·
                    rfl

theorem cell20_822508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_822508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822508 prefixEnd_822508 := by exact prefixLift 822508
  have htrace : WordTrace (prefixWord ++ tailWord_822508) baseStart_822508 baseEnd_822508 := by
    simpa [prefixWord, tailWord_822508, baseEnd_822508] using wordTrace_append hprefix tailTrace_822508
  have hstable : (prefixWord ++ tailWord_822508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822508).length < 2 ^ (prefixWord ++ tailWord_822508).sum := by decide
  have hdescent : baseEnd_822508 < baseStart_822508 := by decide
  rcases family_descends (prefixWord ++ tailWord_822508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822511 : List Nat := [1, 1, 2, 1, 7, 1, 1, 4, 2]
def baseStart_822511 : Nat := 118140960795 + 822511 * 2 ^ 59
def prefixEnd_822511 : Nat := 4983230072969 + 3 ^ 40 * 822511 * 2
def baseEnd_822511 : Nat := 375416432542521471670975

theorem tailTrace_822511 : CollatzResearch.WordTrace tailWord_822511 prefixEnd_822511 375416432542521471670975 := by
  unfold tailWord_822511
  simp only [CollatzResearch.WordTrace]
  refine ⟨29999440723190595540227387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19999627148793730360151591 29999440723190595540227387)
  ·
    refine ⟨44999161084785893310341081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29999440723190595540227387 44999161084785893310341081)
    ·
      refine ⟨33749370813589419982755811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44999161084785893310341081 33749370813589419982755811)
      ·
        refine ⟨50624056220384129974133717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33749370813589419982755811 50624056220384129974133717)
        ·
          refine ⟨1186501317665253046268759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50624056220384129974133717 1186501317665253046268759)
          ·
            refine ⟨1779751976497879569403139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1186501317665253046268759 1779751976497879569403139)
            ·
              refine ⟨2669627964746819354104709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779751976497879569403139 2669627964746819354104709)
              ·
                refine ⟨500555243390028628894633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2669627964746819354104709 500555243390028628894633)
                ·
                  refine ⟨375416432542521471670975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500555243390028628894633 375416432542521471670975)
                  ·
                    rfl

theorem cell20_822511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 2].length) (baseStart_822511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822511 prefixEnd_822511 := by exact prefixLift 822511
  have htrace : WordTrace (prefixWord ++ tailWord_822511) baseStart_822511 baseEnd_822511 := by
    simpa [prefixWord, tailWord_822511, baseEnd_822511] using wordTrace_append hprefix tailTrace_822511
  have hstable : (prefixWord ++ tailWord_822511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822511).length < 2 ^ (prefixWord ++ tailWord_822511).sum := by decide
  have hdescent : baseEnd_822511 < baseStart_822511 := by decide
  rcases family_descends (prefixWord ++ tailWord_822511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822532 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_822532 : Nat := 118140960795 + 822532 * 2 ^ 59
def prefixEnd_822532 : Nat := 4983230072969 + 3 ^ 40 * 822532 * 2
def baseEnd_822532 : Nat := 375426017514738731970889

theorem tailTrace_822532 : CollatzResearch.WordTrace tailWord_822532 prefixEnd_822532 375426017514738731970889 := by
  unfold tailWord_822532
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000103328057258063370925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20000137770743010751161233 15000103328057258063370925)
  ·
    refine ⟨5625038748021471773764097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15000103328057258063370925 5625038748021471773764097)
    ·
      refine ⟨4218779061016103830323073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5625038748021471773764097 4218779061016103830323073)
      ·
        refine ⟨3164084295762077872742305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4218779061016103830323073 3164084295762077872742305)
        ·
          refine ⟨2373063221821558404556729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3164084295762077872742305 2373063221821558404556729)
          ·
            refine ⟨1779797416366168803417547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2373063221821558404556729 1779797416366168803417547)
            ·
              refine ⟨2669696124549253205126321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1779797416366168803417547 2669696124549253205126321)
              ·
                refine ⟨2002272093411939903844741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669696124549253205126321 2002272093411939903844741)
                ·
                  refine ⟨375426017514738731970889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002272093411939903844741 375426017514738731970889)
                  ·
                    rfl

theorem cell20_822532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_822532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822532 prefixEnd_822532 := by exact prefixLift 822532
  have htrace : WordTrace (prefixWord ++ tailWord_822532) baseStart_822532 baseEnd_822532 := by
    simpa [prefixWord, tailWord_822532, baseEnd_822532] using wordTrace_append hprefix tailTrace_822532
  have hstable : (prefixWord ++ tailWord_822532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822532).length < 2 ^ (prefixWord ++ tailWord_822532).sum := by decide
  have hdescent : baseEnd_822532 < baseStart_822532 := by decide
  rcases family_descends (prefixWord ++ tailWord_822532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822539 : List Nat := [1, 1, 1, 1, 5, 4, 3, 4]
def baseStart_822539 : Nat := 118140960795 + 822539 * 2 ^ 59
def prefixEnd_822539 : Nat := 4983230072969 + 3 ^ 40 * 822539 * 2
def baseEnd_822539 : Nat := 125143070835159272912509

theorem tailTrace_822539 : CollatzResearch.WordTrace tailWord_822539 prefixEnd_822539 125143070835159272912509 := by
  unfold tailWord_822539
  simp only [CollatzResearch.WordTrace]
  refine ⟨30000461967089156322246671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20000307978059437548164447 30000461967089156322246671)
  ·
    refine ⟨45000692950633734483370007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30000461967089156322246671 45000692950633734483370007)
    ·
      refine ⟨67501039425950601725055011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45000692950633734483370007 67501039425950601725055011)
      ·
        refine ⟨101251559138925902587582517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67501039425950601725055011 101251559138925902587582517)
        ·
          refine ⟨9492333669274303367585861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101251559138925902587582517 9492333669274303367585861)
          ·
            refine ⟨1779812562988931881422349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9492333669274303367585861 1779812562988931881422349)
            ·
              refine ⟨667429711120849455533381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1779812562988931881422349 667429711120849455533381)
              ·
                refine ⟨125143070835159272912509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 667429711120849455533381 125143070835159272912509)
                ·
                  rfl

theorem cell20_822539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_822539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822539 prefixEnd_822539 := by exact prefixLift 822539
  have htrace : WordTrace (prefixWord ++ tailWord_822539) baseStart_822539 baseEnd_822539 := by
    simpa [prefixWord, tailWord_822539, baseEnd_822539] using wordTrace_append hprefix tailTrace_822539
  have hstable : (prefixWord ++ tailWord_822539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822539).length < 2 ^ (prefixWord ++ tailWord_822539).sum := by decide
  have hdescent : baseEnd_822539 < baseStart_822539 := by decide
  rcases family_descends (prefixWord ++ tailWord_822539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822563 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 3]
def baseStart_822563 : Nat := 118140960795 + 822563 * 2 ^ 59
def prefixEnd_822563 : Nat := 4983230072969 + 3 ^ 40 * 822563 * 2
def baseEnd_822563 : Nat := 375440166759440401937429

theorem tailTrace_822563 : CollatzResearch.WordTrace tailWord_822563 prefixEnd_822563 375440166759440401937429 := by
  unfold tailWord_822563
  simp only [CollatzResearch.WordTrace]
  refine ⟨30001337319002208421120343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20000891546001472280746895 30001337319002208421120343)
  ·
    refine ⟨45002005978503312631680515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30001337319002208421120343 45002005978503312631680515)
    ·
      refine ⟨67503008967754968947520773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45002005978503312631680515 67503008967754968947520773)
      ·
        refine ⟨12656814181454056677660145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67503008967754968947520773 12656814181454056677660145)
        ·
          refine ⟨9492610636090542508245109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12656814181454056677660145 9492610636090542508245109)
          ·
            refine ⟨889932247133488360147979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9492610636090542508245109 889932247133488360147979)
            ·
              refine ⟨1334898370700232540221969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889932247133488360147979 1334898370700232540221969)
              ·
                refine ⟨1001173778025174405166477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1334898370700232540221969 1001173778025174405166477)
                ·
                  refine ⟨375440166759440401937429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001173778025174405166477 375440166759440401937429)
                  ·
                    rfl

theorem cell20_822563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_822563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822563 prefixEnd_822563 := by exact prefixLift 822563
  have htrace : WordTrace (prefixWord ++ tailWord_822563) baseStart_822563 baseEnd_822563 := by
    simpa [prefixWord, tailWord_822563, baseEnd_822563] using wordTrace_append hprefix tailTrace_822563
  have hstable : (prefixWord ++ tailWord_822563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822563).length < 2 ^ (prefixWord ++ tailWord_822563).sum := by decide
  have hdescent : baseEnd_822563 < baseStart_822563 := by decide
  rcases family_descends (prefixWord ++ tailWord_822563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822570 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_822570 : Nat := 118140960795 + 822570 * 2 ^ 59
def prefixEnd_822570 : Nat := 4983230072969 + 3 ^ 40 * 822570 * 2
def baseEnd_822570 : Nat := 375443361750179488704067

theorem tailTrace_822570 : CollatzResearch.WordTrace tailWord_822570 prefixEnd_822570 375443361750179488704067 := by
  unfold tailWord_822570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500398157494212154156291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20001061753317899077750109 7500398157494212154156291)
  ·
    refine ⟨11250597236241318231234437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7500398157494212154156291 11250597236241318231234437)
    ·
      refine ⟨2109486981795247168356457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11250597236241318231234437 2109486981795247168356457)
      ·
        refine ⟨1582115236346435376267343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2109486981795247168356457 1582115236346435376267343)
        ·
          refine ⟨2373172854519653064401015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1582115236346435376267343 2373172854519653064401015)
          ·
            refine ⟨3559759281779479596601523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373172854519653064401015 3559759281779479596601523)
            ·
              refine ⟨5339638922669219394902285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3559759281779479596601523 5339638922669219394902285)
              ·
                refine ⟨2002364596000957273088357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5339638922669219394902285 2002364596000957273088357)
                ·
                  refine ⟨375443361750179488704067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002364596000957273088357 375443361750179488704067)
                  ·
                    rfl

theorem cell20_822570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_822570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822570 prefixEnd_822570 := by exact prefixLift 822570
  have htrace : WordTrace (prefixWord ++ tailWord_822570) baseStart_822570 baseEnd_822570 := by
    simpa [prefixWord, tailWord_822570, baseEnd_822570] using wordTrace_append hprefix tailTrace_822570
  have hstable : (prefixWord ++ tailWord_822570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822570).length < 2 ^ (prefixWord ++ tailWord_822570).sum := by decide
  have hdescent : baseEnd_822570 < baseStart_822570 := by decide
  rcases family_descends (prefixWord ++ tailWord_822570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822580 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_822580 : Nat := 118140960795 + 822580 * 2 ^ 59
def prefixEnd_822580 : Nat := 4983230072969 + 3 ^ 40 * 822580 * 2
def baseEnd_822580 : Nat := 375447926022663898370693

theorem tailTrace_822580 : CollatzResearch.WordTrace tailWord_822580 prefixEnd_822580 375447926022663898370693 := by
  unfold tailWord_822580
  simp only [CollatzResearch.WordTrace]
  refine ⟨15000978679970310162244597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20001304906627080216326129 15000978679970310162244597)
  ·
    refine ⟨1406341751247216577710431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15000978679970310162244597 1406341751247216577710431)
    ·
      refine ⟨2109512626870824866565647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1406341751247216577710431 2109512626870824866565647)
      ·
        refine ⟨3164268940306237299848471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2109512626870824866565647 3164268940306237299848471)
        ·
          refine ⟨4746403410459355949772707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164268940306237299848471 4746403410459355949772707)
          ·
            refine ⟨7119605115689033924659061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4746403410459355949772707 7119605115689033924659061)
            ·
              refine ⟨667462979595846930436787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7119605115689033924659061 667462979595846930436787)
              ·
                refine ⟨1001194469393770395655181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667462979595846930436787 1001194469393770395655181)
                ·
                  refine ⟨375447926022663898370693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001194469393770395655181 375447926022663898370693)
                  ·
                    rfl

theorem cell20_822580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_822580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822580 prefixEnd_822580 := by exact prefixLift 822580
  have htrace : WordTrace (prefixWord ++ tailWord_822580) baseStart_822580 baseEnd_822580 := by
    simpa [prefixWord, tailWord_822580, baseEnd_822580] using wordTrace_append hprefix tailTrace_822580
  have hstable : (prefixWord ++ tailWord_822580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822580).length < 2 ^ (prefixWord ++ tailWord_822580).sum := by decide
  have hdescent : baseEnd_822580 < baseStart_822580 := by decide
  rcases family_descends (prefixWord ++ tailWord_822580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822591 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_822591 : Nat := 118140960795 + 822591 * 2 ^ 59
def prefixEnd_822591 : Nat := 4983230072969 + 3 ^ 40 * 822591 * 2
def baseEnd_822591 : Nat := 375452946722396749003981

theorem tailTrace_822591 : CollatzResearch.WordTrace tailWord_822591 prefixEnd_822591 375452946722396749003981 := by
  unfold tailWord_822591
  simp only [CollatzResearch.WordTrace]
  refine ⟨30002358562900769203139627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20001572375267179468759751 30002358562900769203139627)
  ·
    refine ⟨45003537844351153804709441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30002358562900769203139627 45003537844351153804709441)
    ·
      refine ⟨33752653383263365353532081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45003537844351153804709441 33752653383263365353532081)
      ·
        refine ⟨25314490037447524015149061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33752653383263365353532081 25314490037447524015149061)
        ·
          refine ⟨4746466882021410752840449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25314490037447524015149061 4746466882021410752840449)
          ·
            refine ⟨3559850161516058064630337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4746466882021410752840449 3559850161516058064630337)
            ·
              refine ⟨2669887621137043548472753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3559850161516058064630337 2669887621137043548472753)
              ·
                refine ⟨2002415715852782661354565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2669887621137043548472753 2002415715852782661354565)
                ·
                  refine ⟨375452946722396749003981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002415715852782661354565 375452946722396749003981)
                  ·
                    rfl

theorem cell20_822591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_822591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822591 prefixEnd_822591 := by exact prefixLift 822591
  have htrace : WordTrace (prefixWord ++ tailWord_822591) baseStart_822591 baseEnd_822591 := by
    simpa [prefixWord, tailWord_822591, baseEnd_822591] using wordTrace_append hprefix tailTrace_822591
  have hstable : (prefixWord ++ tailWord_822591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822591).length < 2 ^ (prefixWord ++ tailWord_822591).sum := by decide
  have hdescent : baseEnd_822591 < baseStart_822591 := by decide
  rcases family_descends (prefixWord ++ tailWord_822591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822621 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 4]
def baseStart_822621 : Nat := 118140960795 + 822621 * 2 ^ 59
def prefixEnd_822621 : Nat := 4983230072969 + 3 ^ 40 * 822621 * 2
def baseEnd_822621 : Nat := 375466639539849978003859

theorem tailTrace_822621 : CollatzResearch.WordTrace tailWord_822621 prefixEnd_822621 375466639539849978003859 := by
  unfold tailWord_822621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30003452752792084326731717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20002301835194722884487811 30003452752792084326731717)
  ·
    refine ⟨5625647391148515811262197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30003452752792084326731717 5625647391148515811262197)
    ·
      refine ⟨527404442920173357305831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5625647391148515811262197 527404442920173357305831)
      ·
        refine ⟨791106664380260035958747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527404442920173357305831 791106664380260035958747)
        ·
          refine ⟨1186659996570390053938121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791106664380260035958747 1186659996570390053938121)
          ·
            refine ⟨889994997427792540453591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186659996570390053938121 889994997427792540453591)
            ·
              refine ⟨1334992496141688810680387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889994997427792540453591 1334992496141688810680387)
              ·
                refine ⟨2002488744212533216020581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334992496141688810680387 2002488744212533216020581)
                ·
                  refine ⟨375466639539849978003859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002488744212533216020581 375466639539849978003859)
                  ·
                    rfl

theorem cell20_822621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_822621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822621 prefixEnd_822621 := by exact prefixLift 822621
  have htrace : WordTrace (prefixWord ++ tailWord_822621) baseStart_822621 baseEnd_822621 := by
    simpa [prefixWord, tailWord_822621, baseEnd_822621] using wordTrace_append hprefix tailTrace_822621
  have hstable : (prefixWord ++ tailWord_822621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822621).length < 2 ^ (prefixWord ++ tailWord_822621).sum := by decide
  have hdescent : baseEnd_822621 < baseStart_822621 := by decide
  rcases family_descends (prefixWord ++ tailWord_822621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822636 : List Nat := [2, 2, 1, 1, 5, 1, 1, 7]
def baseStart_822636 : Nat := 118140960795 + 822636 * 2 ^ 59
def prefixEnd_822636 : Nat := 4983230072969 + 3 ^ 40 * 822636 * 2
def baseEnd_822636 : Nat := 125157828649525530834599

theorem tailTrace_822636 : CollatzResearch.WordTrace tailWord_822636 prefixEnd_822636 125157828649525530834599 := by
  unfold tailWord_822636
  simp only [CollatzResearch.WordTrace]
  refine ⟨15001999923868870944263881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20002666565158494592351841 15001999923868870944263881)
  ·
    refine ⟨11251499942901653208197911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15001999923868870944263881 11251499942901653208197911)
    ·
      refine ⟨16877249914352479812296867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11251499942901653208197911 16877249914352479812296867)
      ·
        refine ⟨25315874871528719718445301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16877249914352479812296867 25315874871528719718445301)
        ·
          refine ⟨2373363269205817473604247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25315874871528719718445301 2373363269205817473604247)
          ·
            refine ⟨3560044903808726210406371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2373363269205817473604247 3560044903808726210406371)
            ·
              refine ⟨5340067355713089315609557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560044903808726210406371 5340067355713089315609557)
              ·
                refine ⟨125157828649525530834599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5340067355713089315609557 125157828649525530834599)
                ·
                  rfl

theorem cell20_822636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_822636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822636 prefixEnd_822636 := by exact prefixLift 822636
  have htrace : WordTrace (prefixWord ++ tailWord_822636) baseStart_822636 baseEnd_822636 := by
    simpa [prefixWord, tailWord_822636, baseEnd_822636] using wordTrace_append hprefix tailTrace_822636
  have hstable : (prefixWord ++ tailWord_822636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822636).length < 2 ^ (prefixWord ++ tailWord_822636).sum := by decide
  have hdescent : baseEnd_822636 < baseStart_822636 := by decide
  rcases family_descends (prefixWord ++ tailWord_822636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822705 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_822705 : Nat := 118140960795 + 822705 * 2 ^ 59
def prefixEnd_822705 : Nat := 4983230072969 + 3 ^ 40 * 822705 * 2
def baseEnd_822705 : Nat := 375504979428719019203515

theorem tailTrace_822705 : CollatzResearch.WordTrace tailWord_822705 prefixEnd_822705 375504979428719019203515 := by
  unfold tailWord_822705
  simp only [CollatzResearch.WordTrace]
  refine ⟨30006516484487766672789569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20004344322991844448526379 30006516484487766672789569)
  ·
    refine ⟨22504887363365825004592177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30006516484487766672789569 22504887363365825004592177)
    ·
      refine ⟨16878665522524368753444133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22504887363365825004592177 16878665522524368753444133)
      ·
        refine ⟨3164749785473319141270775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16878665522524368753444133 3164749785473319141270775)
        ·
          refine ⟨4747124678209978711906163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3164749785473319141270775 4747124678209978711906163)
          ·
            refine ⟨7120687017314968067859245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747124678209978711906163 7120687017314968067859245)
            ·
              refine ⟨2670257631493113025447217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7120687017314968067859245 2670257631493113025447217)
              ·
                refine ⟨2002693223619834769085413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670257631493113025447217 2002693223619834769085413)
                ·
                  refine ⟨375504979428719019203515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002693223619834769085413 375504979428719019203515)
                  ·
                    rfl

theorem cell20_822705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_822705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822705 prefixEnd_822705 := by exact prefixLift 822705
  have htrace : WordTrace (prefixWord ++ tailWord_822705) baseStart_822705 baseEnd_822705 := by
    simpa [prefixWord, tailWord_822705, baseEnd_822705] using wordTrace_append hprefix tailTrace_822705
  have hstable : (prefixWord ++ tailWord_822705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822705).length < 2 ^ (prefixWord ++ tailWord_822705).sum := by decide
  have hdescent : baseEnd_822705 < baseStart_822705 := by decide
  rcases family_descends (prefixWord ++ tailWord_822705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822753 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 3]
def baseStart_822753 : Nat := 118140960795 + 822753 * 2 ^ 59
def prefixEnd_822753 : Nat := 4983230072969 + 3 ^ 40 * 822753 * 2
def baseEnd_822753 : Nat := 375526887936644185603319

theorem tailTrace_822753 : CollatzResearch.WordTrace tailWord_822753 prefixEnd_822753 375526887936644185603319 := by
  unfold tailWord_822753
  simp only [CollatzResearch.WordTrace]
  refine ⟨30008267188313870870536913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20005511458875913913691275 30008267188313870870536913)
  ·
    refine ⟨22506200391235403152902685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30008267188313870870536913 22506200391235403152902685)
    ·
      refine ⟨8439825146713276182338507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22506200391235403152902685 8439825146713276182338507)
      ·
        refine ⟨12659737720069914273507761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8439825146713276182338507 12659737720069914273507761)
        ·
          refine ⟨9494803290052435705130821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12659737720069914273507761 9494803290052435705130821)
          ·
            refine ⟨1780275616884831694712029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9494803290052435705130821 1780275616884831694712029)
            ·
              refine ⟨667603356331811885517011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780275616884831694712029 667603356331811885517011)
              ·
                refine ⟨1001405034497717828275517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667603356331811885517011 1001405034497717828275517)
                ·
                  refine ⟨375526887936644185603319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001405034497717828275517 375526887936644185603319)
                  ·
                    rfl

theorem cell20_822753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_822753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822753 prefixEnd_822753 := by exact prefixLift 822753
  have htrace : WordTrace (prefixWord ++ tailWord_822753) baseStart_822753 baseEnd_822753 := by
    simpa [prefixWord, tailWord_822753, baseEnd_822753] using wordTrace_append hprefix tailTrace_822753
  have hstable : (prefixWord ++ tailWord_822753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822753).length < 2 ^ (prefixWord ++ tailWord_822753).sum := by decide
  have hdescent : baseEnd_822753 < baseStart_822753 := by decide
  rcases family_descends (prefixWord ++ tailWord_822753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822764 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_822764 : Nat := 118140960795 + 822764 * 2 ^ 59
def prefixEnd_822764 : Nat := 4983230072969 + 3 ^ 40 * 822764 * 2
def baseEnd_822764 : Nat := 375531908636377036236607

theorem tailTrace_822764 : CollatzResearch.WordTrace tailWord_822764 prefixEnd_822764 375531908636377036236607 := by
  unfold tailWord_822764
  simp only [CollatzResearch.WordTrace]
  refine ⟨15004334195637009874593673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20005778927516013166124897 15004334195637009874593673)
  ·
    refine ⟨11253250646727757405945255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15004334195637009874593673 11253250646727757405945255)
    ·
      refine ⟨16879875970091636108917883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11253250646727757405945255 16879875970091636108917883)
      ·
        refine ⟨25319813955137454163376825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16879875970091636108917883 25319813955137454163376825)
        ·
          refine ⟨18989860466353090622532619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25319813955137454163376825 18989860466353090622532619)
          ·
            refine ⟨28484790699529635933798929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18989860466353090622532619 28484790699529635933798929)
            ·
              refine ⟨21363593024647226950349197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28484790699529635933798929 21363593024647226950349197)
              ·
                refine ⟨8011347384242710106380949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21363593024647226950349197 8011347384242710106380949)
                ·
                  refine ⟨375531908636377036236607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8011347384242710106380949 375531908636377036236607)
                  ·
                    rfl

theorem cell20_822764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_822764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822764 prefixEnd_822764 := by exact prefixLift 822764
  have htrace : WordTrace (prefixWord ++ tailWord_822764) baseStart_822764 baseEnd_822764 := by
    simpa [prefixWord, tailWord_822764, baseEnd_822764] using wordTrace_append hprefix tailTrace_822764
  have hstable : (prefixWord ++ tailWord_822764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822764).length < 2 ^ (prefixWord ++ tailWord_822764).sum := by decide
  have hdescent : baseEnd_822764 < baseStart_822764 := by decide
  rcases family_descends (prefixWord ++ tailWord_822764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822774 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_822774 : Nat := 118140960795 + 822774 * 2 ^ 59
def prefixEnd_822774 : Nat := 4983230072969 + 3 ^ 40 * 822774 * 2
def baseEnd_822774 : Nat := 375536472908861445903233

theorem tailTrace_822774 : CollatzResearch.WordTrace tailWord_822774 prefixEnd_822774 375536472908861445903233 := by
  unfold tailWord_822774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875564570077361966065711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20006022080825194304700917 1875564570077361966065711)
  ·
    refine ⟨2813346855116042949098567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1875564570077361966065711 2813346855116042949098567)
    ·
      refine ⟨4220020282674064423647851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813346855116042949098567 4220020282674064423647851)
      ·
        refine ⟨6330030424011096635471777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4220020282674064423647851 6330030424011096635471777)
        ·
          refine ⟨4747522818008322476603833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6330030424011096635471777 4747522818008322476603833)
          ·
            refine ⟨3560642113506241857452875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4747522818008322476603833 3560642113506241857452875)
            ·
              refine ⟨5340963170259362786179313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3560642113506241857452875 5340963170259362786179313)
              ·
                refine ⟨4005722377694522089634485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5340963170259362786179313 4005722377694522089634485)
                ·
                  refine ⟨375536472908861445903233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4005722377694522089634485 375536472908861445903233)
                  ·
                    rfl

theorem cell20_822774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_822774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822774 prefixEnd_822774 := by exact prefixLift 822774
  have htrace : WordTrace (prefixWord ++ tailWord_822774) baseStart_822774 baseEnd_822774 := by
    simpa [prefixWord, tailWord_822774, baseEnd_822774] using wordTrace_append hprefix tailTrace_822774
  have hstable : (prefixWord ++ tailWord_822774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822774).length < 2 ^ (prefixWord ++ tailWord_822774).sum := by decide
  have hdescent : baseEnd_822774 < baseStart_822774 := by decide
  rcases family_descends (prefixWord ++ tailWord_822774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822790 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_822790 : Nat := 118140960795 + 822790 * 2 ^ 59
def prefixEnd_822790 : Nat := 4983230072969 + 3 ^ 40 * 822790 * 2
def baseEnd_822790 : Nat := 375543775744836501369835

theorem tailTrace_822790 : CollatzResearch.WordTrace tailWord_822790 prefixEnd_822790 375543775744836501369835 := by
  unfold tailWord_822790
  simp only [CollatzResearch.WordTrace]
  refine ⟨937800521536869568426057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20006411126119884126422549 937800521536869568426057)
  ·
    refine ⟨703350391152652176319543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 937800521536869568426057 703350391152652176319543)
    ·
      refine ⟨1055025586728978264479315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703350391152652176319543 1055025586728978264479315)
      ·
        refine ⟨1582538380093467396718973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055025586728978264479315 1582538380093467396718973)
        ·
          refine ⟨593451892535050273769615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1582538380093467396718973 593451892535050273769615)
          ·
            refine ⟨890177838802575410654423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593451892535050273769615 890177838802575410654423)
            ·
              refine ⟨1335266758203863115981635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890177838802575410654423 1335266758203863115981635)
              ·
                refine ⟨2002900137305794673972453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335266758203863115981635 2002900137305794673972453)
                ·
                  refine ⟨375543775744836501369835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2002900137305794673972453 375543775744836501369835)
                  ·
                    rfl

theorem cell20_822790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_822790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822790 prefixEnd_822790 := by exact prefixLift 822790
  have htrace : WordTrace (prefixWord ++ tailWord_822790) baseStart_822790 baseEnd_822790 := by
    simpa [prefixWord, tailWord_822790, baseEnd_822790] using wordTrace_append hprefix tailTrace_822790
  have hstable : (prefixWord ++ tailWord_822790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822790).length < 2 ^ (prefixWord ++ tailWord_822790).sum := by decide
  have hdescent : baseEnd_822790 < baseStart_822790 := by decide
  rcases family_descends (prefixWord ++ tailWord_822790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822804 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 3]
def baseStart_822804 : Nat := 118140960795 + 822804 * 2 ^ 59
def prefixEnd_822804 : Nat := 4983230072969 + 3 ^ 40 * 822804 * 2
def baseEnd_822804 : Nat := 375550165726314674903111

theorem tailTrace_822804 : CollatzResearch.WordTrace tailWord_822804 prefixEnd_822804 375550165726314674903111 := by
  unfold tailWord_822804
  simp only [CollatzResearch.WordTrace]
  refine ⟨15005063655564553290321733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20006751540752737720428977 15005063655564553290321733)
  ·
    refine ⟨2813449435418353741935325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15005063655564553290321733 2813449435418353741935325)
    ·
      refine ⟨1055043538281882653225747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2813449435418353741935325 1055043538281882653225747)
      ·
        refine ⟨1582565307422823979838621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055043538281882653225747 1582565307422823979838621)
        ·
          refine ⟨593461990283558992439483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1582565307422823979838621 593461990283558992439483)
          ·
            refine ⟨890192985425338488659225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593461990283558992439483 890192985425338488659225)
            ·
              refine ⟨667644739069003866494419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890192985425338488659225 667644739069003866494419)
              ·
                refine ⟨1001467108603505799741629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667644739069003866494419 1001467108603505799741629)
                ·
                  refine ⟨375550165726314674903111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001467108603505799741629 375550165726314674903111)
                  ·
                    rfl

theorem cell20_822804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_822804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822804 prefixEnd_822804 := by exact prefixLift 822804
  have htrace : WordTrace (prefixWord ++ tailWord_822804) baseStart_822804 baseEnd_822804 := by
    simpa [prefixWord, tailWord_822804, baseEnd_822804] using wordTrace_append hprefix tailTrace_822804
  have hstable : (prefixWord ++ tailWord_822804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822804).length < 2 ^ (prefixWord ++ tailWord_822804).sum := by decide
  have hdescent : baseEnd_822804 < baseStart_822804 := by decide
  rcases family_descends (prefixWord ++ tailWord_822804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822808 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_822808 : Nat := 118140960795 + 822808 * 2 ^ 59
def prefixEnd_822808 : Nat := 4983230072969 + 3 ^ 40 * 822808 * 2
def baseEnd_822808 : Nat := 375551991435308438769761

theorem tailTrace_822808 : CollatzResearch.WordTrace tailWord_822808 prefixEnd_822808 375551991435308438769761 := by
  unfold tailWord_822808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15005136601557307631894539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20006848802076410175859385 15005136601557307631894539)
  ·
    refine ⟨22507704902335961447841809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15005136601557307631894539 22507704902335961447841809)
    ·
      refine ⟨16880778676751971085881357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22507704902335961447841809 16880778676751971085881357)
      ·
        refine ⟨6330292003781989157205509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16880778676751971085881357 6330292003781989157205509)
        ·
          refine ⟨1186929750709122966976033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6330292003781989157205509 1186929750709122966976033)
          ·
            refine ⟨890197313031842225232025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186929750709122966976033 890197313031842225232025)
            ·
              refine ⟨667647984773881668924019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890197313031842225232025 667647984773881668924019)
              ·
                refine ⟨1001471977160822503386029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667647984773881668924019 1001471977160822503386029)
                ·
                  refine ⟨375551991435308438769761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001471977160822503386029 375551991435308438769761)
                  ·
                    rfl

theorem cell20_822808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_822808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822808 prefixEnd_822808 := by exact prefixLift 822808
  have htrace : WordTrace (prefixWord ++ tailWord_822808) baseStart_822808 baseEnd_822808 := by
    simpa [prefixWord, tailWord_822808, baseEnd_822808] using wordTrace_append hprefix tailTrace_822808
  have hstable : (prefixWord ++ tailWord_822808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822808).length < 2 ^ (prefixWord ++ tailWord_822808).sum := by decide
  have hdescent : baseEnd_822808 < baseStart_822808 := by decide
  rcases family_descends (prefixWord ++ tailWord_822808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822812 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 3]
def baseStart_822812 : Nat := 118140960795 + 822812 * 2 ^ 59
def prefixEnd_822812 : Nat := 4983230072969 + 3 ^ 40 * 822812 * 2
def baseEnd_822812 : Nat := 375553817144302202636411

theorem tailTrace_822812 : CollatzResearch.WordTrace tailWord_822812 prefixEnd_822812 375553817144302202636411 := by
  unfold tailWord_822812
  simp only [CollatzResearch.WordTrace]
  refine ⟨15005209547550061973467345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20006946063400082631289793 15005209547550061973467345)
  ·
    refine ⟨11253907160662546480100509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15005209547550061973467345 11253907160662546480100509)
    ·
      refine ⟨4220215185248454930037691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11253907160662546480100509 4220215185248454930037691)
      ·
        refine ⟨6330322777872682395056537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4220215185248454930037691 6330322777872682395056537)
        ·
          refine ⟨4747742083404511796292403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6330322777872682395056537 4747742083404511796292403)
          ·
            refine ⟨7121613125106767694438605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747742083404511796292403 7121613125106767694438605)
            ·
              refine ⟨2670604921915037885414477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7121613125106767694438605 2670604921915037885414477)
              ·
                refine ⟨1001476845718139207030429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2670604921915037885414477 1001476845718139207030429)
                ·
                  refine ⟨375553817144302202636411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001476845718139207030429 375553817144302202636411)
                  ·
                    rfl

theorem cell20_822812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_822812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822812 prefixEnd_822812 := by exact prefixLift 822812
  have htrace : WordTrace (prefixWord ++ tailWord_822812) baseStart_822812 baseEnd_822812 := by
    simpa [prefixWord, tailWord_822812, baseEnd_822812] using wordTrace_append hprefix tailTrace_822812
  have hstable : (prefixWord ++ tailWord_822812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822812).length < 2 ^ (prefixWord ++ tailWord_822812).sum := by decide
  have hdescent : baseEnd_822812 < baseStart_822812 := by decide
  rcases family_descends (prefixWord ++ tailWord_822812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822826 : List Nat := [3, 1, 4, 1, 1, 1, 1, 8]
def baseStart_822826 : Nat := 118140960795 + 822826 * 2 ^ 59
def prefixEnd_822826 : Nat := 4983230072969 + 3 ^ 40 * 822826 * 2
def baseEnd_822826 : Nat := 125186735708593458723229

theorem tailTrace_822826 : CollatzResearch.WordTrace tailWord_822826 prefixEnd_822826 125186735708593458723229 := by
  unfold tailWord_822826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7502732429262351084486083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20007286478032936225296221 7502732429262351084486083)
  ·
    refine ⟨11254098643893526626729125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7502732429262351084486083 11254098643893526626729125)
    ·
      refine ⟨2110143495730036242511711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11254098643893526626729125 2110143495730036242511711)
      ·
        refine ⟨3165215243595054363767567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2110143495730036242511711 3165215243595054363767567)
        ·
          refine ⟨4747822865392581545651351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165215243595054363767567 4747822865392581545651351)
          ·
            refine ⟨7121734298088872318477027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747822865392581545651351 7121734298088872318477027)
            ·
              refine ⟨10682601447133308477715541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7121734298088872318477027 10682601447133308477715541)
              ·
                refine ⟨125186735708593458723229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10682601447133308477715541 125186735708593458723229)
                ·
                  rfl

theorem cell20_822826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_822826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822826 prefixEnd_822826 := by exact prefixLift 822826
  have htrace : WordTrace (prefixWord ++ tailWord_822826) baseStart_822826 baseEnd_822826 := by
    simpa [prefixWord, tailWord_822826, baseEnd_822826] using wordTrace_append hprefix tailTrace_822826
  have hstable : (prefixWord ++ tailWord_822826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822826).length < 2 ^ (prefixWord ++ tailWord_822826).sum := by decide
  have hdescent : baseEnd_822826 < baseStart_822826 := by decide
  rcases family_descends (prefixWord ++ tailWord_822826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822847 : List Nat := [1, 1, 2, 2, 3, 11]
def baseStart_822847 : Nat := 118140960795 + 822847 * 2 ^ 59
def prefixEnd_822847 : Nat := 4983230072969 + 3 ^ 40 * 822847 * 2
def baseEnd_822847 : Nat := 13909992299925838387763

theorem tailTrace_822847 : CollatzResearch.WordTrace tailWord_822847 prefixEnd_822847 13909992299925838387763 := by
  unfold tailWord_822847
  simp only [CollatzResearch.WordTrace]
  refine ⟨30011695649973324924458795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20007797099982216616305863 30011695649973324924458795)
  ·
    refine ⟨45017543474959987386688193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30011695649973324924458795 45017543474959987386688193)
    ·
      refine ⟨33763157606219990540016145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45017543474959987386688193 33763157606219990540016145)
      ·
        refine ⟨25322368204664992905012109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33763157606219990540016145 25322368204664992905012109)
        ·
          refine ⟨9495888076749372339379541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25322368204664992905012109 9495888076749372339379541)
          ·
            refine ⟨13909992299925838387763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9495888076749372339379541 13909992299925838387763)
            ·
              rfl

theorem cell20_822847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 11].length) (baseStart_822847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822847 prefixEnd_822847 := by exact prefixLift 822847
  have htrace : WordTrace (prefixWord ++ tailWord_822847) baseStart_822847 baseEnd_822847 := by
    simpa [prefixWord, tailWord_822847, baseEnd_822847] using wordTrace_append hprefix tailTrace_822847
  have hstable : (prefixWord ++ tailWord_822847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822847).length < 2 ^ (prefixWord ++ tailWord_822847).sum := by decide
  have hdescent : baseEnd_822847 < baseStart_822847 := by decide
  rcases family_descends (prefixWord ++ tailWord_822847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822870 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_822870 : Nat := 118140960795 + 822870 * 2 ^ 59
def prefixEnd_822870 : Nat := 4983230072969 + 3 ^ 40 * 822870 * 2
def baseEnd_822870 : Nat := 375580289924711778702841

theorem tailTrace_822870 : CollatzResearch.WordTrace tailWord_822870 prefixEnd_822870 375580289924711778702841 := by
  unfold tailWord_822870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1875783408055624990784129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20008356352593333235030709 1875783408055624990784129)
  ·
    refine ⟨1406837556041718743088097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1875783408055624990784129 1406837556041718743088097)
    ·
      refine ⟨1055128167031289057316073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1406837556041718743088097 1055128167031289057316073)
      ·
        refine ⟨791346125273466792987055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055128167031289057316073 791346125273466792987055)
        ·
          refine ⟨1187019187910200189480583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791346125273466792987055 1187019187910200189480583)
          ·
            refine ⟨1780528781865300284220875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187019187910200189480583 1780528781865300284220875)
            ·
              refine ⟨2670793172797950426331313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1780528781865300284220875 2670793172797950426331313)
              ·
                refine ⟨2003094879598462819748485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2670793172797950426331313 2003094879598462819748485)
                ·
                  refine ⟨375580289924711778702841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2003094879598462819748485 375580289924711778702841)
                  ·
                    rfl

theorem cell20_822870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_822870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822870 prefixEnd_822870 := by exact prefixLift 822870
  have htrace : WordTrace (prefixWord ++ tailWord_822870) baseStart_822870 baseEnd_822870 := by
    simpa [prefixWord, tailWord_822870, baseEnd_822870] using wordTrace_append hprefix tailTrace_822870
  have hstable : (prefixWord ++ tailWord_822870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822870).length < 2 ^ (prefixWord ++ tailWord_822870).sum := by decide
  have hdescent : baseEnd_822870 < baseStart_822870 := by decide
  rcases family_descends (prefixWord ++ tailWord_822870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822877 : List Nat := [1, 4, 4, 2, 1, 1, 3, 4]
def baseStart_822877 : Nat := 118140960795 + 822877 * 2 ^ 59
def prefixEnd_822877 : Nat := 4983230072969 + 3 ^ 40 * 822877 * 2
def baseEnd_822877 : Nat := 125194494971816955156493

theorem tailTrace_822877 : CollatzResearch.WordTrace tailWord_822877 prefixEnd_822877 125194494971816955156493 := by
  unfold tailWord_822877
  simp only [CollatzResearch.WordTrace]
  refine ⟨30012789839864640048050885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20008526559909760032033923 30012789839864640048050885)
  ·
    refine ⟨5627398094974620009009541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30012789839864640048050885 5627398094974620009009541)
    ·
      refine ⟨1055137142807741251689289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5627398094974620009009541 1055137142807741251689289)
      ·
        refine ⟨791352857105805938766967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055137142807741251689289 791352857105805938766967)
        ·
          refine ⟨1187029285658708908150451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791352857105805938766967 1187029285658708908150451)
          ·
            refine ⟨1780543928488063362225677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187029285658708908150451 1780543928488063362225677)
            ·
              refine ⟨667703973183023760834629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780543928488063362225677 667703973183023760834629)
              ·
                refine ⟨125194494971816955156493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 667703973183023760834629 125194494971816955156493)
                ·
                  rfl

theorem cell20_822877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_822877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822877 prefixEnd_822877 := by exact prefixLift 822877
  have htrace : WordTrace (prefixWord ++ tailWord_822877) baseStart_822877 baseEnd_822877 := by
    simpa [prefixWord, tailWord_822877, baseEnd_822877] using wordTrace_append hprefix tailTrace_822877
  have hstable : (prefixWord ++ tailWord_822877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822877).length < 2 ^ (prefixWord ++ tailWord_822877).sum := by decide
  have hdescent : baseEnd_822877 < baseStart_822877 := by decide
  rcases family_descends (prefixWord ++ tailWord_822877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822923 : List Nat := [1, 1, 1, 1, 4, 1, 4, 7]
def baseStart_822923 : Nat := 118140960795 + 822923 * 2 ^ 59
def prefixEnd_822923 : Nat := 4983230072969 + 3 ^ 40 * 822923 * 2
def baseEnd_822923 : Nat := 125201493522959716645319

theorem tailTrace_822923 : CollatzResearch.WordTrace tailWord_822923 prefixEnd_822923 125201493522959716645319 := by
  unfold tailWord_822923
  simp only [CollatzResearch.WordTrace]
  refine ⟨30014467597697989904225423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20009645065131993269483615 30014467597697989904225423)
  ·
    refine ⟨45021701396546984856338135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30014467597697989904225423 45021701396546984856338135)
    ·
      refine ⟨67532552094820477284507203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45021701396546984856338135 67532552094820477284507203)
      ·
        refine ⟨101298828142230715926760805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67532552094820477284507203 101298828142230715926760805)
        ·
          refine ⟨18993530276668259236267651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101298828142230715926760805 18993530276668259236267651)
          ·
            refine ⟨28490295415002388854401477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18993530276668259236267651 28490295415002388854401477)
            ·
              refine ⟨5341930390312947910200277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28490295415002388854401477 5341930390312947910200277)
              ·
                refine ⟨125201493522959716645319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5341930390312947910200277 125201493522959716645319)
                ·
                  rfl

theorem cell20_822923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_822923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822923 prefixEnd_822923 := by exact prefixLift 822923
  have htrace : WordTrace (prefixWord ++ tailWord_822923) baseStart_822923 baseEnd_822923 := by
    simpa [prefixWord, tailWord_822923, baseEnd_822923] using wordTrace_append hprefix tailTrace_822923
  have hstable : (prefixWord ++ tailWord_822923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822923).length < 2 ^ (prefixWord ++ tailWord_822923).sum := by decide
  have hdescent : baseEnd_822923 < baseStart_822923 := by decide
  rcases family_descends (prefixWord ++ tailWord_822923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822967 : List Nat := [1, 1, 3, 1, 5, 2, 3, 2, 2]
def baseStart_822967 : Nat := 118140960795 + 822967 * 2 ^ 59
def prefixEnd_822967 : Nat := 4983230072969 + 3 ^ 40 * 822967 * 2
def baseEnd_822967 : Nat := 375624563367810552469111

theorem tailTrace_822967 : CollatzResearch.WordTrace tailWord_822967 prefixEnd_822967 375624563367810552469111 := by
  unfold tailWord_822967
  simp only [CollatzResearch.WordTrace]
  refine ⟨30016072409538585418827155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20010714939692390279218103 30016072409538585418827155)
  ·
    refine ⟨45024108614307878128240733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30016072409538585418827155 45024108614307878128240733)
    ·
      refine ⟨16884040730365454298090275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45024108614307878128240733 16884040730365454298090275)
      ·
        refine ⟨25326061095548181447135413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16884040730365454298090275 25326061095548181447135413)
        ·
          refine ⟨2374318227707642010668945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25326061095548181447135413 2374318227707642010668945)
          ·
            refine ⟨1780738670780731508001709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2374318227707642010668945 1780738670780731508001709)
            ·
              refine ⟨667777001542774315500641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780738670780731508001709 667777001542774315500641)
              ·
                refine ⟨500832751157080736625481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667777001542774315500641 500832751157080736625481)
                ·
                  refine ⟨375624563367810552469111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500832751157080736625481 375624563367810552469111)
                  ·
                    rfl

theorem cell20_822967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 2].length) (baseStart_822967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822967 prefixEnd_822967 := by exact prefixLift 822967
  have htrace : WordTrace (prefixWord ++ tailWord_822967) baseStart_822967 baseEnd_822967 := by
    simpa [prefixWord, tailWord_822967, baseEnd_822967] using wordTrace_append hprefix tailTrace_822967
  have hstable : (prefixWord ++ tailWord_822967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822967).length < 2 ^ (prefixWord ++ tailWord_822967).sum := by decide
  have hdescent : baseEnd_822967 < baseStart_822967 := by decide
  rcases family_descends (prefixWord ++ tailWord_822967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822971 : List Nat := [1, 1, 1, 1, 1, 2, 3, 8, 2]
def baseStart_822971 : Nat := 118140960795 + 822971 * 2 ^ 59
def prefixEnd_822971 : Nat := 4983230072969 + 3 ^ 40 * 822971 * 2
def baseEnd_822971 : Nat := 375626389076804316335761

theorem tailTrace_822971 : CollatzResearch.WordTrace tailWord_822971 prefixEnd_822971 375626389076804316335761 := by
  unfold tailWord_822971
  simp only [CollatzResearch.WordTrace]
  refine ⟨30016218301524094101972767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20010812201016062734648511 30016218301524094101972767)
  ·
    refine ⟨45024327452286141152959151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30016218301524094101972767 45024327452286141152959151)
    ·
      refine ⟨67536491178429211729438727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45024327452286141152959151 67536491178429211729438727)
      ·
        refine ⟨101304736767643817594158091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67536491178429211729438727 101304736767643817594158091)
        ·
          refine ⟨151957105151465726391237137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101304736767643817594158091 151957105151465726391237137)
          ·
            refine ⟨113967828863599294793427853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151957105151465726391237137 113967828863599294793427853)
            ·
              refine ⟨42737935823849735547535445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113967828863599294793427853 42737935823849735547535445)
              ·
                refine ⟨500835185435739088447681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 42737935823849735547535445 500835185435739088447681)
                ·
                  refine ⟨375626389076804316335761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500835185435739088447681 375626389076804316335761)
                  ·
                    rfl

theorem cell20_822971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 2].length) (baseStart_822971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822971 prefixEnd_822971 := by exact prefixLift 822971
  have htrace : WordTrace (prefixWord ++ tailWord_822971) baseStart_822971 baseEnd_822971 := by
    simpa [prefixWord, tailWord_822971, baseEnd_822971] using wordTrace_append hprefix tailTrace_822971
  have hstable : (prefixWord ++ tailWord_822971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822971).length < 2 ^ (prefixWord ++ tailWord_822971).sum := by decide
  have hdescent : baseEnd_822971 < baseStart_822971 := by decide
  rcases family_descends (prefixWord ++ tailWord_822971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822999 : List Nat := [1, 1, 3, 2, 1, 3, 1, 8]
def baseStart_822999 : Nat := 118140960795 + 822999 * 2 ^ 59
def prefixEnd_822999 : Nat := 4983230072969 + 3 ^ 40 * 822999 * 2
def baseEnd_822999 : Nat := 125213056346586887800771

theorem tailTrace_822999 : CollatzResearch.WordTrace tailWord_822999 prefixEnd_822999 125213056346586887800771 := by
  unfold tailWord_822999
  simp only [CollatzResearch.WordTrace]
  refine ⟨30017239545422654883992051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20011493030281769922661367 30017239545422654883992051)
  ·
    refine ⟨45025859318133982325988077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30017239545422654883992051 45025859318133982325988077)
    ·
      refine ⟨16884697244300243372245529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45025859318133982325988077 16884697244300243372245529)
      ·
        refine ⟨12663522933225182529184147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16884697244300243372245529 12663522933225182529184147)
        ·
          refine ⟨18995284399837773793776221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12663522933225182529184147 18995284399837773793776221)
          ·
            refine ⟨7123231649939165172666083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18995284399837773793776221 7123231649939165172666083)
            ·
              refine ⟨10684847474908747758999125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123231649939165172666083 10684847474908747758999125)
              ·
                refine ⟨125213056346586887800771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10684847474908747758999125 125213056346586887800771)
                ·
                  rfl

theorem cell20_822999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_822999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_822999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_822999 prefixEnd_822999 := by exact prefixLift 822999
  have htrace : WordTrace (prefixWord ++ tailWord_822999) baseStart_822999 baseEnd_822999 := by
    simpa [prefixWord, tailWord_822999, baseEnd_822999] using wordTrace_append hprefix tailTrace_822999
  have hstable : (prefixWord ++ tailWord_822999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822999).length < 2 ^ (prefixWord ++ tailWord_822999).sum := by decide
  have hdescent : baseEnd_822999 < baseStart_822999 := by decide
  rcases family_descends (prefixWord ++ tailWord_822999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823026 : List Nat := [3, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_823026 : Nat := 118140960795 + 823026 * 2 ^ 59
def prefixEnd_823026 : Nat := 4983230072969 + 3 ^ 40 * 823026 * 2
def baseEnd_823026 : Nat := 375651492575468569502203

theorem tailTrace_823026 : CollatzResearch.WordTrace tailWord_823026 prefixEnd_823026 375651492575468569502203 := by
  unfold tailWord_823026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7504556079081209623806233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20012149544216558996816621 7504556079081209623806233)
  ·
    refine ⟨5628417059310907217854675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7504556079081209623806233 5628417059310907217854675)
    ·
      refine ⟨8442625588966360826782013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628417059310907217854675 8442625588966360826782013)
      ·
        refine ⟨3165984595862385310043255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8442625588966360826782013 3165984595862385310043255)
        ·
          refine ⟨4748976893793577965064883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165984595862385310043255 4748976893793577965064883)
          ·
            refine ⟨7123465340690366947597325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4748976893793577965064883 7123465340690366947597325)
            ·
              refine ⟨2671299502758887605348997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7123465340690366947597325 2671299502758887605348997)
              ·
                refine ⟨500868656767291426002937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2671299502758887605348997 500868656767291426002937)
                ·
                  refine ⟨375651492575468569502203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500868656767291426002937 375651492575468569502203)
                  ·
                    rfl

theorem cell20_823026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_823026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823026 prefixEnd_823026 := by exact prefixLift 823026
  have htrace : WordTrace (prefixWord ++ tailWord_823026) baseStart_823026 baseEnd_823026 := by
    simpa [prefixWord, tailWord_823026, baseEnd_823026] using wordTrace_append hprefix tailTrace_823026
  have hstable : (prefixWord ++ tailWord_823026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823026).length < 2 ^ (prefixWord ++ tailWord_823026).sum := by decide
  have hdescent : baseEnd_823026 < baseStart_823026 := by decide
  rcases family_descends (prefixWord ++ tailWord_823026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823037 : List Nat := [1, 4, 1, 1, 1, 1, 2, 9]
def baseStart_823037 : Nat := 118140960795 + 823037 * 2 ^ 59
def prefixEnd_823037 : Nat := 4983230072969 + 3 ^ 40 * 823037 * 2
def baseEnd_823037 : Nat := 125218837758400473378497

theorem tailTrace_823037 : CollatzResearch.WordTrace tailWord_823037 prefixEnd_823037 125218837758400473378497 := by
  unfold tailWord_823037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30018625519284987373875365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20012417012856658249250243 30018625519284987373875365)
  ·
    refine ⟨5628492284865935132601631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30018625519284987373875365 5628492284865935132601631)
    ·
      refine ⟨8442738427298902698902447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5628492284865935132601631 8442738427298902698902447)
      ·
        refine ⟨12664107640948354048353671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8442738427298902698902447 12664107640948354048353671)
        ·
          refine ⟨18996161461422531072530507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12664107640948354048353671 18996161461422531072530507)
          ·
            refine ⟨28494242192133796608795761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18996161461422531072530507 28494242192133796608795761)
            ·
              refine ⟨21370681644100347456596821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28494242192133796608795761 21370681644100347456596821)
              ·
                refine ⟨125218837758400473378497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21370681644100347456596821 125218837758400473378497)
                ·
                  rfl

theorem cell20_823037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_823037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823037 prefixEnd_823037 := by exact prefixLift 823037
  have htrace : WordTrace (prefixWord ++ tailWord_823037) baseStart_823037 baseEnd_823037 := by
    simpa [prefixWord, tailWord_823037, baseEnd_823037] using wordTrace_append hprefix tailTrace_823037
  have hstable : (prefixWord ++ tailWord_823037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823037).length < 2 ^ (prefixWord ++ tailWord_823037).sum := by decide
  have hdescent : baseEnd_823037 < baseStart_823037 := by decide
  rcases family_descends (prefixWord ++ tailWord_823037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823068 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_823068 : Nat := 118140960795 + 823068 * 2 ^ 59
def prefixEnd_823068 : Nat := 4983230072969 + 3 ^ 40 * 823068 * 2
def baseEnd_823068 : Nat := 375670662519903090102031

theorem tailTrace_823068 : CollatzResearch.WordTrace tailWord_823068 prefixEnd_823068 375670662519903090102031 := by
  unfold tailWord_823068
  simp only [CollatzResearch.WordTrace]
  refine ⟨15009878091086339834126929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20013170788115119778835905 15009878091086339834126929)
  ·
    refine ⟨11257408568314754875595197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15009878091086339834126929 11257408568314754875595197)
    ·
      refine ⟨4221528213118033078348199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11257408568314754875595197 4221528213118033078348199)
      ·
        refine ⟨6332292319677049617522299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4221528213118033078348199 6332292319677049617522299)
        ·
          refine ⟨9498438479515574426283449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6332292319677049617522299 9498438479515574426283449)
          ·
            refine ⟨7123828859636680819712587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9498438479515574426283449 7123828859636680819712587)
            ·
              refine ⟨10685743289455021229568881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7123828859636680819712587 10685743289455021229568881)
              ·
                refine ⟨8014307467091265922176661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10685743289455021229568881 8014307467091265922176661)
                ·
                  refine ⟨375670662519903090102031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8014307467091265922176661 375670662519903090102031)
                  ·
                    rfl

theorem cell20_823068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_823068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823068 prefixEnd_823068 := by exact prefixLift 823068
  have htrace : WordTrace (prefixWord ++ tailWord_823068) baseStart_823068 baseEnd_823068 := by
    simpa [prefixWord, tailWord_823068, baseEnd_823068] using wordTrace_append hprefix tailTrace_823068
  have hstable : (prefixWord ++ tailWord_823068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823068).length < 2 ^ (prefixWord ++ tailWord_823068).sum := by decide
  have hdescent : baseEnd_823068 < baseStart_823068 := by decide
  rcases family_descends (prefixWord ++ tailWord_823068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823070 : List Nat := [4, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_823070 : Nat := 118140960795 + 823070 * 2 ^ 59
def prefixEnd_823070 : Nat := 4983230072969 + 3 ^ 40 * 823070 * 2
def baseEnd_823070 : Nat := 375671575374399972035357

theorem tailTrace_823070 : CollatzResearch.WordTrace tailWord_823070 prefixEnd_823070 375671575374399972035357 := by
  unfold tailWord_823070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752478641020679251228333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20013219418776956006551109 3752478641020679251228333)
  ·
    refine ⟨1407179490382754719210625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3752478641020679251228333 1407179490382754719210625)
    ·
      refine ⟨1055384617787066039407969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1407179490382754719210625 1055384617787066039407969)
      ·
        refine ⟨791538463340299529555977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055384617787066039407969 791538463340299529555977)
        ·
          refine ⟨593653847505224647166983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791538463340299529555977 593653847505224647166983)
          ·
            refine ⟨890480771257836970750475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593653847505224647166983 890480771257836970750475)
            ·
              refine ⟨1335721156886755456125713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890480771257836970750475 1335721156886755456125713)
              ·
                refine ⟨1001790867665066592094285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1335721156886755456125713 1001790867665066592094285)
                ·
                  refine ⟨375671575374399972035357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001790867665066592094285 375671575374399972035357)
                  ·
                    rfl

theorem cell20_823070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_823070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823070 prefixEnd_823070 := by exact prefixLift 823070
  have htrace : WordTrace (prefixWord ++ tailWord_823070) baseStart_823070 baseEnd_823070 := by
    simpa [prefixWord, tailWord_823070, baseEnd_823070] using wordTrace_append hprefix tailTrace_823070
  have hstable : (prefixWord ++ tailWord_823070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823070).length < 2 ^ (prefixWord ++ tailWord_823070).sum := by decide
  have hdescent : baseEnd_823070 < baseStart_823070 := by decide
  rcases family_descends (prefixWord ++ tailWord_823070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823113 : List Nat := [1, 2, 1, 1, 2, 4, 3, 6]
def baseStart_823113 : Nat := 118140960795 + 823113 * 2 ^ 59
def prefixEnd_823113 : Nat := 4983230072969 + 3 ^ 40 * 823113 * 2
def baseEnd_823113 : Nat := 125230400582027644533949

theorem tailTrace_823113 : CollatzResearch.WordTrace tailWord_823113 prefixEnd_823113 125230400582027644533949 := by
  unfold tailWord_823113
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021397467009652353641993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20014264978006434902427995 30021397467009652353641993)
  ·
    refine ⟨22516048100257239265231495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30021397467009652353641993 22516048100257239265231495)
    ·
      refine ⟨33774072150385858897847243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22516048100257239265231495 33774072150385858897847243)
      ·
        refine ⟨50661108225578788346770865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33774072150385858897847243 50661108225578788346770865)
        ·
          refine ⟨37995831169184091260078149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50661108225578788346770865 37995831169184091260078149)
          ·
            refine ⟨7124218344222017111264653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37995831169184091260078149 7124218344222017111264653)
            ·
              refine ⟨2671581879083256416724245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7124218344222017111264653 2671581879083256416724245)
              ·
                refine ⟨125230400582027644533949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2671581879083256416724245 125230400582027644533949)
                ·
                  rfl

theorem cell20_823113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_823113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823113 prefixEnd_823113 := by exact prefixLift 823113
  have htrace : WordTrace (prefixWord ++ tailWord_823113) baseStart_823113 baseEnd_823113 := by
    simpa [prefixWord, tailWord_823113, baseEnd_823113] using wordTrace_append hprefix tailTrace_823113
  have hstable : (prefixWord ++ tailWord_823113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823113).length < 2 ^ (prefixWord ++ tailWord_823113).sum := by decide
  have hdescent : baseEnd_823113 < baseStart_823113 := by decide
  rcases family_descends (prefixWord ++ tailWord_823113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823137 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 3]
def baseStart_823137 : Nat := 118140960795 + 823137 * 2 ^ 59
def prefixEnd_823137 : Nat := 4983230072969 + 3 ^ 40 * 823137 * 2
def baseEnd_823137 : Nat := 375702156000045516801749

theorem tailTrace_823137 : CollatzResearch.WordTrace tailWord_823137 prefixEnd_823137 375702156000045516801749 := by
  unfold tailWord_823137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30022272818922704452515665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20014848545948469635010443 30022272818922704452515665)
  ·
    refine ⟨22516704614192028339386749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30022272818922704452515665 22516704614192028339386749)
    ·
      refine ⟨8443764230322010627270031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22516704614192028339386749 8443764230322010627270031)
      ·
        refine ⟨12665646345483015940905047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443764230322010627270031 12665646345483015940905047)
        ·
          refine ⟨18998469518224523911357571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12665646345483015940905047 18998469518224523911357571)
          ·
            refine ⟨28497704277336785867036357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18998469518224523911357571 28497704277336785867036357)
            ·
              refine ⟨5343319552000647350069317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28497704277336785867036357 5343319552000647350069317)
              ·
                refine ⟨1001872416000121378137997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5343319552000647350069317 1001872416000121378137997)
                ·
                  refine ⟨375702156000045516801749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001872416000121378137997 375702156000045516801749)
                  ·
                    rfl

theorem cell20_823137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_823137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823137 prefixEnd_823137 := by exact prefixLift 823137
  have htrace : WordTrace (prefixWord ++ tailWord_823137) baseStart_823137 baseEnd_823137 := by
    simpa [prefixWord, tailWord_823137, baseEnd_823137] using wordTrace_append hprefix tailTrace_823137
  have hstable : (prefixWord ++ tailWord_823137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823137).length < 2 ^ (prefixWord ++ tailWord_823137).sum := by decide
  have hdescent : baseEnd_823137 < baseStart_823137 := by decide
  rcases family_descends (prefixWord ++ tailWord_823137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823140 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_823140 : Nat := 118140960795 + 823140 * 2 ^ 59
def prefixEnd_823140 : Nat := 4983230072969 + 3 ^ 40 * 823140 * 2
def baseEnd_823140 : Nat := 375703525281790839701737

theorem tailTrace_823140 : CollatzResearch.WordTrace tailWord_823140 prefixEnd_823140 375703525281790839701737 := by
  unfold tailWord_823140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15011191118955917982437437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20014921491941223976583249 15011191118955917982437437)
  ·
    refine ⟨5629196669608469243414039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15011191118955917982437437 5629196669608469243414039)
    ·
      refine ⟨8443795004412703865121059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5629196669608469243414039 8443795004412703865121059)
      ·
        refine ⟨12665692506619055797681589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443795004412703865121059 12665692506619055797681589)
        ·
          refine ⟨1187408672495536481032649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12665692506619055797681589 1187408672495536481032649)
          ·
            refine ⟨890556504371652360774487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1187408672495536481032649 890556504371652360774487)
            ·
              refine ⟨1335834756557478541161731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890556504371652360774487 1335834756557478541161731)
              ·
                refine ⟨2003752134836217811742597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1335834756557478541161731 2003752134836217811742597)
                ·
                  refine ⟨375703525281790839701737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2003752134836217811742597 375703525281790839701737)
                  ·
                    rfl

theorem cell20_823140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_823140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823140 prefixEnd_823140 := by exact prefixLift 823140
  have htrace : WordTrace (prefixWord ++ tailWord_823140) baseStart_823140 baseEnd_823140 := by
    simpa [prefixWord, tailWord_823140, baseEnd_823140] using wordTrace_append hprefix tailTrace_823140
  have hstable : (prefixWord ++ tailWord_823140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823140).length < 2 ^ (prefixWord ++ tailWord_823140).sum := by decide
  have hdescent : baseEnd_823140 < baseStart_823140 := by decide
  rcases family_descends (prefixWord ++ tailWord_823140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823150 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_823150 : Nat := 118140960795 + 823150 * 2 ^ 59
def prefixEnd_823150 : Nat := 4983230072969 + 3 ^ 40 * 823150 * 2
def baseEnd_823150 : Nat := 375708089554275249368363

theorem tailTrace_823150 : CollatzResearch.WordTrace tailWord_823150 prefixEnd_823150 375708089554275249368363 := by
  unfold tailWord_823150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752843370984450959092363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20015164645250405115159269 3752843370984450959092363)
  ·
    refine ⟨5629265056476676438638545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3752843370984450959092363 5629265056476676438638545)
    ·
      refine ⟨4221948792357507328978909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5629265056476676438638545 4221948792357507328978909)
      ·
        refine ⟨1583230797134065248367091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4221948792357507328978909 1583230797134065248367091)
        ·
          refine ⟨2374846195701097872550637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583230797134065248367091 2374846195701097872550637)
          ·
            refine ⟨890567323387911702206489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2374846195701097872550637 890567323387911702206489)
            ·
              refine ⟨667925492540933776654867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 890567323387911702206489 667925492540933776654867)
              ·
                refine ⟨1001888238811400664982301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 667925492540933776654867 1001888238811400664982301)
                ·
                  refine ⟨375708089554275249368363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1001888238811400664982301 375708089554275249368363)
                  ·
                    rfl

theorem cell20_823150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_823150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823150 prefixEnd_823150 := by exact prefixLift 823150
  have htrace : WordTrace (prefixWord ++ tailWord_823150) baseStart_823150 baseEnd_823150 := by
    simpa [prefixWord, tailWord_823150, baseEnd_823150] using wordTrace_append hprefix tailTrace_823150
  have hstable : (prefixWord ++ tailWord_823150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823150).length < 2 ^ (prefixWord ++ tailWord_823150).sum := by decide
  have hdescent : baseEnd_823150 < baseStart_823150 := by decide
  rcases family_descends (prefixWord ++ tailWord_823150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823202 : List Nat := [3, 3, 1, 2, 4, 1, 1, 5]
def baseStart_823202 : Nat := 118140960795 + 823202 * 2 ^ 59
def prefixEnd_823202 : Nat := 4983230072969 + 3 ^ 40 * 823202 * 2
def baseEnd_823202 : Nat := 125243941257064726544939

theorem tailTrace_823202 : CollatzResearch.WordTrace tailWord_823202 prefixEnd_823202 125243941257064726544939 := by
  unfold tailWord_823202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7506160890921805138407965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20016429042458147035754573 7506160890921805138407965)
  ·
    refine ⟨2814810334095676926902987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7506160890921805138407965 2814810334095676926902987)
    ·
      refine ⟨4222215501143515390354481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2814810334095676926902987 4222215501143515390354481)
      ·
        refine ⟨3166661625857636542765861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4222215501143515390354481 3166661625857636542765861)
        ·
          refine ⟨593749054848306851768599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3166661625857636542765861 593749054848306851768599)
          ·
            refine ⟨890623582272460277652899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593749054848306851768599 890623582272460277652899)
            ·
              refine ⟨1335935373408690416479349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890623582272460277652899 1335935373408690416479349)
              ·
                refine ⟨125243941257064726544939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1335935373408690416479349 125243941257064726544939)
                ·
                  rfl

theorem cell20_823202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_823202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823202 prefixEnd_823202 := by exact prefixLift 823202
  have htrace : WordTrace (prefixWord ++ tailWord_823202) baseStart_823202 baseEnd_823202 := by
    simpa [prefixWord, tailWord_823202, baseEnd_823202] using wordTrace_append hprefix tailTrace_823202
  have hstable : (prefixWord ++ tailWord_823202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823202).length < 2 ^ (prefixWord ++ tailWord_823202).sum := by decide
  have hdescent : baseEnd_823202 < baseStart_823202 := by decide
  rcases family_descends (prefixWord ++ tailWord_823202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823268 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_823268 : Nat := 118140960795 + 823268 * 2 ^ 59
def prefixEnd_823268 : Nat := 4983230072969 + 3 ^ 40 * 823268 * 2
def baseEnd_823268 : Nat := 375761947969591283434547

theorem tailTrace_823268 : CollatzResearch.WordTrace tailWord_823268 prefixEnd_823268 375761947969591283434547 := by
  unfold tailWord_823268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15013525390724056912767229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20018033854298742550356305 15013525390724056912767229)
  ·
    refine ⟨5630072021521521342287711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15013525390724056912767229 5630072021521521342287711)
    ·
      refine ⟨8445108032282282013431567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5630072021521521342287711 8445108032282282013431567)
      ·
        refine ⟨12667662048423423020147351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8445108032282282013431567 12667662048423423020147351)
        ·
          refine ⟨19001493072635134530221027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12667662048423423020147351 19001493072635134530221027)
          ·
            refine ⟨28502239608952701795331541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19001493072635134530221027 28502239608952701795331541)
            ·
              refine ⟨668021240834828948328083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28502239608952701795331541 668021240834828948328083)
              ·
                refine ⟨1002031861252243422492125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668021240834828948328083 1002031861252243422492125)
                ·
                  refine ⟨375761947969591283434547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002031861252243422492125 375761947969591283434547)
                  ·
                    rfl

theorem cell20_823268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_823268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823268 prefixEnd_823268 := by exact prefixLift 823268
  have htrace : WordTrace (prefixWord ++ tailWord_823268) baseStart_823268 baseEnd_823268 := by
    simpa [prefixWord, tailWord_823268, baseEnd_823268] using wordTrace_append hprefix tailTrace_823268
  have hstable : (prefixWord ++ tailWord_823268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823268).length < 2 ^ (prefixWord ++ tailWord_823268).sum := by decide
  have hdescent : baseEnd_823268 < baseStart_823268 := by decide
  rcases family_descends (prefixWord ++ tailWord_823268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823303 : List Nat := [1, 1, 4, 3, 1, 2, 8]
def baseStart_823303 : Nat := 118140960795 + 823303 * 2 ^ 59
def prefixEnd_823303 : Nat := 4983230072969 + 3 ^ 40 * 823303 * 2
def baseEnd_823303 : Nat := 41753102547031857474193

theorem tailTrace_823303 : CollatzResearch.WordTrace tailWord_823303 prefixEnd_823303 41753102547031857474193 := by
  unfold tailWord_823303
  simp only [CollatzResearch.WordTrace]
  refine ⟨30028327336321314803058563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20018884890880876535372375 30028327336321314803058563)
  ·
    refine ⟨45042491004481972204587845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30028327336321314803058563 45042491004481972204587845)
    ·
      refine ⟨8445467063340369788360221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45042491004481972204587845 8445467063340369788360221)
      ·
        refine ⟨3167050148752638670635083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8445467063340369788360221 3167050148752638670635083)
        ·
          refine ⟨4750575223128958005952625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167050148752638670635083 4750575223128958005952625)
          ·
            refine ⟨3562931417346718504464469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4750575223128958005952625 3562931417346718504464469)
            ·
              refine ⟨41753102547031857474193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3562931417346718504464469 41753102547031857474193)
              ·
                rfl

theorem cell20_823303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_823303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823303 prefixEnd_823303 := by exact prefixLift 823303
  have htrace : WordTrace (prefixWord ++ tailWord_823303) baseStart_823303 baseEnd_823303 := by
    simpa [prefixWord, tailWord_823303, baseEnd_823303] using wordTrace_append hprefix tailTrace_823303
  have hstable : (prefixWord ++ tailWord_823303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823303).length < 2 ^ (prefixWord ++ tailWord_823303).sum := by decide
  have hdescent : baseEnd_823303 < baseStart_823303 := by decide
  rcases family_descends (prefixWord ++ tailWord_823303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823316 : List Nat := [2, 4, 3, 2, 1, 1, 2, 5]
def baseStart_823316 : Nat := 118140960795 + 823316 * 2 ^ 59
def prefixEnd_823316 : Nat := 4983230072969 + 3 ^ 40 * 823316 * 2
def baseEnd_823316 : Nat := 125261285492505483278117

theorem tailTrace_823316 : CollatzResearch.WordTrace tailWord_823316 prefixEnd_823316 125261285492505483278117 := by
  unfold tailWord_823316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15014400742637109011640901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20019200990182812015521201 15014400742637109011640901)
  ·
    refine ⟨2815200139244457939682669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15014400742637109011640901 2815200139244457939682669)
    ·
      refine ⟨1055700052216671727381001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2815200139244457939682669 1055700052216671727381001)
      ·
        refine ⟨791775039162503795535751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1055700052216671727381001 791775039162503795535751)
        ·
          refine ⟨1187662558743755693303627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791775039162503795535751 1187662558743755693303627)
          ·
            refine ⟨1781493838115633539955441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187662558743755693303627 1781493838115633539955441)
            ·
              refine ⟨1336120378586725154966581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781493838115633539955441 1336120378586725154966581)
              ·
                refine ⟨125261285492505483278117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1336120378586725154966581 125261285492505483278117)
                ·
                  rfl

theorem cell20_823316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_823316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823316 prefixEnd_823316 := by exact prefixLift 823316
  have htrace : WordTrace (prefixWord ++ tailWord_823316) baseStart_823316 baseEnd_823316 := by
    simpa [prefixWord, tailWord_823316, baseEnd_823316] using wordTrace_append hprefix tailTrace_823316
  have hstable : (prefixWord ++ tailWord_823316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823316).length < 2 ^ (prefixWord ++ tailWord_823316).sum := by decide
  have hdescent : baseEnd_823316 < baseStart_823316 := by decide
  rcases family_descends (prefixWord ++ tailWord_823316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823327 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 3]
def baseStart_823327 : Nat := 118140960795 + 823327 * 2 ^ 59
def prefixEnd_823327 : Nat := 4983230072969 + 3 ^ 40 * 823327 * 2
def baseEnd_823327 : Nat := 375788877177249300467639

theorem tailTrace_823327 : CollatzResearch.WordTrace tailWord_823327 prefixEnd_823327 375788877177249300467639 := by
  unfold tailWord_823327
  simp only [CollatzResearch.WordTrace]
  refine ⟨30029202688234366901932235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20019468458822911267954823 30029202688234366901932235)
  ·
    refine ⟨45043804032351550352898353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30029202688234366901932235 45043804032351550352898353)
    ·
      refine ⟨33782853024263662764673765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45043804032351550352898353 33782853024263662764673765)
      ·
        refine ⟨6334284942049436768376331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33782853024263662764673765 6334284942049436768376331)
        ·
          refine ⟨9501427413074155152564497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6334284942049436768376331 9501427413074155152564497)
          ·
            refine ⟨7126070559805616364423373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9501427413074155152564497 7126070559805616364423373)
            ·
              refine ⟨2672276459927106136658765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7126070559805616364423373 2672276459927106136658765)
              ·
                refine ⟨1002103672472664801247037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2672276459927106136658765 1002103672472664801247037)
                ·
                  refine ⟨375788877177249300467639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002103672472664801247037 375788877177249300467639)
                  ·
                    rfl

theorem cell20_823327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_823327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823327 prefixEnd_823327 := by exact prefixLift 823327
  have htrace : WordTrace (prefixWord ++ tailWord_823327) baseStart_823327 baseEnd_823327 := by
    simpa [prefixWord, tailWord_823327, baseEnd_823327] using wordTrace_append hprefix tailTrace_823327
  have hstable : (prefixWord ++ tailWord_823327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823327).length < 2 ^ (prefixWord ++ tailWord_823327).sum := by decide
  have hdescent : baseEnd_823327 < baseStart_823327 := by decide
  rcases family_descends (prefixWord ++ tailWord_823327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823355 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_823355 : Nat := 118140960795 + 823355 * 2 ^ 59
def prefixEnd_823355 : Nat := 4983230072969 + 3 ^ 40 * 823355 * 2
def baseEnd_823355 : Nat := 375801657140205647534191

theorem tailTrace_823355 : CollatzResearch.WordTrace tailWord_823355 prefixEnd_823355 375801657140205647534191 := by
  unfold tailWord_823355
  simp only [CollatzResearch.WordTrace]
  refine ⟨30030223932132927683951519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20020149288088618455967679 30030223932132927683951519)
  ·
    refine ⟨45045335898199391525927279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30030223932132927683951519 45045335898199391525927279)
    ·
      refine ⟨67568003847299087288890919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45045335898199391525927279 67568003847299087288890919)
      ·
        refine ⟨101352005770948630933336379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67568003847299087288890919 101352005770948630933336379)
        ·
          refine ⟨152028008656422946400004569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101352005770948630933336379 152028008656422946400004569)
          ·
            refine ⟨114021006492317209800003427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152028008656422946400004569 114021006492317209800003427)
            ·
              refine ⟨171031509738475814700005141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114021006492317209800003427 171031509738475814700005141)
              ·
                refine ⟨8017102018991053814062741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171031509738475814700005141 8017102018991053814062741)
                ·
                  refine ⟨375801657140205647534191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8017102018991053814062741 375801657140205647534191)
                  ·
                    rfl

theorem cell20_823355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_823355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823355 prefixEnd_823355 := by exact prefixLift 823355
  have htrace : WordTrace (prefixWord ++ tailWord_823355) baseStart_823355 baseEnd_823355 := by
    simpa [prefixWord, tailWord_823355, baseEnd_823355] using wordTrace_append hprefix tailTrace_823355
  have hstable : (prefixWord ++ tailWord_823355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823355).length < 2 ^ (prefixWord ++ tailWord_823355).sum := by decide
  have hdescent : baseEnd_823355 < baseStart_823355 := by decide
  rcases family_descends (prefixWord ++ tailWord_823355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823358 : List Nat := [4, 2, 1, 3, 2, 8]
def baseStart_823358 : Nat := 118140960795 + 823358 * 2 ^ 59
def prefixEnd_823358 : Nat := 4983230072969 + 3 ^ 40 * 823358 * 2
def baseEnd_823358 : Nat := 13918630608220406312377

theorem tailTrace_823358 : CollatzResearch.WordTrace tailWord_823358 prefixEnd_823358 13918630608220406312377 := by
  unfold tailWord_823358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753791668890257399538841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20020222234081372797540485 3753791668890257399538841)
  ·
    refine ⟨2815343751667693049654131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3753791668890257399538841 2815343751667693049654131)
    ·
      refine ⟨4223015627501539574481197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2815343751667693049654131 4223015627501539574481197)
      ·
        refine ⟨1583630860313077340430449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4223015627501539574481197 1583630860313077340430449)
        ·
          refine ⟨1187723145234808005322837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583630860313077340430449 1187723145234808005322837)
          ·
            refine ⟨13918630608220406312377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1187723145234808005322837 13918630608220406312377)
            ·
              rfl

theorem cell20_823358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 8].length) (baseStart_823358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823358 prefixEnd_823358 := by exact prefixLift 823358
  have htrace : WordTrace (prefixWord ++ tailWord_823358) baseStart_823358 baseEnd_823358 := by
    simpa [prefixWord, tailWord_823358, baseEnd_823358] using wordTrace_append hprefix tailTrace_823358
  have hstable : (prefixWord ++ tailWord_823358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823358).length < 2 ^ (prefixWord ++ tailWord_823358).sum := by decide
  have hdescent : baseEnd_823358 < baseStart_823358 := by decide
  rcases family_descends (prefixWord ++ tailWord_823358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823389 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 6]
def baseStart_823389 : Nat := 118140960795 + 823389 * 2 ^ 59
def prefixEnd_823389 : Nat := 4983230072969 + 3 ^ 40 * 823389 * 2
def baseEnd_823389 : Nat := 375817175666652640400719

theorem tailTrace_823389 : CollatzResearch.WordTrace tailWord_823389 prefixEnd_823389 375817175666652640400719 := by
  unfold tailWord_823389
  simp only [CollatzResearch.WordTrace]
  refine ⟨30031464014009751490689221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20020976009339834327126147 30031464014009751490689221)
  ·
    refine ⟨5630899502626828404504229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30031464014009751490689221 5630899502626828404504229)
    ·
      refine ⟨1055793656742530325844543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5630899502626828404504229 1055793656742530325844543)
      ·
        refine ⟨1583690485113795488766815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055793656742530325844543 1583690485113795488766815)
        ·
          refine ⟨2375535727670693233150223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583690485113795488766815 2375535727670693233150223)
          ·
            refine ⟨3563303591506039849725335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375535727670693233150223 3563303591506039849725335)
            ·
              refine ⟨5344955387259059774588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563303591506039849725335 5344955387259059774588003)
              ·
                refine ⟨8017433080888589661882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5344955387259059774588003 8017433080888589661882005)
                ·
                  refine ⟨375817175666652640400719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8017433080888589661882005 375817175666652640400719)
                  ·
                    rfl

theorem cell20_823389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_823389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823389 prefixEnd_823389 := by exact prefixLift 823389
  have htrace : WordTrace (prefixWord ++ tailWord_823389) baseStart_823389 baseEnd_823389 := by
    simpa [prefixWord, tailWord_823389, baseEnd_823389] using wordTrace_append hprefix tailTrace_823389
  have hstable : (prefixWord ++ tailWord_823389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823389).length < 2 ^ (prefixWord ++ tailWord_823389).sum := by decide
  have hdescent : baseEnd_823389 < baseStart_823389 := by decide
  rcases family_descends (prefixWord ++ tailWord_823389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823406 : List Nat := [4, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_823406 : Nat := 118140960795 + 823406 * 2 ^ 59
def prefixEnd_823406 : Nat := 4983230072969 + 3 ^ 40 * 823406 * 2
def baseEnd_823406 : Nat := 375824934929876136833983

theorem tailTrace_823406 : CollatzResearch.WordTrace tailWord_823406 prefixEnd_823406 375824934929876136833983 := by
  unfold tailWord_823406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754010506868520424257259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20021389369965442262705381 3754010506868520424257259)
  ·
    refine ⟨5631015760302780636385889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3754010506868520424257259 5631015760302780636385889)
    ·
      refine ⟨4223261820227085477289417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5631015760302780636385889 4223261820227085477289417)
      ·
        refine ⟨3167446365170314107967063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4223261820227085477289417 3167446365170314107967063)
        ·
          refine ⟨4751169547755471161950595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3167446365170314107967063 4751169547755471161950595)
          ·
            refine ⟨7126754321633206742925893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4751169547755471161950595 7126754321633206742925893)
            ·
              refine ⟨1336266435306226264298605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7126754321633206742925893 1336266435306226264298605)
              ·
                refine ⟨501099913239834849111977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1336266435306226264298605 501099913239834849111977)
                ·
                  refine ⟨375824934929876136833983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501099913239834849111977 375824934929876136833983)
                  ·
                    rfl

theorem cell20_823406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_823406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823406 prefixEnd_823406 := by exact prefixLift 823406
  have htrace : WordTrace (prefixWord ++ tailWord_823406) baseStart_823406 baseEnd_823406 := by
    simpa [prefixWord, tailWord_823406, baseEnd_823406] using wordTrace_append hprefix tailTrace_823406
  have hstable : (prefixWord ++ tailWord_823406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823406).length < 2 ^ (prefixWord ++ tailWord_823406).sum := by decide
  have hdescent : baseEnd_823406 < baseStart_823406 := by decide
  rcases family_descends (prefixWord ++ tailWord_823406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823417 : List Nat := [1, 2, 1, 3, 4, 2, 7]
def baseStart_823417 : Nat := 118140960795 + 823417 * 2 ^ 59
def prefixEnd_823417 : Nat := 4983230072969 + 3 ^ 40 * 823417 * 2
def baseEnd_823417 : Nat := 41758883958845443051919

theorem tailTrace_823417 : CollatzResearch.WordTrace tailWord_823417 prefixEnd_823417 41758883958845443051919 := by
  unfold tailWord_823417
  simp only [CollatzResearch.WordTrace]
  refine ⟨30032485257908312272708505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20021656838605541515139003 30032485257908312272708505)
  ·
    refine ⟨22524363943431234204531379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30032485257908312272708505 22524363943431234204531379)
    ·
      refine ⟨33786545915146851306797069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22524363943431234204531379 33786545915146851306797069)
      ·
        refine ⟨12669954718180069240048901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33786545915146851306797069 12669954718180069240048901)
        ·
          refine ⟨2375616509658762982509169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12669954718180069240048901 2375616509658762982509169)
          ·
            refine ⟨1781712382244072236881877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375616509658762982509169 1781712382244072236881877)
            ·
              refine ⟨41758883958845443051919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1781712382244072236881877 41758883958845443051919)
              ·
                rfl

theorem cell20_823417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_823417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823417 prefixEnd_823417 := by exact prefixLift 823417
  have htrace : WordTrace (prefixWord ++ tailWord_823417) baseStart_823417 baseEnd_823417 := by
    simpa [prefixWord, tailWord_823417, baseEnd_823417] using wordTrace_append hprefix tailTrace_823417
  have hstable : (prefixWord ++ tailWord_823417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823417).length < 2 ^ (prefixWord ++ tailWord_823417).sum := by decide
  have hdescent : baseEnd_823417 < baseStart_823417 := by decide
  rcases family_descends (prefixWord ++ tailWord_823417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823420 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_823420 : Nat := 118140960795 + 823420 * 2 ^ 59
def prefixEnd_823420 : Nat := 4983230072969 + 3 ^ 40 * 823420 * 2
def baseEnd_823420 : Nat := 375831324911354310367259

theorem tailTrace_823420 : CollatzResearch.WordTrace tailWord_823420 prefixEnd_823420 375831324911354310367259 := by
  unfold tailWord_823420
  simp only [CollatzResearch.WordTrace]
  refine ⟨15016297338448721892533857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20021729784598295856711809 15016297338448721892533857)
  ·
    refine ⟨11262223003836541419400393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15016297338448721892533857 11262223003836541419400393)
    ·
      refine ⟨8446667252877406064550295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11262223003836541419400393 8446667252877406064550295)
      ·
        refine ⟨12670000879316109096825443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8446667252877406064550295 12670000879316109096825443)
        ·
          refine ⟨19005001318974163645238165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12670000879316109096825443 19005001318974163645238165)
          ·
            refine ⟨890859436826913920870539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19005001318974163645238165 890859436826913920870539)
            ·
              refine ⟨1336289155240370881305809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890859436826913920870539 1336289155240370881305809)
              ·
                refine ⟨1002216866430278160979357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336289155240370881305809 1002216866430278160979357)
                ·
                  refine ⟨375831324911354310367259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002216866430278160979357 375831324911354310367259)
                  ·
                    rfl

theorem cell20_823420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_823420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823420 prefixEnd_823420 := by exact prefixLift 823420
  have htrace : WordTrace (prefixWord ++ tailWord_823420) baseStart_823420 baseEnd_823420 := by
    simpa [prefixWord, tailWord_823420, baseEnd_823420] using wordTrace_append hprefix tailTrace_823420
  have hstable : (prefixWord ++ tailWord_823420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823420).length < 2 ^ (prefixWord ++ tailWord_823420).sum := by decide
  have hdescent : baseEnd_823420 < baseStart_823420 := by decide
  rcases family_descends (prefixWord ++ tailWord_823420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823427 : List Nat := [1, 1, 1, 3, 3, 3, 2, 4, 2]
def baseStart_823427 : Nat := 118140960795 + 823427 * 2 ^ 59
def prefixEnd_823427 : Nat := 4983230072969 + 3 ^ 40 * 823427 * 2
def baseEnd_823427 : Nat := 375834519902093397133897

theorem tailTrace_823427 : CollatzResearch.WordTrace tailWord_823427 prefixEnd_823427 375834519902093397133897 := by
  unfold tailWord_823427
  simp only [CollatzResearch.WordTrace]
  refine ⟨30032849987872083980572535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20021899991914722653715023 30032849987872083980572535)
  ·
    refine ⟨45049274981808125970858803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30032849987872083980572535 45049274981808125970858803)
    ·
      refine ⟨67573912472712188956288205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45049274981808125970858803 67573912472712188956288205)
      ·
        refine ⟨25340217177267070858608077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67573912472712188956288205 25340217177267070858608077)
        ·
          refine ⟨9502581441475151571978029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25340217177267070858608077 9502581441475151571978029)
          ·
            refine ⟨3563468040553181839491761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9502581441475151571978029 3563468040553181839491761)
            ·
              refine ⟨2672601030414886379618821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3563468040553181839491761 2672601030414886379618821)
              ·
                refine ⟨501112693202791196178529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2672601030414886379618821 501112693202791196178529)
                ·
                  refine ⟨375834519902093397133897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501112693202791196178529 375834519902093397133897)
                  ·
                    rfl

theorem cell20_823427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 2].length) (baseStart_823427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823427 prefixEnd_823427 := by exact prefixLift 823427
  have htrace : WordTrace (prefixWord ++ tailWord_823427) baseStart_823427 baseEnd_823427 := by
    simpa [prefixWord, tailWord_823427, baseEnd_823427] using wordTrace_append hprefix tailTrace_823427
  have hstable : (prefixWord ++ tailWord_823427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823427).length < 2 ^ (prefixWord ++ tailWord_823427).sum := by decide
  have hdescent : baseEnd_823427 < baseStart_823427 := by decide
  rcases family_descends (prefixWord ++ tailWord_823427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823489 : List Nat := [1, 2, 6, 1, 2, 1, 2, 5]
def baseStart_823489 : Nat := 118140960795 + 823489 * 2 ^ 59
def prefixEnd_823489 : Nat := 4983230072969 + 3 ^ 40 * 823489 * 2
def baseEnd_823489 : Nat := 125287606130498912355659

theorem tailTrace_823489 : CollatzResearch.WordTrace tailWord_823489 prefixEnd_823489 125287606130498912355659 := by
  unfold tailWord_823489
  simp only [CollatzResearch.WordTrace]
  refine ⟨30035111313647468569329521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20023407542431645712886347 30035111313647468569329521)
  ·
    refine ⟨22526333485235601426997141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30035111313647468569329521 22526333485235601426997141)
    ·
      refine ⟨1055921882120418816890491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22526333485235601426997141 1055921882120418816890491)
      ·
        refine ⟨1583882823180628225335737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055921882120418816890491 1583882823180628225335737)
        ·
          refine ⟨1187912117385471169001803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583882823180628225335737 1187912117385471169001803)
          ·
            refine ⟨1781868176078206753502705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187912117385471169001803 1781868176078206753502705)
            ·
              refine ⟨1336401132058655065127029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1781868176078206753502705 1336401132058655065127029)
              ·
                refine ⟨125287606130498912355659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1336401132058655065127029 125287606130498912355659)
                ·
                  rfl

theorem cell20_823489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_823489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823489 prefixEnd_823489 := by exact prefixLift 823489
  have htrace : WordTrace (prefixWord ++ tailWord_823489) baseStart_823489 baseEnd_823489 := by
    simpa [prefixWord, tailWord_823489, baseEnd_823489] using wordTrace_append hprefix tailTrace_823489
  have hstable : (prefixWord ++ tailWord_823489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823489).length < 2 ^ (prefixWord ++ tailWord_823489).sum := by decide
  have hdescent : baseEnd_823489 < baseStart_823489 := by decide
  rcases family_descends (prefixWord ++ tailWord_823489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823548 : List Nat := [2, 2, 2, 1, 4, 3, 1, 5]
def baseStart_823548 : Nat := 118140960795 + 823548 * 2 ^ 59
def prefixEnd_823548 : Nat := 4983230072969 + 3 ^ 40 * 823548 * 2
def baseEnd_823548 : Nat := 125296582533051584700023

theorem tailTrace_823548 : CollatzResearch.WordTrace tailWord_823548 prefixEnd_823548 125296582533051584700023 := by
  unfold tailWord_823548
  simp only [CollatzResearch.WordTrace]
  refine ⟨15018631610216860822863649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20024842146955814430484865 15018631610216860822863649)
  ·
    refine ⟨11263973707662645617147737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15018631610216860822863649 11263973707662645617147737)
    ·
      refine ⟨8447980280746984212860803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11263973707662645617147737 8447980280746984212860803)
      ·
        refine ⟨12671970421120476319291205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8447980280746984212860803 12671970421120476319291205)
        ·
          refine ⟨2375994453960089309867101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12671970421120476319291205 2375994453960089309867101)
          ·
            refine ⟨890997920235033491200163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2375994453960089309867101 890997920235033491200163)
            ·
              refine ⟨1336496880352550236800245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890997920235033491200163 1336496880352550236800245)
              ·
                refine ⟨125296582533051584700023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1336496880352550236800245 125296582533051584700023)
                ·
                  rfl

theorem cell20_823548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_823548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823548 prefixEnd_823548 := by exact prefixLift 823548
  have htrace : WordTrace (prefixWord ++ tailWord_823548) baseStart_823548 baseEnd_823548 := by
    simpa [prefixWord, tailWord_823548, baseEnd_823548] using wordTrace_append hprefix tailTrace_823548
  have hstable : (prefixWord ++ tailWord_823548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823548).length < 2 ^ (prefixWord ++ tailWord_823548).sum := by decide
  have hdescent : baseEnd_823548 < baseStart_823548 := by decide
  rcases family_descends (prefixWord ++ tailWord_823548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823576 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_823576 : Nat := 118140960795 + 823576 * 2 ^ 59
def prefixEnd_823576 : Nat := 4983230072969 + 3 ^ 40 * 823576 * 2
def baseEnd_823576 : Nat := 375902527562111101166621

theorem tailTrace_823576 : CollatzResearch.WordTrace tailWord_823576 prefixEnd_823576 375902527562111101166621 := by
  unfold tailWord_823576
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019142232166141213873291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20025522976221521618497721 15019142232166141213873291)
  ·
    refine ⟨22528713348249211820809937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15019142232166141213873291 22528713348249211820809937)
    ·
      refine ⟨16896535011186908865607453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22528713348249211820809937 16896535011186908865607453)
      ·
        refine ⟨6336200629195090824602795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16896535011186908865607453 6336200629195090824602795)
        ·
          refine ⟨9504300943792636236904193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6336200629195090824602795 9504300943792636236904193)
          ·
            refine ⟨7128225707844477177678145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9504300943792636236904193 7128225707844477177678145)
            ·
              refine ⟨5346169280883357883258609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7128225707844477177678145 5346169280883357883258609)
              ·
                refine ⟨4009626960662518412443957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5346169280883357883258609 4009626960662518412443957)
                ·
                  refine ⟨375902527562111101166621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4009626960662518412443957 375902527562111101166621)
                  ·
                    rfl

theorem cell20_823576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_823576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823576 prefixEnd_823576 := by exact prefixLift 823576
  have htrace : WordTrace (prefixWord ++ tailWord_823576) baseStart_823576 baseEnd_823576 := by
    simpa [prefixWord, tailWord_823576, baseEnd_823576] using wordTrace_append hprefix tailTrace_823576
  have hstable : (prefixWord ++ tailWord_823576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823576).length < 2 ^ (prefixWord ++ tailWord_823576).sum := by decide
  have hdescent : baseEnd_823576 < baseStart_823576 := by decide
  rcases family_descends (prefixWord ++ tailWord_823576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823589 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 3]
def baseStart_823589 : Nat := 118140960795 + 823589 * 2 ^ 59
def prefixEnd_823589 : Nat := 4983230072969 + 3 ^ 40 * 823589 * 2
def baseEnd_823589 : Nat := 375908461116340833733235

theorem tailTrace_823589 : CollatzResearch.WordTrace tailWord_823589 prefixEnd_823589 375908461116340833733235 := by
  unfold tailWord_823589
  simp only [CollatzResearch.WordTrace]
  refine ⟨30038758613285185647969821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20025839075523457098646547 30038758613285185647969821)
  ·
    refine ⟨11264534479981944617988683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30038758613285185647969821 11264534479981944617988683)
    ·
      refine ⟨16896801719972916926983025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11264534479981944617988683 16896801719972916926983025)
      ·
        refine ⟨12672601289979687695237269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16896801719972916926983025 12672601289979687695237269)
        ·
          refine ⟨594028185467797860714247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12672601289979687695237269 594028185467797860714247)
          ·
            refine ⟨891042278201696791071371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594028185467797860714247 891042278201696791071371)
            ·
              refine ⟨1336563417302545186607057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891042278201696791071371 1336563417302545186607057)
              ·
                refine ⟨1002422562976908889955293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336563417302545186607057 1002422562976908889955293)
                ·
                  refine ⟨375908461116340833733235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002422562976908889955293 375908461116340833733235)
                  ·
                    rfl

theorem cell20_823589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_823589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823589 prefixEnd_823589 := by exact prefixLift 823589
  have htrace : WordTrace (prefixWord ++ tailWord_823589) baseStart_823589 baseEnd_823589 := by
    simpa [prefixWord, tailWord_823589, baseEnd_823589] using wordTrace_append hprefix tailTrace_823589
  have hstable : (prefixWord ++ tailWord_823589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823589).length < 2 ^ (prefixWord ++ tailWord_823589).sum := by decide
  have hdescent : baseEnd_823589 < baseStart_823589 := by decide
  rcases family_descends (prefixWord ++ tailWord_823589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823610 : List Nat := [3, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_823610 : Nat := 118140960795 + 823610 * 2 ^ 59
def prefixEnd_823610 : Nat := 4983230072969 + 3 ^ 40 * 823610 * 2
def baseEnd_823610 : Nat := 375918046088558094033149

theorem tailTrace_823610 : CollatzResearch.WordTrace tailWord_823610 prefixEnd_823610 375918046088558094033149 := by
  unfold tailWord_823610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7509881136552276558621071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20026349697472737489656189 7509881136552276558621071)
  ·
    refine ⟨11264821704828414837931607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7509881136552276558621071 11264821704828414837931607)
    ·
      refine ⟨16897232557242622256897411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11264821704828414837931607 16897232557242622256897411)
      ·
        refine ⟨25345848835863933385346117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16897232557242622256897411 25345848835863933385346117)
        ·
          refine ⟨4752346656724487509752397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25345848835863933385346117 4752346656724487509752397)
          ·
            refine ⟨1782129996271682816157149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4752346656724487509752397 1782129996271682816157149)
            ·
              refine ⟨668298748601881056058931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1782129996271682816157149 668298748601881056058931)
              ·
                refine ⟨1002448122902821584088397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668298748601881056058931 1002448122902821584088397)
                ·
                  refine ⟨375918046088558094033149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002448122902821584088397 375918046088558094033149)
                  ·
                    rfl

theorem cell20_823610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_823610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823610 prefixEnd_823610 := by exact prefixLift 823610
  have htrace : WordTrace (prefixWord ++ tailWord_823610) baseStart_823610 baseEnd_823610 := by
    simpa [prefixWord, tailWord_823610, baseEnd_823610] using wordTrace_append hprefix tailTrace_823610
  have hstable : (prefixWord ++ tailWord_823610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823610).length < 2 ^ (prefixWord ++ tailWord_823610).sum := by decide
  have hdescent : baseEnd_823610 < baseStart_823610 := by decide
  rcases family_descends (prefixWord ++ tailWord_823610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823620 : List Nat := [2, 3, 4, 1, 2, 2, 2, 4]
def baseStart_823620 : Nat := 118140960795 + 823620 * 2 ^ 59
def prefixEnd_823620 : Nat := 4983230072969 + 3 ^ 40 * 823620 * 2
def baseEnd_823620 : Nat := 125307536787014167899925

theorem tailTrace_823620 : CollatzResearch.WordTrace tailWord_823620 prefixEnd_823620 125307536787014167899925 := by
  unfold tailWord_823620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15019944638086438971174157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20026592850781918628232209 15019944638086438971174157)
  ·
    refine ⟨5632479239282414614190309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15019944638086438971174157 5632479239282414614190309)
    ·
      refine ⟨1056089857365452740160683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5632479239282414614190309 1056089857365452740160683)
      ·
        refine ⟨1584134786048179110241025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1056089857365452740160683 1584134786048179110241025)
        ·
          refine ⟨1188101089536134332680769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1584134786048179110241025 1188101089536134332680769)
          ·
            refine ⟨891075817152100749510577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188101089536134332680769 891075817152100749510577)
            ·
              refine ⟨668306862864075562132933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891075817152100749510577 668306862864075562132933)
              ·
                refine ⟨125307536787014167899925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 668306862864075562132933 125307536787014167899925)
                ·
                  rfl

theorem cell20_823620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_823620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823620 prefixEnd_823620 := by exact prefixLift 823620
  have htrace : WordTrace (prefixWord ++ tailWord_823620) baseStart_823620 baseEnd_823620 := by
    simpa [prefixWord, tailWord_823620, baseEnd_823620] using wordTrace_append hprefix tailTrace_823620
  have hstable : (prefixWord ++ tailWord_823620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823620).length < 2 ^ (prefixWord ++ tailWord_823620).sum := by decide
  have hdescent : baseEnd_823620 < baseStart_823620 := by decide
  rcases family_descends (prefixWord ++ tailWord_823620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823652 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_823652 : Nat := 118140960795 + 823652 * 2 ^ 59
def prefixEnd_823652 : Nat := 4983230072969 + 3 ^ 40 * 823652 * 2
def baseEnd_823652 : Nat := 375937216032992614632977

theorem tailTrace_823652 : CollatzResearch.WordTrace tailWord_823652 prefixEnd_823652 375937216032992614632977 := by
  unfold tailWord_823652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15020528206028473703756605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20027370941371298271675473 15020528206028473703756605)
  ·
    refine ⟨5632698077260677638908727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15020528206028473703756605 5632698077260677638908727)
    ·
      refine ⟨8449047115891016458363091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5632698077260677638908727 8449047115891016458363091)
      ·
        refine ⟨12673570673836524687544637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8449047115891016458363091 12673570673836524687544637)
        ·
          refine ⟨4752589002688696757829239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12673570673836524687544637 4752589002688696757829239)
          ·
            refine ⟨7128883504033045136743859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752589002688696757829239 7128883504033045136743859)
            ·
              refine ⟨10693325256049567705115789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7128883504033045136743859 10693325256049567705115789)
              ·
                refine ⟨4009996971018587889418421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10693325256049567705115789 4009996971018587889418421)
                ·
                  refine ⟨375937216032992614632977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4009996971018587889418421 375937216032992614632977)
                  ·
                    rfl

theorem cell20_823652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_823652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823652 prefixEnd_823652 := by exact prefixLift 823652
  have htrace : WordTrace (prefixWord ++ tailWord_823652) baseStart_823652 baseEnd_823652 := by
    simpa [prefixWord, tailWord_823652, baseEnd_823652] using wordTrace_append hprefix tailTrace_823652
  have hstable : (prefixWord ++ tailWord_823652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823652).length < 2 ^ (prefixWord ++ tailWord_823652).sum := by decide
  have hdescent : baseEnd_823652 < baseStart_823652 := by decide
  rcases family_descends (prefixWord ++ tailWord_823652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823655 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 4]
def baseStart_823655 : Nat := 118140960795 + 823655 * 2 ^ 59
def prefixEnd_823655 : Nat := 4983230072969 + 3 ^ 40 * 823655 * 2
def baseEnd_823655 : Nat := 375938585314737937532965

theorem tailTrace_823655 : CollatzResearch.WordTrace tailWord_823655 prefixEnd_823655 375938585314737937532965 := by
  unfold tailWord_823655
  simp only [CollatzResearch.WordTrace]
  refine ⟨30041165831046078919872419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20027443887364052613248279 30041165831046078919872419)
  ·
    refine ⟨45061748746569118379808629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30041165831046078919872419 45061748746569118379808629)
    ·
      refine ⟨4224538944990854848107059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45061748746569118379808629 4224538944990854848107059)
      ·
        refine ⟨6336808417486282272160589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4224538944990854848107059 6336808417486282272160589)
        ·
          refine ⟨2376303156557355852060221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6336808417486282272160589 2376303156557355852060221)
          ·
            refine ⟨891113683709008444522583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2376303156557355852060221 891113683709008444522583)
            ·
              refine ⟨1336670525563512666783875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891113683709008444522583 1336670525563512666783875)
              ·
                refine ⟨2005005788345269000175813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1336670525563512666783875 2005005788345269000175813)
                ·
                  refine ⟨375938585314737937532965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005005788345269000175813 375938585314737937532965)
                  ·
                    rfl

theorem cell20_823655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_823655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823655 prefixEnd_823655 := by exact prefixLift 823655
  have htrace : WordTrace (prefixWord ++ tailWord_823655) baseStart_823655 baseEnd_823655 := by
    simpa [prefixWord, tailWord_823655, baseEnd_823655] using wordTrace_append hprefix tailTrace_823655
  have hstable : (prefixWord ++ tailWord_823655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823655).length < 2 ^ (prefixWord ++ tailWord_823655).sum := by decide
  have hdescent : baseEnd_823655 < baseStart_823655 := by decide
  rcases family_descends (prefixWord ++ tailWord_823655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823700 : List Nat := [2, 4, 2, 1, 4, 7]
def baseStart_823700 : Nat := 118140960795 + 823700 * 2 ^ 59
def prefixEnd_823700 : Nat := 4983230072969 + 3 ^ 40 * 823700 * 2
def baseEnd_823700 : Nat := 13924412020033991890103

theorem tailTrace_823700 : CollatzResearch.WordTrace tailWord_823700 prefixEnd_823700 13924412020033991890103 := by
  unfold tailWord_823700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15021403557941525802630277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20028538077255367736840369 15021403557941525802630277)
  ·
    refine ⟨2816513167114036087993177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15021403557941525802630277 2816513167114036087993177)
    ·
      refine ⟨2112384875335527065994883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2816513167114036087993177 2112384875335527065994883)
      ·
        refine ⟨3168577313003290598992325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112384875335527065994883 3168577313003290598992325)
        ·
          refine ⟨594108246188116987311061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3168577313003290598992325 594108246188116987311061)
          ·
            refine ⟨13924412020033991890103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 594108246188116987311061 13924412020033991890103)
            ·
              rfl

theorem cell20_823700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 7].length) (baseStart_823700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823700 prefixEnd_823700 := by exact prefixLift 823700
  have htrace : WordTrace (prefixWord ++ tailWord_823700) baseStart_823700 baseEnd_823700 := by
    simpa [prefixWord, tailWord_823700, baseEnd_823700] using wordTrace_append hprefix tailTrace_823700
  have hstable : (prefixWord ++ tailWord_823700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823700).length < 2 ^ (prefixWord ++ tailWord_823700).sum := by decide
  have hdescent : baseEnd_823700 < baseStart_823700 := by decide
  rcases family_descends (prefixWord ++ tailWord_823700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823702 : List Nat := [5, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_823702 : Nat := 118140960795 + 823702 * 2 ^ 59
def prefixEnd_823702 : Nat := 4983230072969 + 3 ^ 40 * 823702 * 2
def baseEnd_823702 : Nat := 375960037395414662966107

theorem tailTrace_823702 : CollatzResearch.WordTrace tailWord_823702 prefixEnd_823702 375960037395414662966107 := by
  unfold tailWord_823702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1877680003867237871677085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20028586707917203964555573 1877680003867237871677085)
  ·
    refine ⟨704130001450214201878907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1877680003867237871677085 704130001450214201878907)
    ·
      refine ⟨1056195002175321302818361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 704130001450214201878907 1056195002175321302818361)
      ·
        refine ⟨792146251631490977113771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1056195002175321302818361 792146251631490977113771)
        ·
          refine ⟨1188219377447236465670657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792146251631490977113771 1188219377447236465670657)
          ·
            refine ⟨891164533085427349252993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188219377447236465670657 891164533085427349252993)
            ·
              refine ⟨668373399814070511939745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891164533085427349252993 668373399814070511939745)
              ·
                refine ⟨501280049860552883954809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668373399814070511939745 501280049860552883954809)
                ·
                  refine ⟨375960037395414662966107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501280049860552883954809 375960037395414662966107)
                  ·
                    rfl

theorem cell20_823702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_823702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823702 prefixEnd_823702 := by exact prefixLift 823702
  have htrace : WordTrace (prefixWord ++ tailWord_823702) baseStart_823702 baseEnd_823702 := by
    simpa [prefixWord, tailWord_823702, baseEnd_823702] using wordTrace_append hprefix tailTrace_823702
  have hstable : (prefixWord ++ tailWord_823702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823702).length < 2 ^ (prefixWord ++ tailWord_823702).sum := by decide
  have hdescent : baseEnd_823702 < baseStart_823702 := by decide
  rcases family_descends (prefixWord ++ tailWord_823702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823714 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_823714 : Nat := 118140960795 + 823714 * 2 ^ 59
def prefixEnd_823714 : Nat := 4983230072969 + 3 ^ 40 * 823714 * 2
def baseEnd_823714 : Nat := 375965514522395954566057

theorem tailTrace_823714 : CollatzResearch.WordTrace tailWord_823714 prefixEnd_823714 375965514522395954566057 := by
  unfold tailWord_823714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7510829434458082999067549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20028878491888221330846797 7510829434458082999067549)
  ·
    refine ⟨2816561037921781124650331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7510829434458082999067549 2816561037921781124650331)
    ·
      refine ⟨4224841556882671686975497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816561037921781124650331 4224841556882671686975497)
      ·
        refine ⟨3168631167662003765231623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4224841556882671686975497 3168631167662003765231623)
        ·
          refine ⟨4752946751493005647847435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168631167662003765231623 4752946751493005647847435)
          ·
            refine ⟨7129420127239508471771153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4752946751493005647847435 7129420127239508471771153)
            ·
              refine ⟨5347065095429631353828365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7129420127239508471771153 5347065095429631353828365)
              ·
                refine ⟨2005149410786111757685637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5347065095429631353828365 2005149410786111757685637)
                ·
                  refine ⟨375965514522395954566057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005149410786111757685637 375965514522395954566057)
                  ·
                    rfl

theorem cell20_823714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_823714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823714 prefixEnd_823714 := by exact prefixLift 823714
  have htrace : WordTrace (prefixWord ++ tailWord_823714) baseStart_823714 baseEnd_823714 := by
    simpa [prefixWord, tailWord_823714, baseEnd_823714] using wordTrace_append hprefix tailTrace_823714
  have hstable : (prefixWord ++ tailWord_823714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823714).length < 2 ^ (prefixWord ++ tailWord_823714).sum := by decide
  have hdescent : baseEnd_823714 < baseStart_823714 := by decide
  rcases family_descends (prefixWord ++ tailWord_823714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823735 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_823735 : Nat := 118140960795 + 823735 * 2 ^ 59
def prefixEnd_823735 : Nat := 4983230072969 + 3 ^ 40 * 823735 * 2
def baseEnd_823735 : Nat := 375975099494613214865971

theorem tailTrace_823735 : CollatzResearch.WordTrace tailWord_823735 prefixEnd_823735 375975099494613214865971 := by
  unfold tailWord_823735
  simp only [CollatzResearch.WordTrace]
  refine ⟨30044083670756252582784659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20029389113837501721856439 30044083670756252582784659)
  ·
    refine ⟨45066125506134378874176989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30044083670756252582784659 45066125506134378874176989)
    ·
      refine ⟨16899797064800392077816371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45066125506134378874176989 16899797064800392077816371)
      ·
        refine ⟨25349695597200588116724557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16899797064800392077816371 25349695597200588116724557)
        ·
          refine ⟨9506135848950220543771709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25349695597200588116724557 9506135848950220543771709)
          ·
            refine ⟨3564800943356332703914391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9506135848950220543771709 3564800943356332703914391)
            ·
              refine ⟨5347201415034499055871587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3564800943356332703914391 5347201415034499055871587)
              ·
                refine ⟨8020802122551748583807381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5347201415034499055871587 8020802122551748583807381)
                ·
                  refine ⟨375975099494613214865971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8020802122551748583807381 375975099494613214865971)
                  ·
                    rfl

theorem cell20_823735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_823735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823735 prefixEnd_823735 := by exact prefixLift 823735
  have htrace : WordTrace (prefixWord ++ tailWord_823735) baseStart_823735 baseEnd_823735 := by
    simpa [prefixWord, tailWord_823735, baseEnd_823735] using wordTrace_append hprefix tailTrace_823735
  have hstable : (prefixWord ++ tailWord_823735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823735).length < 2 ^ (prefixWord ++ tailWord_823735).sum := by decide
  have hdescent : baseEnd_823735 < baseStart_823735 := by decide
  rcases family_descends (prefixWord ++ tailWord_823735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823762 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_823762 : Nat := 118140960795 + 823762 * 2 ^ 59
def prefixEnd_823762 : Nat := 4983230072969 + 3 ^ 40 * 823762 * 2
def baseEnd_823762 : Nat := 375987423030321120965861

theorem tailTrace_823762 : CollatzResearch.WordTrace tailWord_823762 prefixEnd_823762 375987423030321120965861 := by
  unfold tailWord_823762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7511267110414609048504385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20030045627772290796011693 7511267110414609048504385)
  ·
    refine ⟨5633450332810956786378289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7511267110414609048504385 5633450332810956786378289)
    ·
      refine ⟨4225087749608217589783717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5633450332810956786378289 4225087749608217589783717)
      ·
        refine ⟨792203953051540798084447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4225087749608217589783717 792203953051540798084447)
        ·
          refine ⟨1188305929577311197126671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792203953051540798084447 1188305929577311197126671)
          ·
            refine ⟨1782458894365966795690007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1188305929577311197126671 1782458894365966795690007)
            ·
              refine ⟨2673688341548950193535011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782458894365966795690007 2673688341548950193535011)
              ·
                refine ⟨4010532512323425290302517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673688341548950193535011 4010532512323425290302517)
                ·
                  refine ⟨375987423030321120965861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4010532512323425290302517 375987423030321120965861)
                  ·
                    rfl

theorem cell20_823762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_823762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823762 prefixEnd_823762 := by exact prefixLift 823762
  have htrace : WordTrace (prefixWord ++ tailWord_823762) baseStart_823762 baseEnd_823762 := by
    simpa [prefixWord, tailWord_823762, baseEnd_823762] using wordTrace_append hprefix tailTrace_823762
  have hstable : (prefixWord ++ tailWord_823762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823762).length < 2 ^ (prefixWord ++ tailWord_823762).sum := by decide
  have hdescent : baseEnd_823762 < baseStart_823762 := by decide
  rcases family_descends (prefixWord ++ tailWord_823762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823790 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_823790 : Nat := 118140960795 + 823790 * 2 ^ 59
def prefixEnd_823790 : Nat := 4983230072969 + 3 ^ 40 * 823790 * 2
def baseEnd_823790 : Nat := 376000202993277468032413

theorem tailTrace_823790 : CollatzResearch.WordTrace tailWord_823790 prefixEnd_823790 376000202993277468032413 := by
  unfold tailWord_823790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3755761210694624622004603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20030726457037997984024549 3755761210694624622004603)
  ·
    refine ⟨5633641816041936933006905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3755761210694624622004603 5633641816041936933006905)
    ·
      refine ⟨4225231362031452699755179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5633641816041936933006905 4225231362031452699755179)
      ·
        refine ⟨6337847043047179049632769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4225231362031452699755179 6337847043047179049632769)
        ·
          refine ⟨4753385282285384287224577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6337847043047179049632769 4753385282285384287224577)
          ·
            refine ⟨3565038961714038215418433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4753385282285384287224577 3565038961714038215418433)
            ·
              refine ⟨2673779221285528661563825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3565038961714038215418433 2673779221285528661563825)
              ·
                refine ⟨2005334415964146496172869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2673779221285528661563825 2005334415964146496172869)
                ·
                  refine ⟨376000202993277468032413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005334415964146496172869 376000202993277468032413)
                  ·
                    rfl

theorem cell20_823790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_823790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823790 prefixEnd_823790 := by exact prefixLift 823790
  have htrace : WordTrace (prefixWord ++ tailWord_823790) baseStart_823790 baseEnd_823790 := by
    simpa [prefixWord, tailWord_823790, baseEnd_823790] using wordTrace_append hprefix tailTrace_823790
  have hstable : (prefixWord ++ tailWord_823790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823790).length < 2 ^ (prefixWord ++ tailWord_823790).sum := by decide
  have hdescent : baseEnd_823790 < baseStart_823790 := by decide
  rcases family_descends (prefixWord ++ tailWord_823790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823856 : List Nat := [2, 1, 1, 1, 2, 3, 4, 6]
def baseStart_823856 : Nat := 118140960795 + 823856 * 2 ^ 59
def prefixEnd_823856 : Nat := 4983230072969 + 3 ^ 40 * 823856 * 2
def baseEnd_823856 : Nat := 125343442397224857277381

theorem tailTrace_823856 : CollatzResearch.WordTrace tailWord_823856 prefixEnd_823856 125343442397224857277381 := by
  unfold tailWord_823856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15024248451658945123969711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20032331268878593498626281 15024248451658945123969711)
  ·
    refine ⟨22536372677488417685954567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15024248451658945123969711 22536372677488417685954567)
    ·
      refine ⟨33804559016232626528931851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22536372677488417685954567 33804559016232626528931851)
      ·
        refine ⟨50706838524348939793397777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33804559016232626528931851 50706838524348939793397777)
        ·
          refine ⟨38030128893261704845048333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50706838524348939793397777 38030128893261704845048333)
          ·
            refine ⟨14261298334973139316893125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38030128893261704845048333 14261298334973139316893125)
            ·
              refine ⟨2673993437807463621917461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14261298334973139316893125 2673993437807463621917461)
              ·
                refine ⟨125343442397224857277381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2673993437807463621917461 125343442397224857277381)
                ·
                  rfl

theorem cell20_823856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_823856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823856 prefixEnd_823856 := by exact prefixLift 823856
  have htrace : WordTrace (prefixWord ++ tailWord_823856) baseStart_823856 baseEnd_823856 := by
    simpa [prefixWord, tailWord_823856, baseEnd_823856] using wordTrace_append hprefix tailTrace_823856
  have hstable : (prefixWord ++ tailWord_823856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823856).length < 2 ^ (prefixWord ++ tailWord_823856).sum := by decide
  have hdescent : baseEnd_823856 < baseStart_823856 := by decide
  rcases family_descends (prefixWord ++ tailWord_823856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823883 : List Nat := [1, 1, 1, 1, 3, 1, 8, 2, 2]
def baseStart_823883 : Nat := 118140960795 + 823883 * 2 ^ 59
def prefixEnd_823883 : Nat := 4983230072969 + 3 ^ 40 * 823883 * 2
def baseEnd_823883 : Nat := 376042650727382477932033

theorem tailTrace_823883 : CollatzResearch.WordTrace tailWord_823883 prefixEnd_823883 376042650727382477932033 := by
  unfold tailWord_823883
  simp only [CollatzResearch.WordTrace]
  refine ⟨30049481674220073859172303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20032987782813382572781535 30049481674220073859172303)
  ·
    refine ⟨45074222511330110788758455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30049481674220073859172303 45074222511330110788758455)
    ·
      refine ⟨67611333766995166183137683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45074222511330110788758455 67611333766995166183137683)
      ·
        refine ⟨101417000650492749274706525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67611333766995166183137683 101417000650492749274706525)
        ·
          refine ⟨38031375243934780978014947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101417000650492749274706525 38031375243934780978014947)
          ·
            refine ⟨57047062865902171467022421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38031375243934780978014947 57047062865902171467022421)
            ·
              refine ⟨668520267959791071879169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 57047062865902171467022421 668520267959791071879169)
              ·
                refine ⟨501390200969843303909377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668520267959791071879169 501390200969843303909377)
                ·
                  refine ⟨376042650727382477932033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501390200969843303909377 376042650727382477932033)
                  ·
                    rfl

theorem cell20_823883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 2].length) (baseStart_823883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823883 prefixEnd_823883 := by exact prefixLift 823883
  have htrace : WordTrace (prefixWord ++ tailWord_823883) baseStart_823883 baseEnd_823883 := by
    simpa [prefixWord, tailWord_823883, baseEnd_823883] using wordTrace_append hprefix tailTrace_823883
  have hstable : (prefixWord ++ tailWord_823883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823883).length < 2 ^ (prefixWord ++ tailWord_823883).sum := by decide
  have hdescent : baseEnd_823883 < baseStart_823883 := by decide
  rcases family_descends (prefixWord ++ tailWord_823883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823962 : List Nat := [3, 1, 1, 6, 2, 1, 2, 4]
def baseStart_823962 : Nat := 118140960795 + 823962 * 2 ^ 59
def prefixEnd_823962 : Nat := 4983230072969 + 3 ^ 40 * 823962 * 2
def baseEnd_823962 : Nat := 125359569493336438099459

theorem tailTrace_823962 : CollatzResearch.WordTrace tailWord_823962 prefixEnd_823962 125359569493336438099459 := by
  unfold tailWord_823962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513090760233467587824535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20034908693955913567532093 7513090760233467587824535)
  ·
    refine ⟨11269636140350201381736803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7513090760233467587824535 11269636140350201381736803)
    ·
      refine ⟨16904454210525302072605205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11269636140350201381736803 16904454210525302072605205)
      ·
        refine ⟨792396291118373534653369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16904454210525302072605205 792396291118373534653369)
        ·
          refine ⟨594297218338780150990027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792396291118373534653369 594297218338780150990027)
          ·
            refine ⟨891445827508170226485041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594297218338780150990027 891445827508170226485041)
            ·
              refine ⟨668584370631127669863781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891445827508170226485041 668584370631127669863781)
              ·
                refine ⟨125359569493336438099459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 668584370631127669863781 125359569493336438099459)
                ·
                  rfl

theorem cell20_823962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_823962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823962 prefixEnd_823962 := by exact prefixLift 823962
  have htrace : WordTrace (prefixWord ++ tailWord_823962) baseStart_823962 baseEnd_823962 := by
    simpa [prefixWord, tailWord_823962, baseEnd_823962] using wordTrace_append hprefix tailTrace_823962
  have hstable : (prefixWord ++ tailWord_823962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823962).length < 2 ^ (prefixWord ++ tailWord_823962).sum := by decide
  have hdescent : baseEnd_823962 < baseStart_823962 := by decide
  rcases family_descends (prefixWord ++ tailWord_823962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823977 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_823977 : Nat := 118140960795 + 823977 * 2 ^ 59
def prefixEnd_823977 : Nat := 4983230072969 + 3 ^ 40 * 823977 * 2
def baseEnd_823977 : Nat := 376085554888735928798315

theorem tailTrace_823977 : CollatzResearch.WordTrace tailWord_823977 prefixEnd_823977 376085554888735928798315 := by
  unfold tailWord_823977
  simp only [CollatzResearch.WordTrace]
  refine ⟨30052910135879527913094185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20035273423919685275396123 30052910135879527913094185)
  ·
    refine ⟨22539682601909645934820639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30052910135879527913094185 22539682601909645934820639)
    ·
      refine ⟨33809523902864468902230959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22539682601909645934820639 33809523902864468902230959)
      ·
        refine ⟨50714285854296703353346439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33809523902864468902230959 50714285854296703353346439)
        ·
          refine ⟨76071428781445055030019659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50714285854296703353346439 76071428781445055030019659)
          ·
            refine ⟨114107143172167582545029489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76071428781445055030019659 114107143172167582545029489)
            ·
              refine ⟨85580357379125686908772117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114107143172167582545029489 85580357379125686908772117)
              ·
                refine ⟨4011579252146516573848693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85580357379125686908772117 4011579252146516573848693)
                ·
                  refine ⟨376085554888735928798315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4011579252146516573848693 376085554888735928798315)
                  ·
                    rfl

theorem cell20_823977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_823977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823977 prefixEnd_823977 := by exact prefixLift 823977
  have htrace : WordTrace (prefixWord ++ tailWord_823977) baseStart_823977 baseEnd_823977 := by
    simpa [prefixWord, tailWord_823977, baseEnd_823977] using wordTrace_append hprefix tailTrace_823977
  have hstable : (prefixWord ++ tailWord_823977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823977).length < 2 ^ (prefixWord ++ tailWord_823977).sum := by decide
  have hdescent : baseEnd_823977 < baseStart_823977 := by decide
  rcases family_descends (prefixWord ++ tailWord_823977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823994 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_823994 : Nat := 118140960795 + 823994 * 2 ^ 59
def prefixEnd_823994 : Nat := 4983230072969 + 3 ^ 40 * 823994 * 2
def baseEnd_823994 : Nat := 376093314151959425231579

theorem tailTrace_823994 : CollatzResearch.WordTrace tailWord_823994 prefixEnd_823994 376093314151959425231579 := by
  unfold tailWord_823994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7513382544204484954115759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20035686784545293210975357 7513382544204484954115759)
  ·
    refine ⟨11270073816306727431173639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7513382544204484954115759 11270073816306727431173639)
    ·
      refine ⟨16905110724460091146760459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11270073816306727431173639 16905110724460091146760459)
      ·
        refine ⟨25357666086690136720140689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16905110724460091146760459 25357666086690136720140689)
        ·
          refine ⟨19018249565017602540105517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25357666086690136720140689 19018249565017602540105517)
          ·
            refine ⟨7131843586881600952539569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19018249565017602540105517 7131843586881600952539569)
            ·
              refine ⟨5348882690161200714404677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7131843586881600952539569 5348882690161200714404677)
              ·
                refine ⟨1002915504405225133950877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5348882690161200714404677 1002915504405225133950877)
                ·
                  refine ⟨376093314151959425231579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002915504405225133950877 376093314151959425231579)
                  ·
                    rfl

theorem cell20_823994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_823994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_823994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_823994 prefixEnd_823994 := by exact prefixLift 823994
  have htrace : WordTrace (prefixWord ++ tailWord_823994) baseStart_823994 baseEnd_823994 := by
    simpa [prefixWord, tailWord_823994, baseEnd_823994] using wordTrace_append hprefix tailTrace_823994
  have hstable : (prefixWord ++ tailWord_823994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823994).length < 2 ^ (prefixWord ++ tailWord_823994).sum := by decide
  have hdescent : baseEnd_823994 < baseStart_823994 := by decide
  rcases family_descends (prefixWord ++ tailWord_823994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824008 : List Nat := [2, 1, 3, 1, 2, 3, 1, 7]
def baseStart_824008 : Nat := 118140960795 + 824008 * 2 ^ 59
def prefixEnd_824008 : Nat := 4983230072969 + 3 ^ 40 * 824008 * 2
def baseEnd_824008 : Nat := 125366568044479199588285

theorem tailTrace_824008 : CollatzResearch.WordTrace tailWord_824008 prefixEnd_824008 125366568044479199588285 := by
  unfold tailWord_824008
  simp only [CollatzResearch.WordTrace]
  refine ⟨15027020399383610103736339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20036027199178146804981785 15027020399383610103736339)
  ·
    refine ⟨22540530599075415155604509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15027020399383610103736339 22540530599075415155604509)
    ·
      refine ⟨8452698974653280683351691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22540530599075415155604509 8452698974653280683351691)
      ·
        refine ⟨12679048461979921025027537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8452698974653280683351691 12679048461979921025027537)
        ·
          refine ⟨9509286346484940768770653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12679048461979921025027537 9509286346484940768770653)
          ·
            refine ⟨3565982379931852788288995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9509286346484940768770653 3565982379931852788288995)
            ·
              refine ⟨5348973569897779182433493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3565982379931852788288995 5348973569897779182433493)
              ·
                refine ⟨125366568044479199588285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5348973569897779182433493 125366568044479199588285)
                ·
                  rfl

theorem cell20_824008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_824008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824008 prefixEnd_824008 := by exact prefixLift 824008
  have htrace : WordTrace (prefixWord ++ tailWord_824008) baseStart_824008 baseEnd_824008 := by
    simpa [prefixWord, tailWord_824008, baseEnd_824008] using wordTrace_append hprefix tailTrace_824008
  have hstable : (prefixWord ++ tailWord_824008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824008).length < 2 ^ (prefixWord ++ tailWord_824008).sum := by decide
  have hdescent : baseEnd_824008 < baseStart_824008 := by decide
  rcases family_descends (prefixWord ++ tailWord_824008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824046 : List Nat := [4, 1, 2, 1, 1, 11]
def baseStart_824046 : Nat := 118140960795 + 824046 * 2 ^ 59
def prefixEnd_824046 : Nat := 4983230072969 + 3 ^ 40 * 824046 * 2
def baseEnd_824046 : Nat := 13930261050699198351779

theorem tailTrace_824046 : CollatzResearch.WordTrace tailWord_824046 prefixEnd_824046 13930261050699198351779 := by
  unfold tailWord_824046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3756928346578694087169499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20036951181753035131570661 3756928346578694087169499)
  ·
    refine ⟨5635392519868041130754249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3756928346578694087169499 5635392519868041130754249)
    ·
      refine ⟨4226544389901030848065687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5635392519868041130754249 4226544389901030848065687)
      ·
        refine ⟨6339816584851546272098531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226544389901030848065687 6339816584851546272098531)
        ·
          refine ⟨9509724877277319408147797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6339816584851546272098531 9509724877277319408147797)
          ·
            refine ⟨13930261050699198351779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9509724877277319408147797 13930261050699198351779)
            ·
              rfl

theorem cell20_824046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 11].length) (baseStart_824046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824046 prefixEnd_824046 := by exact prefixLift 824046
  have htrace : WordTrace (prefixWord ++ tailWord_824046) baseStart_824046 baseEnd_824046 := by
    simpa [prefixWord, tailWord_824046, baseEnd_824046] using wordTrace_append hprefix tailTrace_824046
  have hstable : (prefixWord ++ tailWord_824046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824046).length < 2 ^ (prefixWord ++ tailWord_824046).sum := by decide
  have hdescent : baseEnd_824046 < baseStart_824046 := by decide
  rcases family_descends (prefixWord ++ tailWord_824046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824056 : List Nat := [2, 1, 2, 1, 1, 2, 5, 4, 2]
def baseStart_824056 : Nat := 118140960795 + 824056 * 2 ^ 59
def prefixEnd_824056 : Nat := 4983230072969 + 3 ^ 40 * 824056 * 2
def baseEnd_824056 : Nat := 376121612641362765164659

theorem tailTrace_824056 : CollatzResearch.WordTrace tailWord_824056 prefixEnd_824056 376121612641362765164659 := by
  unfold tailWord_824056
  simp only [CollatzResearch.WordTrace]
  refine ⟨15027895751296662202610011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20037194335062216270146681 15027895751296662202610011)
  ·
    refine ⟨22541843626944993303915017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15027895751296662202610011 22541843626944993303915017)
    ·
      refine ⟨16906382720208744977936263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22541843626944993303915017 16906382720208744977936263)
      ·
        refine ⟨25359574080313117466904395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16906382720208744977936263 25359574080313117466904395)
        ·
          refine ⟨38039361120469676200356593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25359574080313117466904395 38039361120469676200356593)
          ·
            refine ⟨28529520840352257150267445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38039361120469676200356593 28529520840352257150267445)
            ·
              refine ⟨2674642578783024107837573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28529520840352257150267445 2674642578783024107837573)
              ·
                refine ⟨501495483521817020219545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2674642578783024107837573 501495483521817020219545)
                ·
                  refine ⟨376121612641362765164659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501495483521817020219545 376121612641362765164659)
                  ·
                    rfl

theorem cell20_824056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_824056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824056 prefixEnd_824056 := by exact prefixLift 824056
  have htrace : WordTrace (prefixWord ++ tailWord_824056) baseStart_824056 baseEnd_824056 := by
    simpa [prefixWord, tailWord_824056, baseEnd_824056] using wordTrace_append hprefix tailTrace_824056
  have hstable : (prefixWord ++ tailWord_824056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824056).length < 2 ^ (prefixWord ++ tailWord_824056).sum := by decide
  have hdescent : baseEnd_824056 < baseStart_824056 := by decide
  rcases family_descends (prefixWord ++ tailWord_824056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824115 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_824115 : Nat := 118140960795 + 824115 * 2 ^ 59
def prefixEnd_824115 : Nat := 4983230072969 + 3 ^ 40 * 824115 * 2
def baseEnd_824115 : Nat := 376148541849020782197751

theorem tailTrace_824115 : CollatzResearch.WordTrace tailWord_824115 prefixEnd_824115 376148541849020782197751 := by
  unfold tailWord_824115
  simp only [CollatzResearch.WordTrace]
  refine ⟨30057943409379577481617799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20038628939586384987745199 30057943409379577481617799)
  ·
    refine ⟨45086915114069366222426699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30057943409379577481617799 45086915114069366222426699)
    ·
      refine ⟨67630372671104049333640049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45086915114069366222426699 67630372671104049333640049)
      ·
        refine ⟨50722779503328037000230037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67630372671104049333640049 50722779503328037000230037)
        ·
          refine ⟨2377630289218501734385783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50722779503328037000230037 2377630289218501734385783)
          ·
            refine ⟨3566445433827752601578675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2377630289218501734385783 3566445433827752601578675)
            ·
              refine ⟨5349668150741628902368013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3566445433827752601578675 5349668150741628902368013)
              ·
                refine ⟨2006125556528110838388005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5349668150741628902368013 2006125556528110838388005)
                ·
                  refine ⟨376148541849020782197751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006125556528110838388005 376148541849020782197751)
                  ·
                    rfl

theorem cell20_824115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_824115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824115 prefixEnd_824115 := by exact prefixLift 824115
  have htrace : WordTrace (prefixWord ++ tailWord_824115) baseStart_824115 baseEnd_824115 := by
    simpa [prefixWord, tailWord_824115, baseEnd_824115] using wordTrace_append hprefix tailTrace_824115
  have hstable : (prefixWord ++ tailWord_824115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824115).length < 2 ^ (prefixWord ++ tailWord_824115).sum := by decide
  have hdescent : baseEnd_824115 < baseStart_824115 := by decide
  rcases family_descends (prefixWord ++ tailWord_824115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824225 : List Nat := [1, 2, 3, 4, 1, 2, 1, 4, 2]
def baseStart_824225 : Nat := 118140960795 + 824225 * 2 ^ 59
def prefixEnd_824225 : Nat := 4983230072969 + 3 ^ 40 * 824225 * 2
def baseEnd_824225 : Nat := 376198748846349288530635

theorem tailTrace_824225 : CollatzResearch.WordTrace tailWord_824225 prefixEnd_824225 376198748846349288530635 := by
  unfold tailWord_824225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30061955438981066268122129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20041303625987377512081419 30061955438981066268122129)
  ·
    refine ⟨22546466579235799701091597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30061955438981066268122129 22546466579235799701091597)
    ·
      refine ⟨8454924967213424887909349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22546466579235799701091597 8454924967213424887909349)
      ·
        refine ⟨1585298431352517166483003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8454924967213424887909349 1585298431352517166483003)
        ·
          refine ⟨2377947647028775749724505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1585298431352517166483003 2377947647028775749724505)
          ·
            refine ⟨1783460735271581812293379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2377947647028775749724505 1783460735271581812293379)
            ·
              refine ⟨2675191102907372718440069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783460735271581812293379 2675191102907372718440069)
              ·
                refine ⟨501598331795132384707513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2675191102907372718440069 501598331795132384707513)
                ·
                  refine ⟨376198748846349288530635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501598331795132384707513 376198748846349288530635)
                  ·
                    rfl

theorem cell20_824225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 2].length) (baseStart_824225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824225 prefixEnd_824225 := by exact prefixLift 824225
  have htrace : WordTrace (prefixWord ++ tailWord_824225) baseStart_824225 baseEnd_824225 := by
    simpa [prefixWord, tailWord_824225, baseEnd_824225] using wordTrace_append hprefix tailTrace_824225
  have hstable : (prefixWord ++ tailWord_824225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824225).length < 2 ^ (prefixWord ++ tailWord_824225).sum := by decide
  have hdescent : baseEnd_824225 < baseStart_824225 := by decide
  rcases family_descends (prefixWord ++ tailWord_824225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824269 : List Nat := [1, 6, 3, 1, 2, 1, 1, 2, 3]
def baseStart_824269 : Nat := 118140960795 + 824269 * 2 ^ 59
def prefixEnd_824269 : Nat := 4983230072969 + 3 ^ 40 * 824269 * 2
def baseEnd_824269 : Nat := 376218831645280691063789

theorem tailTrace_824269 : CollatzResearch.WordTrace tailWord_824269 prefixEnd_824269 376218831645280691063789 := by
  unfold tailWord_824269
  simp only [CollatzResearch.WordTrace]
  refine ⟨30063560250821661782723861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20042373500547774521815907 30063560250821661782723861)
  ·
    refine ⟨1409229386757265396065181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30063560250821661782723861 1409229386757265396065181)
    ·
      refine ⟨528461020033974523524443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1409229386757265396065181 528461020033974523524443)
      ·
        refine ⟨792691530050961785286665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528461020033974523524443 792691530050961785286665)
        ·
          refine ⟨594518647538221338964999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792691530050961785286665 594518647538221338964999)
          ·
            refine ⟨891777971307332008447499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594518647538221338964999 891777971307332008447499)
            ·
              refine ⟨1337666956960998012671249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891777971307332008447499 1337666956960998012671249)
              ·
                refine ⟨1003250217720748509503437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337666956960998012671249 1003250217720748509503437)
                ·
                  refine ⟨376218831645280691063789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003250217720748509503437 376218831645280691063789)
                  ·
                    rfl

theorem cell20_824269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_824269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824269 prefixEnd_824269 := by exact prefixLift 824269
  have htrace : WordTrace (prefixWord ++ tailWord_824269) baseStart_824269 baseEnd_824269 := by
    simpa [prefixWord, tailWord_824269, baseEnd_824269] using wordTrace_append hprefix tailTrace_824269
  have hstable : (prefixWord ++ tailWord_824269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824269).length < 2 ^ (prefixWord ++ tailWord_824269).sum := by decide
  have hdescent : baseEnd_824269 < baseStart_824269 := by decide
  rcases family_descends (prefixWord ++ tailWord_824269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824305 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_824305 : Nat := 118140960795 + 824305 * 2 ^ 59
def prefixEnd_824305 : Nat := 4983230072969 + 3 ^ 40 * 824305 * 2
def baseEnd_824305 : Nat := 376235263026224565863641

theorem tailTrace_824305 : CollatzResearch.WordTrace tailWord_824305 prefixEnd_824305 376235263026224565863641 := by
  unfold tailWord_824305
  simp only [CollatzResearch.WordTrace]
  refine ⟨30064873278691239931034369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20043248852460826620689579 30064873278691239931034369)
  ·
    refine ⟨22548654959018429948275777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30064873278691239931034369 22548654959018429948275777)
    ·
      refine ⟨16911491219263822461206833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22548654959018429948275777 16911491219263822461206833)
      ·
        refine ⟨12683618414447866845905125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16911491219263822461206833 12683618414447866845905125)
        ·
          refine ⟨2378178452708975033607211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12683618414447866845905125 2378178452708975033607211)
          ·
            refine ⟨3567267679063462550410817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378178452708975033607211 3567267679063462550410817)
            ·
              refine ⟨2675450759297596912808113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3567267679063462550410817 2675450759297596912808113)
              ·
                refine ⟨2006588069473197684606085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675450759297596912808113 2006588069473197684606085)
                ·
                  refine ⟨376235263026224565863641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006588069473197684606085 376235263026224565863641)
                  ·
                    rfl

theorem cell20_824305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_824305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824305 prefixEnd_824305 := by exact prefixLift 824305
  have htrace : WordTrace (prefixWord ++ tailWord_824305) baseStart_824305 baseEnd_824305 := by
    simpa [prefixWord, tailWord_824305, baseEnd_824305] using wordTrace_append hprefix tailTrace_824305
  have hstable : (prefixWord ++ tailWord_824305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824305).length < 2 ^ (prefixWord ++ tailWord_824305).sum := by decide
  have hdescent : baseEnd_824305 < baseStart_824305 := by decide
  rcases family_descends (prefixWord ++ tailWord_824305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824349 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 3]
def baseStart_824349 : Nat := 118140960795 + 824349 * 2 ^ 59
def prefixEnd_824349 : Nat := 4983230072969 + 3 ^ 40 * 824349 * 2
def baseEnd_824349 : Nat := 376255345825155968396795

theorem tailTrace_824349 : CollatzResearch.WordTrace tailWord_824349 prefixEnd_824349 376255345825155968396795 := by
  unfold tailWord_824349
  simp only [CollatzResearch.WordTrace]
  refine ⟨30066478090531835445636101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20044318727021223630424067 30066478090531835445636101)
  ·
    refine ⟨5637464641974719146056769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30066478090531835445636101 5637464641974719146056769)
    ·
      refine ⟨4228098481481039359542577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5637464641974719146056769 4228098481481039359542577)
      ·
        refine ⟨3171073861110779519656933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4228098481481039359542577 3171073861110779519656933)
        ·
          refine ⟨594576348958271159935675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3171073861110779519656933 594576348958271159935675)
          ·
            refine ⟨891864523437406739903513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594576348958271159935675 891864523437406739903513)
            ·
              refine ⟨668898392578055054927635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891864523437406739903513 668898392578055054927635)
              ·
                refine ⟨1003347588867082582391453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668898392578055054927635 1003347588867082582391453)
                ·
                  refine ⟨376255345825155968396795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003347588867082582391453 376255345825155968396795)
                  ·
                    rfl

theorem cell20_824349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_824349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824349 prefixEnd_824349 := by exact prefixLift 824349
  have htrace : WordTrace (prefixWord ++ tailWord_824349) baseStart_824349 baseEnd_824349 := by
    simpa [prefixWord, tailWord_824349, baseEnd_824349] using wordTrace_append hprefix tailTrace_824349
  have hstable : (prefixWord ++ tailWord_824349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824349).length < 2 ^ (prefixWord ++ tailWord_824349).sum := by decide
  have hdescent : baseEnd_824349 < baseStart_824349 := by decide
  rcases family_descends (prefixWord ++ tailWord_824349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824353 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 3]
def baseStart_824353 : Nat := 118140960795 + 824353 * 2 ^ 59
def prefixEnd_824353 : Nat := 4983230072969 + 3 ^ 40 * 824353 * 2
def baseEnd_824353 : Nat := 376257171534149732263445

theorem tailTrace_824353 : CollatzResearch.WordTrace tailWord_824353 prefixEnd_824353 376257171534149732263445 := by
  unfold tailWord_824353
  simp only [CollatzResearch.WordTrace]
  refine ⟨30066623982517344128781713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20044415988344896085854475 30066623982517344128781713)
  ·
    refine ⟨22549967986888008096586285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30066623982517344128781713 22549967986888008096586285)
    ·
      refine ⟨8456237995083003036219857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22549967986888008096586285 8456237995083003036219857)
      ·
        refine ⟨6342178496312252277164893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8456237995083003036219857 6342178496312252277164893)
        ·
          refine ⟨2378316936117094603936835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6342178496312252277164893 2378316936117094603936835)
          ·
            refine ⟨3567475404175641905905253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2378316936117094603936835 3567475404175641905905253)
            ·
              refine ⟨668901638282932857357235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3567475404175641905905253 668901638282932857357235)
              ·
                refine ⟨1003352457424399286035853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668901638282932857357235 1003352457424399286035853)
                ·
                  refine ⟨376257171534149732263445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003352457424399286035853 376257171534149732263445)
                  ·
                    rfl

theorem cell20_824353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_824353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824353 prefixEnd_824353 := by exact prefixLift 824353
  have htrace : WordTrace (prefixWord ++ tailWord_824353) baseStart_824353 baseEnd_824353 := by
    simpa [prefixWord, tailWord_824353, baseEnd_824353] using wordTrace_append hprefix tailTrace_824353
  have hstable : (prefixWord ++ tailWord_824353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824353).length < 2 ^ (prefixWord ++ tailWord_824353).sum := by decide
  have hdescent : baseEnd_824353 < baseStart_824353 := by decide
  rcases family_descends (prefixWord ++ tailWord_824353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824364 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_824364 : Nat := 118140960795 + 824364 * 2 ^ 59
def prefixEnd_824364 : Nat := 4983230072969 + 3 ^ 40 * 824364 * 2
def baseEnd_824364 : Nat := 376262192233882582896733

theorem tailTrace_824364 : CollatzResearch.WordTrace tailWord_824364 prefixEnd_824364 376262192233882582896733 := by
  unfold tailWord_824364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15033512592738746503716073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20044683456984995338288097 15033512592738746503716073)
  ·
    refine ⟨11275134444554059877787055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15033512592738746503716073 11275134444554059877787055)
    ·
      refine ⟨16912701666831089816680583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11275134444554059877787055 16912701666831089816680583)
      ·
        refine ⟨25369052500246634725020875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16912701666831089816680583 25369052500246634725020875)
        ·
          refine ⟨38053578750369952087531313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25369052500246634725020875 38053578750369952087531313)
          ·
            refine ⟨28540184062777464065648485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38053578750369952087531313 28540184062777464065648485)
            ·
              refine ⟨5351284511770774512309091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28540184062777464065648485 5351284511770774512309091)
              ·
                refine ⟨8026926767656161768463637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351284511770774512309091 8026926767656161768463637)
                ·
                  refine ⟨376262192233882582896733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8026926767656161768463637 376262192233882582896733)
                  ·
                    rfl

theorem cell20_824364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_824364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824364 prefixEnd_824364 := by exact prefixLift 824364
  have htrace : WordTrace (prefixWord ++ tailWord_824364) baseStart_824364 baseEnd_824364 := by
    simpa [prefixWord, tailWord_824364, baseEnd_824364] using wordTrace_append hprefix tailTrace_824364
  have hstable : (prefixWord ++ tailWord_824364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824364).length < 2 ^ (prefixWord ++ tailWord_824364).sum := by decide
  have hdescent : baseEnd_824364 < baseStart_824364 := by decide
  rcases family_descends (prefixWord ++ tailWord_824364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824398 : List Nat := [4, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_824398 : Nat := 118140960795 + 824398 * 2 ^ 59
def prefixEnd_824398 : Nat := 4983230072969 + 3 ^ 40 * 824398 * 2
def baseEnd_824398 : Nat := 376277710760329575763261

theorem tailTrace_824398 : CollatzResearch.WordTrace tailWord_824398 prefixEnd_824398 376277710760329575763261 := by
  unfold tailWord_824398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3758533158419289601771231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20045510178236211209446565 3758533158419289601771231)
  ·
    refine ⟨5637799737628934402656847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3758533158419289601771231 5637799737628934402656847)
    ·
      refine ⟨8456699606443401603985271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5637799737628934402656847 8456699606443401603985271)
      ·
        refine ⟨12685049409665102405977907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8456699606443401603985271 12685049409665102405977907)
        ·
          refine ⟨19027574114497653608966861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685049409665102405977907 19027574114497653608966861)
          ·
            refine ⟨7135340292936620103362573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19027574114497653608966861 7135340292936620103362573)
            ·
              refine ⟨2675752609851232538760965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7135340292936620103362573 2675752609851232538760965)
              ·
                refine ⟨501703614347106101017681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2675752609851232538760965 501703614347106101017681)
                ·
                  refine ⟨376277710760329575763261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501703614347106101017681 376277710760329575763261)
                  ·
                    rfl

theorem cell20_824398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_824398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824398 prefixEnd_824398 := by exact prefixLift 824398
  have htrace : WordTrace (prefixWord ++ tailWord_824398) baseStart_824398 baseEnd_824398 := by
    simpa [prefixWord, tailWord_824398, baseEnd_824398] using wordTrace_append hprefix tailTrace_824398
  have hstable : (prefixWord ++ tailWord_824398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824398).length < 2 ^ (prefixWord ++ tailWord_824398).sum := by decide
  have hdescent : baseEnd_824398 < baseStart_824398 := by decide
  rcases family_descends (prefixWord ++ tailWord_824398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824409 : List Nat := [1, 2, 1, 2, 2, 1, 2, 9]
def baseStart_824409 : Nat := 118140960795 + 824409 * 2 ^ 59
def prefixEnd_824409 : Nat := 4983230072969 + 3 ^ 40 * 824409 * 2
def baseEnd_824409 : Nat := 125427577153354142132183

theorem tailTrace_824409 : CollatzResearch.WordTrace tailWord_824409 prefixEnd_824409 125427577153354142132183 := by
  unfold tailWord_824409
  simp only [CollatzResearch.WordTrace]
  refine ⟨30068666470314465692820281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20045777646876310461880187 30068666470314465692820281)
  ·
    refine ⟨22551499852735849269615211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30068666470314465692820281 22551499852735849269615211)
    ·
      refine ⟨33827249779103773904422817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22551499852735849269615211 33827249779103773904422817)
      ·
        refine ⟨25370437334327830428317113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33827249779103773904422817 25370437334327830428317113)
        ·
          refine ⟨19027828000745872821237835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25370437334327830428317113 19027828000745872821237835)
          ·
            refine ⟨28541742001118809231856753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19027828000745872821237835 28541742001118809231856753)
            ·
              refine ⟨21406306500839106923892565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28541742001118809231856753 21406306500839106923892565)
              ·
                refine ⟨125427577153354142132183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21406306500839106923892565 125427577153354142132183)
                ·
                  rfl

theorem cell20_824409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_824409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824409 prefixEnd_824409 := by exact prefixLift 824409
  have htrace : WordTrace (prefixWord ++ tailWord_824409) baseStart_824409 baseEnd_824409 := by
    simpa [prefixWord, tailWord_824409, baseEnd_824409] using wordTrace_append hprefix tailTrace_824409
  have hstable : (prefixWord ++ tailWord_824409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824409).length < 2 ^ (prefixWord ++ tailWord_824409).sum := by decide
  have hdescent : baseEnd_824409 < baseStart_824409 := by decide
  rcases family_descends (prefixWord ++ tailWord_824409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824412 : List Nat := [2, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_824412 : Nat := 118140960795 + 824412 * 2 ^ 59
def prefixEnd_824412 : Nat := 4983230072969 + 3 ^ 40 * 824412 * 2
def baseEnd_824412 : Nat := 376284100741807749296537

theorem tailTrace_824412 : CollatzResearch.WordTrace tailWord_824412 prefixEnd_824412 376284100741807749296537 := by
  unfold tailWord_824412
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034387944651798602589745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20045850592869064803452993 15034387944651798602589745)
  ·
    refine ⟨11275790958488848951942309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15034387944651798602589745 11275790958488848951942309)
    ·
      refine ⟨2114210804716659178489183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11275790958488848951942309 2114210804716659178489183)
      ·
        refine ⟨3171316207074988767733775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114210804716659178489183 3171316207074988767733775)
        ·
          refine ⟨4756974310612483151600663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171316207074988767733775 4756974310612483151600663)
          ·
            refine ⟨7135461465918724727400995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4756974310612483151600663 7135461465918724727400995)
            ·
              refine ⟨10703192198878087091101493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135461465918724727400995 10703192198878087091101493)
              ·
                refine ⟨1003424268644820664790765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10703192198878087091101493 1003424268644820664790765)
                ·
                  refine ⟨376284100741807749296537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003424268644820664790765 376284100741807749296537)
                  ·
                    rfl

theorem cell20_824412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_824412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824412 prefixEnd_824412 := by exact prefixLift 824412
  have htrace : WordTrace (prefixWord ++ tailWord_824412) baseStart_824412 baseEnd_824412 := by
    simpa [prefixWord, tailWord_824412, baseEnd_824412] using wordTrace_append hprefix tailTrace_824412
  have hstable : (prefixWord ++ tailWord_824412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824412).length < 2 ^ (prefixWord ++ tailWord_824412).sum := by decide
  have hdescent : baseEnd_824412 < baseStart_824412 := by decide
  rcases family_descends (prefixWord ++ tailWord_824412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824457 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_824457 : Nat := 118140960795 + 824457 * 2 ^ 59
def prefixEnd_824457 : Nat := 4983230072969 + 3 ^ 40 * 824457 * 2
def baseEnd_824457 : Nat := 376304639967987592796353

theorem tailTrace_824457 : CollatzResearch.WordTrace tailWord_824457 prefixEnd_824457 376304639967987592796353 := by
  unfold tailWord_824457
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070417174140569890567625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20046944782760379927045083 30070417174140569890567625)
  ·
    refine ⟨22552812880605427417925719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30070417174140569890567625 22552812880605427417925719)
    ·
      refine ⟨33829219320908141126888579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22552812880605427417925719 33829219320908141126888579)
      ·
        refine ⟨50743828981362211690332869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33829219320908141126888579 50743828981362211690332869)
        ·
          refine ⟨9514467934005414691937413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50743828981362211690332869 9514467934005414691937413)
          ·
            refine ⟨1783962737626015254738265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9514467934005414691937413 1783962737626015254738265)
            ·
              refine ⟨1337972053219511441053699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1783962737626015254738265 1337972053219511441053699)
              ·
                refine ⟨2006958079829267161580549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337972053219511441053699 2006958079829267161580549)
                ·
                  refine ⟨376304639967987592796353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2006958079829267161580549 376304639967987592796353)
                  ·
                    rfl

theorem cell20_824457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_824457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824457 prefixEnd_824457 := by exact prefixLift 824457
  have htrace : WordTrace (prefixWord ++ tailWord_824457) baseStart_824457 baseEnd_824457 := by
    simpa [prefixWord, tailWord_824457, baseEnd_824457] using wordTrace_append hprefix tailTrace_824457
  have hstable : (prefixWord ++ tailWord_824457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824457).length < 2 ^ (prefixWord ++ tailWord_824457).sum := by decide
  have hdescent : baseEnd_824457 < baseStart_824457 := by decide
  rcases family_descends (prefixWord ++ tailWord_824457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824509 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_824509 : Nat := 118140960795 + 824509 * 2 ^ 59
def prefixEnd_824509 : Nat := 4983230072969 + 3 ^ 40 * 824509 * 2
def baseEnd_824509 : Nat := 376328374184906523062807

theorem tailTrace_824509 : CollatzResearch.WordTrace tailWord_824509 prefixEnd_824509 376328374184906523062807 := by
  unfold tailWord_824509
  simp only [CollatzResearch.WordTrace]
  refine ⟨30072313769952182771460581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20048209179968121847640387 30072313769952182771460581)
  ·
    refine ⟨5638558831866034269648859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30072313769952182771460581 5638558831866034269648859)
    ·
      refine ⟨8457838247799051404473289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638558831866034269648859 8457838247799051404473289)
      ·
        refine ⟨6343378685849288553354967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8457838247799051404473289 6343378685849288553354967)
        ·
          refine ⟨9515068028773932830032451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6343378685849288553354967 9515068028773932830032451)
          ·
            refine ⟨14272602043160899245048677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9515068028773932830032451 14272602043160899245048677)
            ·
              refine ⟨2676112883092668608446627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14272602043160899245048677 2676112883092668608446627)
              ·
                refine ⟨4014169324639002912669941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2676112883092668608446627 4014169324639002912669941)
                ·
                  refine ⟨376328374184906523062807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4014169324639002912669941 376328374184906523062807)
                  ·
                    rfl

theorem cell20_824509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_824509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824509 prefixEnd_824509 := by exact prefixLift 824509
  have htrace : WordTrace (prefixWord ++ tailWord_824509) baseStart_824509 baseEnd_824509 := by
    simpa [prefixWord, tailWord_824509, baseEnd_824509] using wordTrace_append hprefix tailTrace_824509
  have hstable : (prefixWord ++ tailWord_824509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824509).length < 2 ^ (prefixWord ++ tailWord_824509).sum := by decide
  have hdescent : baseEnd_824509 < baseStart_824509 := by decide
  rcases family_descends (prefixWord ++ tailWord_824509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824512 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_824512 : Nat := 118140960795 + 824512 * 2 ^ 59
def prefixEnd_824512 : Nat := 4983230072969 + 3 ^ 40 * 824512 * 2
def baseEnd_824512 : Nat := 376329743466651845962795

theorem tailTrace_824512 : CollatzResearch.WordTrace tailWord_824512 prefixEnd_824512 376329743466651845962795 := by
  unfold tailWord_824512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15036211594470657141909895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20048282125960876189213193 15036211594470657141909895)
  ·
    refine ⟨22554317391705985712864843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15036211594470657141909895 22554317391705985712864843)
    ·
      refine ⟨33831476087558978569297265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22554317391705985712864843 33831476087558978569297265)
      ·
        refine ⟨25373607065669233926972949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33831476087558978569297265 25373607065669233926972949)
        ·
          refine ⟨1189387831203245340326857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25373607065669233926972949 1189387831203245340326857)
          ·
            refine ⟨892040873402434005245143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189387831203245340326857 892040873402434005245143)
            ·
              refine ⟨1338061310103651007867715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892040873402434005245143 1338061310103651007867715)
              ·
                refine ⟨2007091965155476511801573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338061310103651007867715 2007091965155476511801573)
                ·
                  refine ⟨376329743466651845962795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2007091965155476511801573 376329743466651845962795)
                  ·
                    rfl

theorem cell20_824512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_824512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824512 prefixEnd_824512 := by exact prefixLift 824512
  have htrace : WordTrace (prefixWord ++ tailWord_824512) baseStart_824512 baseEnd_824512 := by
    simpa [prefixWord, tailWord_824512, baseEnd_824512] using wordTrace_append hprefix tailTrace_824512
  have hstable : (prefixWord ++ tailWord_824512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824512).length < 2 ^ (prefixWord ++ tailWord_824512).sum := by decide
  have hdescent : baseEnd_824512 < baseStart_824512 := by decide
  rcases family_descends (prefixWord ++ tailWord_824512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824585 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 3]
def baseStart_824585 : Nat := 118140960795 + 824585 * 2 ^ 59
def prefixEnd_824585 : Nat := 4983230072969 + 3 ^ 40 * 824585 * 2
def baseEnd_824585 : Nat := 376363062655788036529163

theorem tailTrace_824585 : CollatzResearch.WordTrace tailWord_824585 prefixEnd_824585 376363062655788036529163 := by
  unfold tailWord_824585
  simp only [CollatzResearch.WordTrace]
  refine ⟨30075085717676847751227209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20050057145117898500818139 30075085717676847751227209)
  ·
    refine ⟨22556314288257635813420407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30075085717676847751227209 22556314288257635813420407)
    ·
      refine ⟨33834471432386453720130611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22556314288257635813420407 33834471432386453720130611)
      ·
        refine ⟨50751707148579680580195917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33834471432386453720130611 50751707148579680580195917)
        ·
          refine ⟨19031890180717380217573469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50751707148579680580195917 19031890180717380217573469)
          ·
            refine ⟨7136958817769017581590051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19031890180717380217573469 7136958817769017581590051)
            ·
              refine ⟨10705438226653526372385077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136958817769017581590051 10705438226653526372385077)
              ·
                refine ⟨1003634833748768097411101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10705438226653526372385077 1003634833748768097411101)
                ·
                  refine ⟨376363062655788036529163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003634833748768097411101 376363062655788036529163)
                  ·
                    rfl

theorem cell20_824585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3].length) (baseStart_824585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824585 prefixEnd_824585 := by exact prefixLift 824585
  have htrace : WordTrace (prefixWord ++ tailWord_824585) baseStart_824585 baseEnd_824585 := by
    simpa [prefixWord, tailWord_824585, baseEnd_824585] using wordTrace_append hprefix tailTrace_824585
  have hstable : (prefixWord ++ tailWord_824585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824585).length < 2 ^ (prefixWord ++ tailWord_824585).sum := by decide
  have hdescent : baseEnd_824585 < baseStart_824585 := by decide
  rcases family_descends (prefixWord ++ tailWord_824585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824605 : List Nat := [1, 4, 2, 3, 1, 2, 2, 3, 2]
def baseStart_824605 : Nat := 118140960795 + 824605 * 2 ^ 59
def prefixEnd_824605 : Nat := 4983230072969 + 3 ^ 40 * 824605 * 2
def baseEnd_824605 : Nat := 376372191200756855862415

theorem tailTrace_824605 : CollatzResearch.WordTrace tailWord_824605 prefixEnd_824605 376372191200756855862415 := by
  unfold tailWord_824605
  simp only [CollatzResearch.WordTrace]
  refine ⟨30075815177604391166955269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20050543451736260777970179 30075815177604391166955269)
  ·
    refine ⟨5639215345800823343804113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30075815177604391166955269 5639215345800823343804113)
    ·
      refine ⟨4229411509350617507853085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5639215345800823343804113 4229411509350617507853085)
      ·
        refine ⟨1586029316006481565444907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4229411509350617507853085 1586029316006481565444907)
        ·
          refine ⟨2379043974009722348167361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586029316006481565444907 2379043974009722348167361)
          ·
            refine ⟨1784282980507291761125521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379043974009722348167361 1784282980507291761125521)
            ·
              refine ⟨1338212235380468820844141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784282980507291761125521 1338212235380468820844141)
              ·
                refine ⟨501829588267675807816553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338212235380468820844141 501829588267675807816553)
                ·
                  refine ⟨376372191200756855862415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501829588267675807816553 376372191200756855862415)
                  ·
                    rfl

theorem cell20_824605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_824605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824605 prefixEnd_824605 := by exact prefixLift 824605
  have htrace : WordTrace (prefixWord ++ tailWord_824605) baseStart_824605 baseEnd_824605 := by
    simpa [prefixWord, tailWord_824605, baseEnd_824605] using wordTrace_append hprefix tailTrace_824605
  have hstable : (prefixWord ++ tailWord_824605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824605).length < 2 ^ (prefixWord ++ tailWord_824605).sum := by decide
  have hdescent : baseEnd_824605 < baseStart_824605 := by decide
  rcases family_descends (prefixWord ++ tailWord_824605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824616 : List Nat := [2, 1, 5, 1, 2, 2, 7]
def baseStart_824616 : Nat := 118140960795 + 824616 * 2 ^ 59
def prefixEnd_824616 : Nat := 4983230072969 + 3 ^ 40 * 824616 * 2
def baseEnd_824616 : Nat := 41819690211165522943967

theorem tailTrace_824616 : CollatzResearch.WordTrace tailWord_824616 prefixEnd_824616 41819690211165522943967 := by
  unfold tailWord_824616
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038108190282270022802851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20050810920376360030403801 15038108190282270022802851)
  ·
    refine ⟨22557162285423405034204277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15038108190282270022802851 22557162285423405034204277)
    ·
      refine ⟨2114733964258444221956651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22557162285423405034204277 2114733964258444221956651)
      ·
        refine ⟨3172100946387666332934977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114733964258444221956651 3172100946387666332934977)
        ·
          refine ⟨2379075709790749749701233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3172100946387666332934977 2379075709790749749701233)
          ·
            refine ⟨1784306782343062312275925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2379075709790749749701233 1784306782343062312275925)
            ·
              refine ⟨41819690211165522943967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1784306782343062312275925 41819690211165522943967)
              ·
                rfl

theorem cell20_824616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 7].length) (baseStart_824616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824616 prefixEnd_824616 := by exact prefixLift 824616
  have htrace : WordTrace (prefixWord ++ tailWord_824616) baseStart_824616 baseEnd_824616 := by
    simpa [prefixWord, tailWord_824616, baseEnd_824616] using wordTrace_append hprefix tailTrace_824616
  have hstable : (prefixWord ++ tailWord_824616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824616).length < 2 ^ (prefixWord ++ tailWord_824616).sum := by decide
  have hdescent : baseEnd_824616 < baseStart_824616 := by decide
  rcases family_descends (prefixWord ++ tailWord_824616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824626 : List Nat := [3, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_824626 : Nat := 118140960795 + 824626 * 2 ^ 59
def prefixEnd_824626 : Nat := 4983230072969 + 3 ^ 40 * 824626 * 2
def baseEnd_824626 : Nat := 376381776172974116162329

theorem tailTrace_824626 : CollatzResearch.WordTrace tailWord_824626 prefixEnd_824626 376381776172974116162329 := by
  unfold tailWord_824626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519145277632077938367433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20051054073685541168979821 7519145277632077938367433)
  ·
    refine ⟨5639358958224058453775575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7519145277632077938367433 5639358958224058453775575)
    ·
      refine ⟨8459038437336087680663363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5639358958224058453775575 8459038437336087680663363)
      ·
        refine ⟨12688557656004131520995045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8459038437336087680663363 12688557656004131520995045)
        ·
          refine ⟨2379104560500774660186571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12688557656004131520995045 2379104560500774660186571)
          ·
            refine ⟨3568656840751161990279857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379104560500774660186571 3568656840751161990279857)
            ·
              refine ⟨2676492630563371492709893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568656840751161990279857 2676492630563371492709893)
              ·
                refine ⟨501842368230632154883105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2676492630563371492709893 501842368230632154883105)
                ·
                  refine ⟨376381776172974116162329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501842368230632154883105 376381776172974116162329)
                  ·
                    rfl

theorem cell20_824626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_824626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824626 prefixEnd_824626 := by exact prefixLift 824626
  have htrace : WordTrace (prefixWord ++ tailWord_824626) baseStart_824626 baseEnd_824626 := by
    simpa [prefixWord, tailWord_824626, baseEnd_824626] using wordTrace_append hprefix tailTrace_824626
  have hstable : (prefixWord ++ tailWord_824626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824626).length < 2 ^ (prefixWord ++ tailWord_824626).sum := by decide
  have hdescent : baseEnd_824626 < baseStart_824626 := by decide
  rcases family_descends (prefixWord ++ tailWord_824626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824640 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_824640 : Nat := 118140960795 + 824640 * 2 ^ 59
def prefixEnd_824640 : Nat := 4983230072969 + 3 ^ 40 * 824640 * 2
def baseEnd_824640 : Nat := 376388166154452289695605

theorem tailTrace_824640 : CollatzResearch.WordTrace tailWord_824640 prefixEnd_824640 376388166154452289695605 := by
  unfold tailWord_824640
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038545866238796072239687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20051394488318394762986249 15038545866238796072239687)
  ·
    refine ⟨22557818799358194108359531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15038545866238796072239687 22557818799358194108359531)
    ·
      refine ⟨33836728199037291162539297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22557818799358194108359531 33836728199037291162539297)
      ·
        refine ⟨25377546149277968371904473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33836728199037291162539297 25377546149277968371904473)
        ·
          refine ⟨19033159611958476278928355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25377546149277968371904473 19033159611958476278928355)
          ·
            refine ⟨28549739417937714418392533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19033159611958476278928355 28549739417937714418392533)
            ·
              refine ⟨669134517607915181681075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28549739417937714418392533 669134517607915181681075)
              ·
                refine ⟨1003701776411872772521613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669134517607915181681075 1003701776411872772521613)
                ·
                  refine ⟨376388166154452289695605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003701776411872772521613 376388166154452289695605)
                  ·
                    rfl

theorem cell20_824640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_824640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824640 prefixEnd_824640 := by exact prefixLift 824640
  have htrace : WordTrace (prefixWord ++ tailWord_824640) baseStart_824640 baseEnd_824640 := by
    simpa [prefixWord, tailWord_824640, baseEnd_824640] using wordTrace_append hprefix tailTrace_824640
  have hstable : (prefixWord ++ tailWord_824640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824640).length < 2 ^ (prefixWord ++ tailWord_824640).sum := by decide
  have hdescent : baseEnd_824640 < baseStart_824640 := by decide
  rcases family_descends (prefixWord ++ tailWord_824640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824646 : List Nat := [6, 1, 1, 3, 1, 2, 2, 4]
def baseStart_824646 : Nat := 118140960795 + 824646 * 2 ^ 59
def prefixEnd_824646 : Nat := 4983230072969 + 3 ^ 40 * 824646 * 2
def baseEnd_824646 : Nat := 125463634905980978498527

theorem tailTrace_824646 : CollatzResearch.WordTrace tailWord_824646 prefixEnd_824646 125463634905980978498527 := by
  unfold tailWord_824646
  simp only [CollatzResearch.WordTrace]
  refine ⟨939915955326745474037431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20051540380303903446131861 939915955326745474037431)
  ·
    refine ⟨1409873932990118211056147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 939915955326745474037431 1409873932990118211056147)
    ·
      refine ⟨2114810899485177316584221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1409873932990118211056147 2114810899485177316584221)
      ·
        refine ⟨793054087306941493719083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2114810899485177316584221 793054087306941493719083)
        ·
          refine ⟨1189581130960412240578625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793054087306941493719083 1189581130960412240578625)
          ·
            refine ⟨892185848220309180433969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189581130960412240578625 892185848220309180433969)
            ·
              refine ⟨669139386165231885325477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892185848220309180433969 669139386165231885325477)
              ·
                refine ⟨125463634905980978498527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669139386165231885325477 125463634905980978498527)
                ·
                  rfl

theorem cell20_824646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_824646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824646 prefixEnd_824646 := by exact prefixLift 824646
  have htrace : WordTrace (prefixWord ++ tailWord_824646) baseStart_824646 baseEnd_824646 := by
    simpa [prefixWord, tailWord_824646, baseEnd_824646] using wordTrace_append hprefix tailTrace_824646
  have hstable : (prefixWord ++ tailWord_824646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824646).length < 2 ^ (prefixWord ++ tailWord_824646).sum := by decide
  have hdescent : baseEnd_824646 < baseStart_824646 := by decide
  rcases family_descends (prefixWord ++ tailWord_824646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824661 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_824661 : Nat := 118140960795 + 824661 * 2 ^ 59
def prefixEnd_824661 : Nat := 4983230072969 + 3 ^ 40 * 824661 * 2
def baseEnd_824661 : Nat := 376397751126669549995519

theorem tailTrace_824661 : CollatzResearch.WordTrace tailWord_824661 prefixEnd_824661 376397751126669549995519 := by
  unfold tailWord_824661
  simp only [CollatzResearch.WordTrace]
  refine ⟨30077857665401512730993837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20051905110267675153995891 30077857665401512730993837)
  ·
    refine ⟨11279196624525567274122689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30077857665401512730993837 11279196624525567274122689)
    ·
      refine ⟨8459397468394175455592017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11279196624525567274122689 8459397468394175455592017)
      ·
        refine ⟨6344548101295631591694013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8459397468394175455592017 6344548101295631591694013)
        ·
          refine ⟨2379205537985861846885255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6344548101295631591694013 2379205537985861846885255)
          ·
            refine ⟨3568808306978792770327883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379205537985861846885255 3568808306978792770327883)
            ·
              refine ⟨5353212460468189155491825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3568808306978792770327883 5353212460468189155491825)
              ·
                refine ⟨4014909345351141866618869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5353212460468189155491825 4014909345351141866618869)
                ·
                  refine ⟨376397751126669549995519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4014909345351141866618869 376397751126669549995519)
                  ·
                    rfl

theorem cell20_824661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_824661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824661 prefixEnd_824661 := by exact prefixLift 824661
  have htrace : WordTrace (prefixWord ++ tailWord_824661) baseStart_824661 baseEnd_824661 := by
    simpa [prefixWord, tailWord_824661, baseEnd_824661] using wordTrace_append hprefix tailTrace_824661
  have hstable : (prefixWord ++ tailWord_824661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824661).length < 2 ^ (prefixWord ++ tailWord_824661).sum := by decide
  have hdescent : baseEnd_824661 < baseStart_824661 := by decide
  rcases family_descends (prefixWord ++ tailWord_824661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824675 : List Nat := [1, 1, 1, 5, 2, 2, 8]
def baseStart_824675 : Nat := 118140960795 + 824675 * 2 ^ 59
def prefixEnd_824675 : Nat := 4983230072969 + 3 ^ 40 * 824675 * 2
def baseEnd_824675 : Nat := 41822682345349747058755

theorem tailTrace_824675 : CollatzResearch.WordTrace tailWord_824675 prefixEnd_824675 41822682345349747058755 := by
  unfold tailWord_824675
  simp only [CollatzResearch.WordTrace]
  refine ⟨30078368287350793122003479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20052245524900528748002319 30078368287350793122003479)
  ·
    refine ⟨45117552431026189683005219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30078368287350793122003479 45117552431026189683005219)
    ·
      refine ⟨67676328646539284524507829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45117552431026189683005219 67676328646539284524507829)
      ·
        refine ⟨6344655810613057924172609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67676328646539284524507829 6344655810613057924172609)
        ·
          refine ⟨4758491857959793443129457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6344655810613057924172609 4758491857959793443129457)
          ·
            refine ⟨3568868893469845082347093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758491857959793443129457 3568868893469845082347093)
            ·
              refine ⟨41822682345349747058755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3568868893469845082347093 41822682345349747058755)
              ·
                rfl

theorem cell20_824675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_824675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824675 prefixEnd_824675 := by exact prefixLift 824675
  have htrace : WordTrace (prefixWord ++ tailWord_824675) baseStart_824675 baseEnd_824675 := by
    simpa [prefixWord, tailWord_824675, baseEnd_824675] using wordTrace_append hprefix tailTrace_824675
  have hstable : (prefixWord ++ tailWord_824675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824675).length < 2 ^ (prefixWord ++ tailWord_824675).sum := by decide
  have hdescent : baseEnd_824675 < baseStart_824675 := by decide
  rcases family_descends (prefixWord ++ tailWord_824675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824685 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_824685 : Nat := 118140960795 + 824685 * 2 ^ 59
def prefixEnd_824685 : Nat := 4983230072969 + 3 ^ 40 * 824685 * 2
def baseEnd_824685 : Nat := 376408705380632133195421

theorem tailTrace_824685 : CollatzResearch.WordTrace tailWord_824685 prefixEnd_824685 376408705380632133195421 := by
  unfold tailWord_824685
  simp only [CollatzResearch.WordTrace]
  refine ⟨30078733017314564829867509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20052488678209709886578339 30078733017314564829867509)
  ·
    refine ⟨2819881220373240452800079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30078733017314564829867509 2819881220373240452800079)
    ·
      refine ⟨4229821830559860679200119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2819881220373240452800079 4229821830559860679200119)
      ·
        refine ⟨6344732745839791018800179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4229821830559860679200119 6344732745839791018800179)
        ·
          refine ⟨9517099118759686528200269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6344732745839791018800179 9517099118759686528200269)
          ·
            refine ⟨3568912169534882448075101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9517099118759686528200269 3568912169534882448075101)
            ·
              refine ⟨1338342063575580918028163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3568912169534882448075101 1338342063575580918028163)
              ·
                refine ⟨2007513095363371377042245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338342063575580918028163 2007513095363371377042245)
                ·
                  refine ⟨376408705380632133195421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2007513095363371377042245 376408705380632133195421)
                  ·
                    rfl

theorem cell20_824685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_824685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824685 prefixEnd_824685 := by exact prefixLift 824685
  have htrace : WordTrace (prefixWord ++ tailWord_824685) baseStart_824685 baseEnd_824685 := by
    simpa [prefixWord, tailWord_824685, baseEnd_824685] using wordTrace_append hprefix tailTrace_824685
  have hstable : (prefixWord ++ tailWord_824685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824685).length < 2 ^ (prefixWord ++ tailWord_824685).sum := by decide
  have hdescent : baseEnd_824685 < baseStart_824685 := by decide
  rcases family_descends (prefixWord ++ tailWord_824685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824699 : List Nat := [1, 1, 1, 1, 1, 6, 3, 3, 3]
def baseStart_824699 : Nat := 118140960795 + 824699 * 2 ^ 59
def prefixEnd_824699 : Nat := 4983230072969 + 3 ^ 40 * 824699 * 2
def baseEnd_824699 : Nat := 376415095362110306728697

theorem tailTrace_824699 : CollatzResearch.WordTrace tailWord_824699 prefixEnd_824699 376415095362110306728697 := by
  unfold tailWord_824699
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079243639263845220877151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20052829092842563480584767 30079243639263845220877151)
  ·
    refine ⟨45118865458895767831315727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30079243639263845220877151 45118865458895767831315727)
    ·
      refine ⟨67678298188343651746973591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45118865458895767831315727 67678298188343651746973591)
      ·
        refine ⟨101517447282515477620460387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67678298188343651746973591 101517447282515477620460387)
        ·
          refine ⟨152276170923773216430690581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101517447282515477620460387 152276170923773216430690581)
          ·
            refine ⟨7137945512051869520188621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152276170923773216430690581 7137945512051869520188621)
            ·
              refine ⟨2676729567019451070070733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7137945512051869520188621 2676729567019451070070733)
              ·
                refine ⟨1003773587632294151276525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2676729567019451070070733 1003773587632294151276525)
                ·
                  refine ⟨376415095362110306728697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003773587632294151276525 376415095362110306728697)
                  ·
                    rfl

theorem cell20_824699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_824699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824699 prefixEnd_824699 := by exact prefixLift 824699
  have htrace : WordTrace (prefixWord ++ tailWord_824699) baseStart_824699 baseEnd_824699 := by
    simpa [prefixWord, tailWord_824699, baseEnd_824699] using wordTrace_append hprefix tailTrace_824699
  have hstable : (prefixWord ++ tailWord_824699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824699).length < 2 ^ (prefixWord ++ tailWord_824699).sum := by decide
  have hdescent : baseEnd_824699 < baseStart_824699 := by decide
  rcases family_descends (prefixWord ++ tailWord_824699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824761 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 4]
def baseStart_824761 : Nat := 118140960795 + 824761 * 2 ^ 59
def prefixEnd_824761 : Nat := 4983230072969 + 3 ^ 40 * 824761 * 2
def baseEnd_824761 : Nat := 376443393851513646661777

theorem tailTrace_824761 : CollatzResearch.WordTrace tailWord_824761 prefixEnd_824761 376443393851513646661777 := by
  unfold tailWord_824761
  simp only [CollatzResearch.WordTrace]
  refine ⟨30081504965039229809634137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20054336643359486539756091 30081504965039229809634137)
  ·
    refine ⟨22561128723779422357225603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30081504965039229809634137 22561128723779422357225603)
    ·
      refine ⟨33841693085669133535838405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22561128723779422357225603 33841693085669133535838405)
      ·
        refine ⟨6345317453562962537969701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33841693085669133535838405 6345317453562962537969701)
        ·
          refine ⟨1189747022543055475869319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6345317453562962537969701 1189747022543055475869319)
          ·
            refine ⟨1784620533814583213803979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189747022543055475869319 1784620533814583213803979)
            ·
              refine ⟨2676930800721874820705969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784620533814583213803979 2676930800721874820705969)
              ·
                refine ⟨2007698100541406115529477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2676930800721874820705969 2007698100541406115529477)
                ·
                  refine ⟨376443393851513646661777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2007698100541406115529477 376443393851513646661777)
                  ·
                    rfl

theorem cell20_824761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_824761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824761 prefixEnd_824761 := by exact prefixLift 824761
  have htrace : WordTrace (prefixWord ++ tailWord_824761) baseStart_824761 baseEnd_824761 := by
    simpa [prefixWord, tailWord_824761, baseEnd_824761] using wordTrace_append hprefix tailTrace_824761
  have hstable : (prefixWord ++ tailWord_824761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824761).length < 2 ^ (prefixWord ++ tailWord_824761).sum := by decide
  have hdescent : baseEnd_824761 < baseStart_824761 := by decide
  rcases family_descends (prefixWord ++ tailWord_824761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824770 : List Nat := [3, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_824770 : Nat := 118140960795 + 824770 * 2 ^ 59
def prefixEnd_824770 : Nat := 4983230072969 + 3 ^ 40 * 824770 * 2
def baseEnd_824770 : Nat := 376447501696749615361741

theorem tailTrace_824770 : CollatzResearch.WordTrace tailWord_824770 prefixEnd_824770 376447501696749615361741 := by
  unfold tailWord_824770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520458305501656086677941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20054555481337749564474509 7520458305501656086677941)
  ·
    refine ⟨705042966140780258126057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7520458305501656086677941 705042966140780258126057)
    ·
      refine ⟨528782224605585193594543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 705042966140780258126057 528782224605585193594543)
      ·
        refine ⟨793173336908377790391815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528782224605585193594543 793173336908377790391815)
        ·
          refine ⟨1189760005362566685587723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793173336908377790391815 1189760005362566685587723)
          ·
            refine ⟨1784640008043850028381585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189760005362566685587723 1784640008043850028381585)
            ·
              refine ⟨1338480006032887521286189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784640008043850028381585 1338480006032887521286189)
              ·
                refine ⟨501930002262332820482321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338480006032887521286189 501930002262332820482321)
                ·
                  refine ⟨376447501696749615361741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501930002262332820482321 376447501696749615361741)
                  ·
                    rfl

theorem cell20_824770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_824770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824770 prefixEnd_824770 := by exact prefixLift 824770
  have htrace : WordTrace (prefixWord ++ tailWord_824770) baseStart_824770 baseEnd_824770 := by
    simpa [prefixWord, tailWord_824770, baseEnd_824770] using wordTrace_append hprefix tailTrace_824770
  have hstable : (prefixWord ++ tailWord_824770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824770).length < 2 ^ (prefixWord ++ tailWord_824770).sum := by decide
  have hdescent : baseEnd_824770 < baseStart_824770 := by decide
  rcases family_descends (prefixWord ++ tailWord_824770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824778 : List Nat := [3, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_824778 : Nat := 118140960795 + 824778 * 2 ^ 59
def prefixEnd_824778 : Nat := 4983230072969 + 3 ^ 40 * 824778 * 2
def baseEnd_824778 : Nat := 376451153114737143095041

theorem tailTrace_824778 : CollatzResearch.WordTrace tailWord_824778 prefixEnd_824778 376451153114737143095041 := by
  unfold tailWord_824778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520531251494410428250747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20054750003985094475335325 7520531251494410428250747)
  ·
    refine ⟨11280796877241615642376121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7520531251494410428250747 11280796877241615642376121)
    ·
      refine ⟨8460597657931211731782091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11280796877241615642376121 8460597657931211731782091)
      ·
        refine ⟨12690896486896817597673137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460597657931211731782091 12690896486896817597673137)
        ·
          refine ⟨9518172365172613198254853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12690896486896817597673137 9518172365172613198254853)
          ·
            refine ⟨1784657318469864974672785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9518172365172613198254853 1784657318469864974672785)
            ·
              refine ⟨1338492988852398731004589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784657318469864974672785 1338492988852398731004589)
              ·
                refine ⟨501934870819649524126721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338492988852398731004589 501934870819649524126721)
                ·
                  refine ⟨376451153114737143095041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501934870819649524126721 376451153114737143095041)
                  ·
                    rfl

theorem cell20_824778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_824778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824778 prefixEnd_824778 := by exact prefixLift 824778
  have htrace : WordTrace (prefixWord ++ tailWord_824778) baseStart_824778 baseEnd_824778 := by
    simpa [prefixWord, tailWord_824778, baseEnd_824778] using wordTrace_append hprefix tailTrace_824778
  have hstable : (prefixWord ++ tailWord_824778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824778).length < 2 ^ (prefixWord ++ tailWord_824778).sum := by decide
  have hdescent : baseEnd_824778 < baseStart_824778 := by decide
  rcases family_descends (prefixWord ++ tailWord_824778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824788 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 3]
def baseStart_824788 : Nat := 118140960795 + 824788 * 2 ^ 59
def prefixEnd_824788 : Nat := 4983230072969 + 3 ^ 40 * 824788 * 2
def baseEnd_824788 : Nat := 376455717387221552761667

theorem tailTrace_824788 : CollatzResearch.WordTrace tailWord_824788 prefixEnd_824788 376455717387221552761667 := by
  unfold tailWord_824788
  simp only [CollatzResearch.WordTrace]
  refine ⟨15041244867970706710433509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20054993157294275613911345 15041244867970706710433509)
  ·
    refine ⟨2820233412744507508206283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15041244867970706710433509 2820233412744507508206283)
    ·
      refine ⟨4230350119116761262309425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820233412744507508206283 4230350119116761262309425)
      ·
        refine ⟨3172762589337570946732069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4230350119116761262309425 3172762589337570946732069)
        ·
          refine ⟨594892985500794552512263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3172762589337570946732069 594892985500794552512263)
          ·
            refine ⟨892339478251191828768395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594892985500794552512263 892339478251191828768395)
            ·
              refine ⟨1338509217376787743152593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892339478251191828768395 1338509217376787743152593)
              ·
                refine ⟨1003881913032590807364445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338509217376787743152593 1003881913032590807364445)
                ·
                  refine ⟨376455717387221552761667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1003881913032590807364445 376455717387221552761667)
                  ·
                    rfl

theorem cell20_824788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_824788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824788 prefixEnd_824788 := by exact prefixLift 824788
  have htrace : WordTrace (prefixWord ++ tailWord_824788) baseStart_824788 baseEnd_824788 := by
    simpa [prefixWord, tailWord_824788, baseEnd_824788] using wordTrace_append hprefix tailTrace_824788
  have hstable : (prefixWord ++ tailWord_824788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824788).length < 2 ^ (prefixWord ++ tailWord_824788).sum := by decide
  have hdescent : baseEnd_824788 < baseStart_824788 := by decide
  rcases family_descends (prefixWord ++ tailWord_824788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824789 : List Nat := [1, 3, 2, 3, 1, 1, 9]
def baseStart_824789 : Nat := 118140960795 + 824789 * 2 ^ 59
def prefixEnd_824789 : Nat := 4983230072969 + 3 ^ 40 * 824789 * 2
def baseEnd_824789 : Nat := 41828463757163332636481

theorem tailTrace_824789 : CollatzResearch.WordTrace tailWord_824789 prefixEnd_824789 41828463757163332636481 := by
  unfold tailWord_824789
  simp only [CollatzResearch.WordTrace]
  refine ⟨30082526208937790591653421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20055017472625193727768947 30082526208937790591653421)
  ·
    refine ⟨11280947328351671471870033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30082526208937790591653421 11280947328351671471870033)
    ·
      refine ⟨8460710496263753603902525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11280947328351671471870033 8460710496263753603902525)
      ·
        refine ⟨3172766436098907601463447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8460710496263753603902525 3172766436098907601463447)
        ·
          refine ⟨4759149654148361402195171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172766436098907601463447 4759149654148361402195171)
          ·
            refine ⟨7138724481222542103292757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759149654148361402195171 7138724481222542103292757)
            ·
              refine ⟨41828463757163332636481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7138724481222542103292757 41828463757163332636481)
              ·
                rfl

theorem cell20_824789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_824789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824789 prefixEnd_824789 := by exact prefixLift 824789
  have htrace : WordTrace (prefixWord ++ tailWord_824789) baseStart_824789 baseEnd_824789 := by
    simpa [prefixWord, tailWord_824789, baseEnd_824789] using wordTrace_append hprefix tailTrace_824789
  have hstable : (prefixWord ++ tailWord_824789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824789).length < 2 ^ (prefixWord ++ tailWord_824789).sum := by decide
  have hdescent : baseEnd_824789 < baseStart_824789 := by decide
  rcases family_descends (prefixWord ++ tailWord_824789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824799 : List Nat := [1, 1, 2, 3, 3, 1, 1, 6, 2]
def baseStart_824799 : Nat := 118140960795 + 824799 * 2 ^ 59
def prefixEnd_824799 : Nat := 4983230072969 + 3 ^ 40 * 824799 * 2
def baseEnd_824799 : Nat := 376460738086954403394955

theorem tailTrace_824799 : CollatzResearch.WordTrace tailWord_824799 prefixEnd_824799 376460738086954403394955 := by
  unfold tailWord_824799
  simp only [CollatzResearch.WordTrace]
  refine ⟨30082890938901562299517451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20055260625934374866344967 30082890938901562299517451)
  ·
    refine ⟨45124336408352343449276177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30082890938901562299517451 45124336408352343449276177)
    ·
      refine ⟨33843252306264257586957133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45124336408352343449276177 33843252306264257586957133)
      ·
        refine ⟨12691219614849096595108925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33843252306264257586957133 12691219614849096595108925)
        ·
          refine ⟨4759207355568411223165847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12691219614849096595108925 4759207355568411223165847)
          ·
            refine ⟨7138811033352616834748771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759207355568411223165847 7138811033352616834748771)
            ·
              refine ⟨10708216550028925252123157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138811033352616834748771 10708216550028925252123157)
              ·
                refine ⟨501947650782605871193273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10708216550028925252123157 501947650782605871193273)
                ·
                  refine ⟨376460738086954403394955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501947650782605871193273 376460738086954403394955)
                  ·
                    rfl

theorem cell20_824799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 2].length) (baseStart_824799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824799 prefixEnd_824799 := by exact prefixLift 824799
  have htrace : WordTrace (prefixWord ++ tailWord_824799) baseStart_824799 baseEnd_824799 := by
    simpa [prefixWord, tailWord_824799, baseEnd_824799] using wordTrace_append hprefix tailTrace_824799
  have hstable : (prefixWord ++ tailWord_824799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824799).length < 2 ^ (prefixWord ++ tailWord_824799).sum := by decide
  have hdescent : baseEnd_824799 < baseStart_824799 := by decide
  rcases family_descends (prefixWord ++ tailWord_824799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824833 : List Nat := [1, 2, 4, 1, 4, 2, 1, 3, 2]
def baseStart_824833 : Nat := 118140960795 + 824833 * 2 ^ 59
def prefixEnd_824833 : Nat := 4983230072969 + 3 ^ 40 * 824833 * 2
def baseEnd_824833 : Nat := 376476256613401396261483

theorem tailTrace_824833 : CollatzResearch.WordTrace tailWord_824833 prefixEnd_824833 376476256613401396261483 := by
  unfold tailWord_824833
  simp only [CollatzResearch.WordTrace]
  refine ⟨30084131020778386106255153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20056087347185590737503435 30084131020778386106255153)
  ·
    refine ⟨22563098265583789579691365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30084131020778386106255153 22563098265583789579691365)
    ·
      refine ⟨4230580924796960546192131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22563098265583789579691365 4230580924796960546192131)
      ·
        refine ⟨6345871387195440819288197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230580924796960546192131 6345871387195440819288197)
        ·
          refine ⟨1189850885099145153616537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6345871387195440819288197 1189850885099145153616537)
          ·
            refine ⟨892388163824358865212403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189850885099145153616537 892388163824358865212403)
            ·
              refine ⟨1338582245736538297818605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892388163824358865212403 1338582245736538297818605)
              ·
                refine ⟨501968342151201861681977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338582245736538297818605 501968342151201861681977)
                ·
                  refine ⟨376476256613401396261483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 501968342151201861681977 376476256613401396261483)
                  ·
                    rfl

theorem cell20_824833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_824833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824833 prefixEnd_824833 := by exact prefixLift 824833
  have htrace : WordTrace (prefixWord ++ tailWord_824833) baseStart_824833 baseEnd_824833 := by
    simpa [prefixWord, tailWord_824833, baseEnd_824833] using wordTrace_append hprefix tailTrace_824833
  have hstable : (prefixWord ++ tailWord_824833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824833).length < 2 ^ (prefixWord ++ tailWord_824833).sum := by decide
  have hdescent : baseEnd_824833 < baseStart_824833 := by decide
  rcases family_descends (prefixWord ++ tailWord_824833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824844 : List Nat := [2, 2, 1, 2, 5, 2, 6]
def baseStart_824844 : Nat := 118140960795 + 824844 * 2 ^ 59
def prefixEnd_824844 : Nat := 4983230072969 + 3 ^ 40 * 824844 * 2
def baseEnd_824844 : Nat := 41831253034792694099419

theorem tailTrace_824844 : CollatzResearch.WordTrace tailWord_824844 prefixEnd_824844 41831253034792694099419 := by
  unfold tailWord_824844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15042266111869267492452793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20056354815825689989937057 15042266111869267492452793)
  ·
    refine ⟨11281699583901950619339595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15042266111869267492452793 11281699583901950619339595)
    ·
      refine ⟨16922549375852925929009393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11281699583901950619339595 16922549375852925929009393)
      ·
        refine ⟨12691912031889694446757045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16922549375852925929009393 12691912031889694446757045)
        ·
          refine ⟨1189866752989658854383473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12691912031889694446757045 1189866752989658854383473)
          ·
            refine ⟨892400064742244140787605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189866752989658854383473 892400064742244140787605)
            ·
              refine ⟨41831253034792694099419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 892400064742244140787605 41831253034792694099419)
              ·
                rfl

theorem cell20_824844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 6].length) (baseStart_824844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824844 prefixEnd_824844 := by exact prefixLift 824844
  have htrace : WordTrace (prefixWord ++ tailWord_824844) baseStart_824844 baseEnd_824844 := by
    simpa [prefixWord, tailWord_824844, baseEnd_824844] using wordTrace_append hprefix tailTrace_824844
  have hstable : (prefixWord ++ tailWord_824844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824844).length < 2 ^ (prefixWord ++ tailWord_824844).sum := by decide
  have hdescent : baseEnd_824844 < baseStart_824844 := by decide
  rcases family_descends (prefixWord ++ tailWord_824844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824865 : List Nat := [1, 2, 3, 2, 2, 2, 1, 7]
def baseStart_824865 : Nat := 118140960795 + 824865 * 2 ^ 59
def prefixEnd_824865 : Nat := 4983230072969 + 3 ^ 40 * 824865 * 2
def baseEnd_824865 : Nat := 125496954095117169064895

theorem tailTrace_824865 : CollatzResearch.WordTrace tailWord_824865 prefixEnd_824865 125496954095117169064895 := by
  unfold tailWord_824865
  simp only [CollatzResearch.WordTrace]
  refine ⟨30085298156662455571420049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20056865437774970380946699 30085298156662455571420049)
  ·
    refine ⟨22563973617496841678565037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30085298156662455571420049 22563973617496841678565037)
    ·
      refine ⟨8461490106561315629461889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22563973617496841678565037 8461490106561315629461889)
      ·
        refine ⟨6346117579920986722096417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8461490106561315629461889 6346117579920986722096417)
        ·
          refine ⟨4759588184940740041572313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6346117579920986722096417 4759588184940740041572313)
          ·
            refine ⟨3569691138705555031179235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759588184940740041572313 3569691138705555031179235)
            ·
              refine ⟨5354536708058332546768853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3569691138705555031179235 5354536708058332546768853)
              ·
                refine ⟨125496954095117169064895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5354536708058332546768853 125496954095117169064895)
                ·
                  rfl

theorem cell20_824865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_824865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824865 prefixEnd_824865 := by exact prefixLift 824865
  have htrace : WordTrace (prefixWord ++ tailWord_824865) baseStart_824865 baseEnd_824865 := by
    simpa [prefixWord, tailWord_824865, baseEnd_824865] using wordTrace_append hprefix tailTrace_824865
  have hstable : (prefixWord ++ tailWord_824865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824865).length < 2 ^ (prefixWord ++ tailWord_824865).sum := by decide
  have hdescent : baseEnd_824865 < baseStart_824865 := by decide
  rcases family_descends (prefixWord ++ tailWord_824865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824902 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_824902 : Nat := 118140960795 + 824902 * 2 ^ 59
def prefixEnd_824902 : Nat := 4983230072969 + 3 ^ 40 * 824902 * 2
def baseEnd_824902 : Nat := 376507750093543822961201

theorem tailTrace_824902 : CollatzResearch.WordTrace tailWord_824902 prefixEnd_824902 376507750093543822961201 := by
  unfold tailWord_824902
  simp only [CollatzResearch.WordTrace]
  refine ⟨940207739297762840328655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20057765105018940593677973 940207739297762840328655)
  ·
    refine ⟨1410311608946644260492983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940207739297762840328655 1410311608946644260492983)
    ·
      refine ⟨2115467413419966390739475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410311608946644260492983 2115467413419966390739475)
      ·
        refine ⟨3173201120129949586109213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115467413419966390739475 3173201120129949586109213)
        ·
          refine ⟨1189950420048731094790955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3173201120129949586109213 1189950420048731094790955)
          ·
            refine ⟨1784925630073096642186433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189950420048731094790955 1784925630073096642186433)
            ·
              refine ⟨1338694222554822481639825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784925630073096642186433 1338694222554822481639825)
              ·
                refine ⟨1004020666916116861229869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338694222554822481639825 1004020666916116861229869)
                ·
                  refine ⟨376507750093543822961201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004020666916116861229869 376507750093543822961201)
                  ·
                    rfl

theorem cell20_824902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_824902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824902 prefixEnd_824902 := by exact prefixLift 824902
  have htrace : WordTrace (prefixWord ++ tailWord_824902) baseStart_824902 baseEnd_824902 := by
    simpa [prefixWord, tailWord_824902, baseEnd_824902] using wordTrace_append hprefix tailTrace_824902
  have hstable : (prefixWord ++ tailWord_824902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824902).length < 2 ^ (prefixWord ++ tailWord_824902).sum := by decide
  have hdescent : baseEnd_824902 < baseStart_824902 := by decide
  rcases family_descends (prefixWord ++ tailWord_824902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824903 : List Nat := [1, 1, 4, 1, 5, 8]
def baseStart_824903 : Nat := 118140960795 + 824903 * 2 ^ 59
def prefixEnd_824903 : Nat := 4983230072969 + 3 ^ 40 * 824903 * 2
def baseEnd_824903 : Nat := 13944748389658972738069

theorem tailTrace_824903 : CollatzResearch.WordTrace tailWord_824903 prefixEnd_824903 13944748389658972738069 := by
  unfold tailWord_824903
  simp only [CollatzResearch.WordTrace]
  refine ⟨30086684130524788061303363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20057789420349858707535575 30086684130524788061303363)
  ·
    refine ⟨45130026195787182091955045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30086684130524788061303363 45130026195787182091955045)
    ·
      refine ⟨8461879911710096642241571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45130026195787182091955045 8461879911710096642241571)
      ·
        refine ⟨12692819867565144963362357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8461879911710096642241571 12692819867565144963362357)
        ·
          refine ⟨1189951862584232340315221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12692819867565144963362357 1189951862584232340315221)
          ·
            refine ⟨13944748389658972738069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1189951862584232340315221 13944748389658972738069)
            ·
              rfl

theorem cell20_824903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 8].length) (baseStart_824903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824903 prefixEnd_824903 := by exact prefixLift 824903
  have htrace : WordTrace (prefixWord ++ tailWord_824903) baseStart_824903 baseEnd_824903 := by
    simpa [prefixWord, tailWord_824903, baseEnd_824903] using wordTrace_append hprefix tailTrace_824903
  have hstable : (prefixWord ++ tailWord_824903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824903).length < 2 ^ (prefixWord ++ tailWord_824903).sum := by decide
  have hdescent : baseEnd_824903 < baseStart_824903 := by decide
  rcases family_descends (prefixWord ++ tailWord_824903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824909 : List Nat := [1, 6, 1, 1, 3, 1, 1, 4, 2]
def baseStart_824909 : Nat := 118140960795 + 824909 * 2 ^ 59
def prefixEnd_824909 : Nat := 4983230072969 + 3 ^ 40 * 824909 * 2
def baseEnd_824909 : Nat := 376510945084282909727839

theorem tailTrace_824909 : CollatzResearch.WordTrace tailWord_824909 prefixEnd_824909 376510945084282909727839 := by
  unfold tailWord_824909
  simp only [CollatzResearch.WordTrace]
  refine ⟨30086902968503051086021781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20057935312335367390681187 30086902968503051086021781)
  ·
    refine ⟨1410323576648580519657271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30086902968503051086021781 1410323576648580519657271)
    ·
      refine ⟨2115485364972870779485907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410323576648580519657271 2115485364972870779485907)
      ·
        refine ⟨3173228047459306169228861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115485364972870779485907 3173228047459306169228861)
        ·
          refine ⟨1189960517797239813460823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3173228047459306169228861 1189960517797239813460823)
          ·
            refine ⟨1784940776695859720191235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189960517797239813460823 1784940776695859720191235)
            ·
              refine ⟨2677411165043789580286853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784940776695859720191235 2677411165043789580286853)
              ·
                refine ⟨502014593445710546303785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2677411165043789580286853 502014593445710546303785)
                ·
                  refine ⟨376510945084282909727839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502014593445710546303785 376510945084282909727839)
                  ·
                    rfl

theorem cell20_824909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_824909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824909 prefixEnd_824909 := by exact prefixLift 824909
  have htrace : WordTrace (prefixWord ++ tailWord_824909) baseStart_824909 baseEnd_824909 := by
    simpa [prefixWord, tailWord_824909, baseEnd_824909] using wordTrace_append hprefix tailTrace_824909
  have hstable : (prefixWord ++ tailWord_824909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824909).length < 2 ^ (prefixWord ++ tailWord_824909).sum := by decide
  have hdescent : baseEnd_824909 < baseStart_824909 := by decide
  rcases family_descends (prefixWord ++ tailWord_824909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824913 : List Nat := [1, 2, 2, 1, 3, 2, 3, 4, 2]
def baseStart_824913 : Nat := 118140960795 + 824913 * 2 ^ 59
def prefixEnd_824913 : Nat := 4983230072969 + 3 ^ 40 * 824913 * 2
def baseEnd_824913 : Nat := 376512770793276673594489

theorem tailTrace_824913 : CollatzResearch.WordTrace tailWord_824913 prefixEnd_824913 376512770793276673594489 := by
  unfold tailWord_824913
  simp only [CollatzResearch.WordTrace]
  refine ⟨30087048860488559769167393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20058032573659039846111595 30087048860488559769167393)
  ·
    refine ⟨22565286645366419826875545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30087048860488559769167393 22565286645366419826875545)
    ·
      refine ⟨16923964984024814870156659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22565286645366419826875545 16923964984024814870156659)
      ·
        refine ⟨25385947476037222305234989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16923964984024814870156659 25385947476037222305234989)
        ·
          refine ⟨9519730303513958364463121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25385947476037222305234989 9519730303513958364463121)
          ·
            refine ⟨7139797727635468773347341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9519730303513958364463121 7139797727635468773347341)
            ·
              refine ⟨2677424147863300790005253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7139797727635468773347341 2677424147863300790005253)
              ·
                refine ⟨502017027724368898125985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2677424147863300790005253 502017027724368898125985)
                ·
                  refine ⟨376512770793276673594489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502017027724368898125985 376512770793276673594489)
                  ·
                    rfl

theorem cell20_824913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_824913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824913 prefixEnd_824913 := by exact prefixLift 824913
  have htrace : WordTrace (prefixWord ++ tailWord_824913) baseStart_824913 baseEnd_824913 := by
    simpa [prefixWord, tailWord_824913, baseEnd_824913] using wordTrace_append hprefix tailTrace_824913
  have hstable : (prefixWord ++ tailWord_824913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824913).length < 2 ^ (prefixWord ++ tailWord_824913).sum := by decide
  have hdescent : baseEnd_824913 < baseStart_824913 := by decide
  rcases family_descends (prefixWord ++ tailWord_824913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824955 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_824955 : Nat := 118140960795 + 824955 * 2 ^ 59
def prefixEnd_824955 : Nat := 4983230072969 + 3 ^ 40 * 824955 * 2
def baseEnd_824955 : Nat := 376531940737711194194317

theorem tailTrace_824955 : CollatzResearch.WordTrace tailWord_824955 prefixEnd_824955 376531940737711194194317 := by
  unfold tailWord_824955
  simp only [CollatzResearch.WordTrace]
  refine ⟨30088580726336400942196319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20059053817557600628130879 30088580726336400942196319)
  ·
    refine ⟨45132871089504601413294479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30088580726336400942196319 45132871089504601413294479)
    ·
      refine ⟨67699306634256902119941719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45132871089504601413294479 67699306634256902119941719)
      ·
        refine ⟨101548959951385353179912579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67699306634256902119941719 101548959951385353179912579)
        ·
          refine ⟨152323439927078029769868869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101548959951385353179912579 152323439927078029769868869)
          ·
            refine ⟨28560644986327130581850413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152323439927078029769868869 28560644986327130581850413)
            ·
              refine ⟨10710241869872673968193905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28560644986327130581850413 10710241869872673968193905)
              ·
                refine ⟨8032681402404505476145429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10710241869872673968193905 8032681402404505476145429)
                ·
                  refine ⟨376531940737711194194317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8032681402404505476145429 376531940737711194194317)
                  ·
                    rfl

theorem cell20_824955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_824955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824955 prefixEnd_824955 := by exact prefixLift 824955
  have htrace : WordTrace (prefixWord ++ tailWord_824955) baseStart_824955 baseEnd_824955 := by
    simpa [prefixWord, tailWord_824955, baseEnd_824955] using wordTrace_append hprefix tailTrace_824955
  have hstable : (prefixWord ++ tailWord_824955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824955).length < 2 ^ (prefixWord ++ tailWord_824955).sum := by decide
  have hdescent : baseEnd_824955 < baseStart_824955 := by decide
  rcases family_descends (prefixWord ++ tailWord_824955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824968 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_824968 : Nat := 118140960795 + 824968 * 2 ^ 59
def prefixEnd_824968 : Nat := 4983230072969 + 3 ^ 40 * 824968 * 2
def baseEnd_824968 : Nat := 376537874291940926760931

theorem tailTrace_824968 : CollatzResearch.WordTrace tailWord_824968 prefixEnd_824968 376537874291940926760931 := by
  unfold tailWord_824968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15044527437644652081209779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20059369916859536108279705 15044527437644652081209779)
  ·
    refine ⟨22566791156466978121814669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15044527437644652081209779 22566791156466978121814669)
    ·
      refine ⟨8462546683675116795680501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22566791156466978121814669 8462546683675116795680501)
      ·
        refine ⟨793363751594542199595047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8462546683675116795680501 793363751594542199595047)
        ·
          refine ⟨1190045627391813299392571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793363751594542199595047 1190045627391813299392571)
          ·
            refine ⟨1785068441087719949088857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190045627391813299392571 1785068441087719949088857)
            ·
              refine ⟨1338801330815789961816643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785068441087719949088857 1338801330815789961816643)
              ·
                refine ⟨2008201996223684942724965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338801330815789961816643 2008201996223684942724965)
                ·
                  refine ⟨376537874291940926760931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008201996223684942724965 376537874291940926760931)
                  ·
                    rfl

theorem cell20_824968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_824968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824968 prefixEnd_824968 := by exact prefixLift 824968
  have htrace : WordTrace (prefixWord ++ tailWord_824968) baseStart_824968 baseEnd_824968 := by
    simpa [prefixWord, tailWord_824968, baseEnd_824968] using wordTrace_append hprefix tailTrace_824968
  have hstable : (prefixWord ++ tailWord_824968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824968).length < 2 ^ (prefixWord ++ tailWord_824968).sum := by decide
  have hdescent : baseEnd_824968 < baseStart_824968 := by decide
  rcases family_descends (prefixWord ++ tailWord_824968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824972 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 4]
def baseStart_824972 : Nat := 118140960795 + 824972 * 2 ^ 59
def prefixEnd_824972 : Nat := 4983230072969 + 3 ^ 40 * 824972 * 2
def baseEnd_824972 : Nat := 376539700000934690627581

theorem tailTrace_824972 : CollatzResearch.WordTrace tailWord_824972 prefixEnd_824972 376539700000934690627581 := by
  unfold tailWord_824972
  simp only [CollatzResearch.WordTrace]
  refine ⟨15044600383637406422782585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20059467178183208563710113 15044600383637406422782585)
  ·
    refine ⟨11283450287728054817086939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15044600383637406422782585 11283450287728054817086939)
    ·
      refine ⟨16925175431592082225630409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11283450287728054817086939 16925175431592082225630409)
      ·
        refine ⟨12693881573694061669222807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16925175431592082225630409 12693881573694061669222807)
        ·
          refine ⟨19040822360541092503834211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12693881573694061669222807 19040822360541092503834211)
          ·
            refine ⟨28561233540811638755751317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19040822360541092503834211 28561233540811638755751317)
            ·
              refine ⟨1338807822225545566675843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28561233540811638755751317 1338807822225545566675843)
              ·
                refine ⟨2008211733338318350013765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1338807822225545566675843 2008211733338318350013765)
                ·
                  refine ⟨376539700000934690627581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008211733338318350013765 376539700000934690627581)
                  ·
                    rfl

theorem cell20_824972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_824972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824972 prefixEnd_824972 := by exact prefixLift 824972
  have htrace : WordTrace (prefixWord ++ tailWord_824972) baseStart_824972 baseEnd_824972 := by
    simpa [prefixWord, tailWord_824972, baseEnd_824972] using wordTrace_append hprefix tailTrace_824972
  have hstable : (prefixWord ++ tailWord_824972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824972).length < 2 ^ (prefixWord ++ tailWord_824972).sum := by decide
  have hdescent : baseEnd_824972 < baseStart_824972 := by decide
  rcases family_descends (prefixWord ++ tailWord_824972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824996 : List Nat := [2, 3, 1, 2, 2, 2, 4, 4]
def baseStart_824996 : Nat := 118140960795 + 824996 * 2 ^ 59
def prefixEnd_824996 : Nat := 4983230072969 + 3 ^ 40 * 824996 * 2
def baseEnd_824996 : Nat := 125516884751632424609161

theorem tailTrace_824996 : CollatzResearch.WordTrace tailWord_824996 prefixEnd_824996 125516884751632424609161 := by
  unfold tailWord_824996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045038059593932472219421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20060050746125243296292561 15045038059593932472219421)
  ·
    refine ⟨5641889272347724677082283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15045038059593932472219421 5641889272347724677082283)
    ·
      refine ⟨8462833908521587015623425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5641889272347724677082283 8462833908521587015623425)
      ·
        refine ⟨6347125431391190261717569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8462833908521587015623425 6347125431391190261717569)
        ·
          refine ⟨4760344073543392696288177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6347125431391190261717569 4760344073543392696288177)
          ·
            refine ⟨3570258055157544522216133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4760344073543392696288177 3570258055157544522216133)
            ·
              refine ⟨669423385342039597915525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3570258055157544522216133 669423385342039597915525)
              ·
                refine ⟨125516884751632424609161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669423385342039597915525 125516884751632424609161)
                ·
                  rfl

theorem cell20_824996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_824996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_824996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_824996 prefixEnd_824996 := by exact prefixLift 824996
  have htrace : WordTrace (prefixWord ++ tailWord_824996) baseStart_824996 baseEnd_824996 := by
    simpa [prefixWord, tailWord_824996, baseEnd_824996] using wordTrace_append hprefix tailTrace_824996
  have hstable : (prefixWord ++ tailWord_824996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824996).length < 2 ^ (prefixWord ++ tailWord_824996).sum := by decide
  have hdescent : baseEnd_824996 < baseStart_824996 := by decide
  rcases family_descends (prefixWord ++ tailWord_824996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825013 : List Nat := [1, 3, 3, 3, 3, 1, 6]
def baseStart_825013 : Nat := 118140960795 + 825013 * 2 ^ 59
def prefixEnd_825013 : Nat := 4983230072969 + 3 ^ 40 * 825013 * 2
def baseEnd_825013 : Nat := 41839823724235641140083

theorem tailTrace_825013 : CollatzResearch.WordTrace tailWord_825013 prefixEnd_825013 41839823724235641140083 := by
  unfold tailWord_825013
  simp only [CollatzResearch.WordTrace]
  refine ⟨30090696160126276847807693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20060464106750851231871795 30090696160126276847807693)
  ·
    refine ⟨11284011060047353817927885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30090696160126276847807693 11284011060047353817927885)
    ·
      refine ⟨4231504147517757681722957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11284011060047353817927885 4231504147517757681722957)
      ·
        refine ⟨1586814055319159130646109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4231504147517757681722957 1586814055319159130646109)
        ·
          refine ⟨595055270744684673992291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1586814055319159130646109 595055270744684673992291)
          ·
            refine ⟨892582906117027010988437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595055270744684673992291 892582906117027010988437)
            ·
              refine ⟨41839823724235641140083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 892582906117027010988437 41839823724235641140083)
              ·
                rfl

theorem cell20_825013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 6].length) (baseStart_825013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825013 prefixEnd_825013 := by exact prefixLift 825013
  have htrace : WordTrace (prefixWord ++ tailWord_825013) baseStart_825013 baseEnd_825013 := by
    simpa [prefixWord, tailWord_825013, baseEnd_825013] using wordTrace_append hprefix tailTrace_825013
  have hstable : (prefixWord ++ tailWord_825013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825013).length < 2 ^ (prefixWord ++ tailWord_825013).sum := by decide
  have hdescent : baseEnd_825013 < baseStart_825013 := by decide
  rcases family_descends (prefixWord ++ tailWord_825013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825024 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_825024 : Nat := 118140960795 + 825024 * 2 ^ 59
def prefixEnd_825024 : Nat := 4983230072969 + 3 ^ 40 * 825024 * 2
def baseEnd_825024 : Nat := 376563434217853620894035

theorem tailTrace_825024 : CollatzResearch.WordTrace tailWord_825024 prefixEnd_825024 376563434217853620894035 := by
  unfold tailWord_825024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045548681543212863229063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20060731575390950484305417 15045548681543212863229063)
  ·
    refine ⟨22568323022314819294843595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15045548681543212863229063 22568323022314819294843595)
    ·
      refine ⟨33852484533472228942265393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22568323022314819294843595 33852484533472228942265393)
      ·
        refine ⟨25389363400104171706699045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33852484533472228942265393 25389363400104171706699045)
        ·
          refine ⟨4760505637519532195006071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25389363400104171706699045 4760505637519532195006071)
          ·
            refine ⟨7140758456279298292509107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760505637519532195006071 7140758456279298292509107)
            ·
              refine ⟨10711137684418947438763661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7140758456279298292509107 10711137684418947438763661)
              ·
                refine ⟨4016676631657105289536373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10711137684418947438763661 4016676631657105289536373)
                ·
                  refine ⟨376563434217853620894035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4016676631657105289536373 376563434217853620894035)
                  ·
                    rfl

theorem cell20_825024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_825024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825024 prefixEnd_825024 := by exact prefixLift 825024
  have htrace : WordTrace (prefixWord ++ tailWord_825024) baseStart_825024 baseEnd_825024 := by
    simpa [prefixWord, tailWord_825024, baseEnd_825024] using wordTrace_append hprefix tailTrace_825024
  have hstable : (prefixWord ++ tailWord_825024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825024).length < 2 ^ (prefixWord ++ tailWord_825024).sum := by decide
  have hdescent : baseEnd_825024 < baseStart_825024 := by decide
  rcases family_descends (prefixWord ++ tailWord_825024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825030 : List Nat := [6, 1, 2, 1, 1, 2, 2, 5]
def baseStart_825030 : Nat := 118140960795 + 825030 * 2 ^ 59
def prefixEnd_825030 : Nat := 4983230072969 + 3 ^ 40 * 825030 * 2
def baseEnd_825030 : Nat := 125522057593781422231337

theorem tailTrace_825030 : CollatzResearch.WordTrace tailWord_825030 prefixEnd_825030 125522057593781422231337 := by
  unfold tailWord_825030
  simp only [CollatzResearch.WordTrace]
  refine ⟨940353631283271523474267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20060877467376459167451029 940353631283271523474267)
  ·
    refine ⟨1410530446924907285211401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940353631283271523474267 1410530446924907285211401)
    ·
      refine ⟨1057897835193680463908551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1410530446924907285211401 1057897835193680463908551)
      ·
        refine ⟨1586846752790520695862827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057897835193680463908551 1586846752790520695862827)
        ·
          refine ⟨2380270129185781043794241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586846752790520695862827 2380270129185781043794241)
          ·
            refine ⟨1785202596889335782845681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2380270129185781043794241 1785202596889335782845681)
            ·
              refine ⟨1338901947667001837134261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785202596889335782845681 1338901947667001837134261)
              ·
                refine ⟨125522057593781422231337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1338901947667001837134261 125522057593781422231337)
                ·
                  rfl

theorem cell20_825030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_825030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825030 prefixEnd_825030 := by exact prefixLift 825030
  have htrace : WordTrace (prefixWord ++ tailWord_825030) baseStart_825030 baseEnd_825030 := by
    simpa [prefixWord, tailWord_825030, baseEnd_825030] using wordTrace_append hprefix tailTrace_825030
  have hstable : (prefixWord ++ tailWord_825030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825030).length < 2 ^ (prefixWord ++ tailWord_825030).sum := by decide
  have hdescent : baseEnd_825030 < baseStart_825030 := by decide
  rcases family_descends (prefixWord ++ tailWord_825030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825034 : List Nat := [3, 1, 2, 1, 5, 1, 2, 5]
def baseStart_825034 : Nat := 118140960795 + 825034 * 2 ^ 59
def prefixEnd_825034 : Nat := 4983230072969 + 3 ^ 40 * 825034 * 2
def baseEnd_825034 : Nat := 125522666163446010186887

theorem tailTrace_825034 : CollatzResearch.WordTrace tailWord_825034 prefixEnd_825034 125522666163446010186887 := by
  unfold tailWord_825034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522865523262549358580539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20060974728700131622881437 7522865523262549358580539)
  ·
    refine ⟨11284298284893824037870809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7522865523262549358580539 11284298284893824037870809)
    ·
      refine ⟨8463223713670368028403107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11284298284893824037870809 8463223713670368028403107)
      ·
        refine ⟨12694835570505552042604661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8463223713670368028403107 12694835570505552042604661)
        ·
          refine ⟨1190140834734895503994187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12694835570505552042604661 1190140834734895503994187)
          ·
            refine ⟨1785211252102343255991281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190140834734895503994187 1785211252102343255991281)
            ·
              refine ⟨1338908439076757441993461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785211252102343255991281 1338908439076757441993461)
              ·
                refine ⟨125522666163446010186887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1338908439076757441993461 125522666163446010186887)
                ·
                  rfl

theorem cell20_825034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_825034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825034 prefixEnd_825034 := by exact prefixLift 825034
  have htrace : WordTrace (prefixWord ++ tailWord_825034) baseStart_825034 baseEnd_825034 := by
    simpa [prefixWord, tailWord_825034, baseEnd_825034] using wordTrace_append hprefix tailTrace_825034
  have hstable : (prefixWord ++ tailWord_825034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825034).length < 2 ^ (prefixWord ++ tailWord_825034).sum := by decide
  have hdescent : baseEnd_825034 < baseStart_825034 := by decide
  rcases family_descends (prefixWord ++ tailWord_825034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825037 : List Nat := [1, 6, 2, 1, 1, 2, 1, 3, 3]
def baseStart_825037 : Nat := 118140960795 + 825037 * 2 ^ 59
def prefixEnd_825037 : Nat := 4983230072969 + 3 ^ 40 * 825037 * 2
def baseEnd_825037 : Nat := 376569367772083353460649

theorem tailTrace_825037 : CollatzResearch.WordTrace tailWord_825037 prefixEnd_825037 376569367772083353460649 := by
  unfold tailWord_825037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30091571512039328946681365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20061047674692885964454243 30091571512039328946681365)
  ·
    refine ⟨1410542414626843544375689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30091571512039328946681365 1410542414626843544375689)
    ·
      refine ⟨1057906810970132658281767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1410542414626843544375689 1057906810970132658281767)
      ·
        refine ⟨1586860216455198987422651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057906810970132658281767 1586860216455198987422651)
        ·
          refine ⟨2380290324682798481133977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586860216455198987422651 2380290324682798481133977)
          ·
            refine ⟨1785217743512098860850483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2380290324682798481133977 1785217743512098860850483)
            ·
              refine ⟨2677826615268148291275725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785217743512098860850483 2677826615268148291275725)
              ·
                refine ⟨1004184980725555609228397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2677826615268148291275725 1004184980725555609228397)
                ·
                  refine ⟨376569367772083353460649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004184980725555609228397 376569367772083353460649)
                  ·
                    rfl

theorem cell20_825037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_825037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825037 prefixEnd_825037 := by exact prefixLift 825037
  have htrace : WordTrace (prefixWord ++ tailWord_825037) baseStart_825037 baseEnd_825037 := by
    simpa [prefixWord, tailWord_825037, baseEnd_825037] using wordTrace_append hprefix tailTrace_825037
  have hstable : (prefixWord ++ tailWord_825037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825037).length < 2 ^ (prefixWord ++ tailWord_825037).sum := by decide
  have hdescent : baseEnd_825037 < baseStart_825037 := by decide
  rcases family_descends (prefixWord ++ tailWord_825037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825041 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 3]
def baseStart_825041 : Nat := 118140960795 + 825041 * 2 ^ 59
def prefixEnd_825041 : Nat := 4983230072969 + 3 ^ 40 * 825041 * 2
def baseEnd_825041 : Nat := 376571193481077117327299

theorem tailTrace_825041 : CollatzResearch.WordTrace tailWord_825041 prefixEnd_825041 376571193481077117327299 := by
  unfold tailWord_825041
  simp only [CollatzResearch.WordTrace]
  refine ⟨30091717404024837629826977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20061144936016558419884651 30091717404024837629826977)
  ·
    refine ⟨22568788053018628222370233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30091717404024837629826977 22568788053018628222370233)
    ·
      refine ⟨16926591039763971166777675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22568788053018628222370233 16926591039763971166777675)
      ·
        refine ⟨25389886559645956750166513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16926591039763971166777675 25389886559645956750166513)
        ·
          refine ⟨19042414919734467562624885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25389886559645956750166513 19042414919734467562624885)
          ·
            refine ⟨1785226398725106333996083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19042414919734467562624885 1785226398725106333996083)
            ·
              refine ⟨2677839598087659500994125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785226398725106333996083 2677839598087659500994125)
              ·
                refine ⟨1004189849282872312872797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2677839598087659500994125 1004189849282872312872797)
                ·
                  refine ⟨376571193481077117327299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004189849282872312872797 376571193481077117327299)
                  ·
                    rfl

theorem cell20_825041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_825041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825041 prefixEnd_825041 := by exact prefixLift 825041
  have htrace : WordTrace (prefixWord ++ tailWord_825041) baseStart_825041 baseEnd_825041 := by
    simpa [prefixWord, tailWord_825041, baseEnd_825041] using wordTrace_append hprefix tailTrace_825041
  have hstable : (prefixWord ++ tailWord_825041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825041).length < 2 ^ (prefixWord ++ tailWord_825041).sum := by decide
  have hdescent : baseEnd_825041 < baseStart_825041 := by decide
  rcases family_descends (prefixWord ++ tailWord_825041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825134 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_825134 : Nat := 118140960795 + 825134 * 2 ^ 59
def prefixEnd_825134 : Nat := 4983230072969 + 3 ^ 40 * 825134 * 2
def baseEnd_825134 : Nat := 376613641215182127226919

theorem tailTrace_825134 : CollatzResearch.WordTrace tailWord_825134 prefixEnd_825134 376613641215182127226919 := by
  unfold tailWord_825134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761888674085989314120307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20063406261791943008641637 3761888674085989314120307)
  ·
    refine ⟨5642833011128983971180461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3761888674085989314120307 5642833011128983971180461)
    ·
      refine ⟨2116062379173368989192673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5642833011128983971180461 2116062379173368989192673)
      ·
        refine ⟨1587046784380026741894505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2116062379173368989192673 1587046784380026741894505)
        ·
          refine ⟨1190285088285020056420879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587046784380026741894505 1190285088285020056420879)
          ·
            refine ⟨1785427632427530084631319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190285088285020056420879 1785427632427530084631319)
            ·
              refine ⟨2678141448641295126946979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785427632427530084631319 2678141448641295126946979)
              ·
                refine ⟨4017212172961942690420469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2678141448641295126946979 4017212172961942690420469)
                ·
                  refine ⟨376613641215182127226919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4017212172961942690420469 376613641215182127226919)
                  ·
                    rfl

theorem cell20_825134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_825134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825134 prefixEnd_825134 := by exact prefixLift 825134
  have htrace : WordTrace (prefixWord ++ tailWord_825134) baseStart_825134 baseEnd_825134 := by
    simpa [prefixWord, tailWord_825134, baseEnd_825134] using wordTrace_append hprefix tailTrace_825134
  have hstable : (prefixWord ++ tailWord_825134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825134).length < 2 ^ (prefixWord ++ tailWord_825134).sum := by decide
  have hdescent : baseEnd_825134 < baseStart_825134 := by decide
  rcases family_descends (prefixWord ++ tailWord_825134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825141 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 4]
def baseStart_825141 : Nat := 118140960795 + 825141 * 2 ^ 59
def prefixEnd_825141 : Nat := 4983230072969 + 3 ^ 40 * 825141 * 2
def baseEnd_825141 : Nat := 376616836205921213993557

theorem tailTrace_825141 : CollatzResearch.WordTrace tailWord_825141 prefixEnd_825141 376616836205921213993557 := by
  unfold tailWord_825141
  simp only [CollatzResearch.WordTrace]
  refine ⟨30095364703662554708467277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20063576469108369805644851 30095364703662554708467277)
  ·
    refine ⟨11285761763873458015675229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30095364703662554708467277 11285761763873458015675229)
    ·
      refine ⟨4232160661452546755878211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11285761763873458015675229 4232160661452546755878211)
      ·
        refine ⟨6348240992178820133817317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4232160661452546755878211 6348240992178820133817317)
        ·
          refine ⟨1190295186033528775090747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6348240992178820133817317 1190295186033528775090747)
          ·
            refine ⟨1785442779050293162636121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190295186033528775090747 1785442779050293162636121)
            ·
              refine ⟨1339082084287719871977091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785442779050293162636121 1339082084287719871977091)
              ·
                refine ⟨2008623126431579807965637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339082084287719871977091 2008623126431579807965637)
                ·
                  refine ⟨376616836205921213993557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008623126431579807965637 376616836205921213993557)
                  ·
                    rfl

theorem cell20_825141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_825141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825141 prefixEnd_825141 := by exact prefixLift 825141
  have htrace : WordTrace (prefixWord ++ tailWord_825141) baseStart_825141 baseEnd_825141 := by
    simpa [prefixWord, tailWord_825141, baseEnd_825141] using wordTrace_append hprefix tailTrace_825141
  have hstable : (prefixWord ++ tailWord_825141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825141).length < 2 ^ (prefixWord ++ tailWord_825141).sum := by decide
  have hdescent : baseEnd_825141 < baseStart_825141 := by decide
  rcases family_descends (prefixWord ++ tailWord_825141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825158 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_825158 : Nat := 118140960795 + 825158 * 2 ^ 59
def prefixEnd_825158 : Nat := 4983230072969 + 3 ^ 40 * 825158 * 2
def baseEnd_825158 : Nat := 376624595469144710426821

theorem tailTrace_825158 : CollatzResearch.WordTrace tailWord_825158 prefixEnd_825158 376624595469144710426821 := by
  unfold tailWord_825158
  simp only [CollatzResearch.WordTrace]
  refine ⟨940499523268780206619879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20063989829733977741224085 940499523268780206619879)
  ·
    refine ⟨1410749284903170309929819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 940499523268780206619879 1410749284903170309929819)
    ·
      refine ⟨2116123927354755464894729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410749284903170309929819 2116123927354755464894729)
      ·
        refine ⟨1587092945516066598671047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2116123927354755464894729 1587092945516066598671047)
        ·
          refine ⟨2380639418274099898006571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587092945516066598671047 2380639418274099898006571)
          ·
            refine ⟨3570959127411149847009857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380639418274099898006571 3570959127411149847009857)
            ·
              refine ⟨2678219345558362385257393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570959127411149847009857 2678219345558362385257393)
              ·
                refine ⟨2008664509168771788943045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2678219345558362385257393 2008664509168771788943045)
                ·
                  refine ⟨376624595469144710426821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2008664509168771788943045 376624595469144710426821)
                  ·
                    rfl

theorem cell20_825158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_825158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825158 prefixEnd_825158 := by exact prefixLift 825158
  have htrace : WordTrace (prefixWord ++ tailWord_825158) baseStart_825158 baseEnd_825158 := by
    simpa [prefixWord, tailWord_825158, baseEnd_825158] using wordTrace_append hprefix tailTrace_825158
  have hstable : (prefixWord ++ tailWord_825158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825158).length < 2 ^ (prefixWord ++ tailWord_825158).sum := by decide
  have hdescent : baseEnd_825158 < baseStart_825158 := by decide
  rcases family_descends (prefixWord ++ tailWord_825158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825165 : List Nat := [1, 6, 1, 2, 1, 1, 4, 4]
def baseStart_825165 : Nat := 118140960795 + 825165 * 2 ^ 59
def prefixEnd_825165 : Nat := 4983230072969 + 3 ^ 40 * 825165 * 2
def baseEnd_825165 : Nat := 125542596819961265731153

theorem tailTrace_825165 : CollatzResearch.WordTrace tailWord_825165 prefixEnd_825165 125542596819961265731153 := by
  unfold tailWord_825165
  simp only [CollatzResearch.WordTrace]
  refine ⟨30096240055575606807340949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20064160037050404538227299 30096240055575606807340949)
  ·
    refine ⟨1410761252605106569094107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30096240055575606807340949 1410761252605106569094107)
    ·
      refine ⟨2116141878907659853641161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410761252605106569094107 2116141878907659853641161)
      ·
        refine ⟨1587106409180744890230871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2116141878907659853641161 1587106409180744890230871)
        ·
          refine ⟨2380659613771117335346307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587106409180744890230871 2380659613771117335346307)
          ·
            refine ⟨3570989420656676003019461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380659613771117335346307 3570989420656676003019461)
            ·
              refine ⟨669560516373126750566149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3570989420656676003019461 669560516373126750566149)
              ·
                refine ⟨125542596819961265731153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669560516373126750566149 125542596819961265731153)
                ·
                  rfl

theorem cell20_825165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_825165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825165 prefixEnd_825165 := by exact prefixLift 825165
  have htrace : WordTrace (prefixWord ++ tailWord_825165) baseStart_825165 baseEnd_825165 := by
    simpa [prefixWord, tailWord_825165, baseEnd_825165] using wordTrace_append hprefix tailTrace_825165
  have hstable : (prefixWord ++ tailWord_825165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825165).length < 2 ^ (prefixWord ++ tailWord_825165).sum := by decide
  have hdescent : baseEnd_825165 < baseStart_825165 := by decide
  rcases family_descends (prefixWord ++ tailWord_825165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825169 : List Nat := [1, 2, 2, 1, 5, 2, 1, 6]
def baseStart_825169 : Nat := 118140960795 + 825169 * 2 ^ 59
def prefixEnd_825169 : Nat := 4983230072969 + 3 ^ 40 * 825169 * 2
def baseEnd_825169 : Nat := 125543205389625853686703

theorem tailTrace_825169 : CollatzResearch.WordTrace tailWord_825169 prefixEnd_825169 125543205389625853686703 := by
  unfold tailWord_825169
  simp only [CollatzResearch.WordTrace]
  refine ⟨30096385947561115490486561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20064257298374076993657707 30096385947561115490486561)
  ·
    refine ⟨22572289460670836617864921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30096385947561115490486561 22572289460670836617864921)
    ·
      refine ⟨16929217095503127463398691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22572289460670836617864921 16929217095503127463398691)
      ·
        refine ⟨25393825643254691195098037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16929217095503127463398691 25393825643254691195098037)
        ·
          refine ⟨2380671154055127299540441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25393825643254691195098037 2380671154055127299540441)
          ·
            refine ⟨1785503365541345474655331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2380671154055127299540441 1785503365541345474655331)
            ·
              refine ⟨2678255048312018211982997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785503365541345474655331 2678255048312018211982997)
              ·
                refine ⟨125543205389625853686703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2678255048312018211982997 125543205389625853686703)
                ·
                  rfl

theorem cell20_825169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_825169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825169 prefixEnd_825169 := by exact prefixLift 825169
  have htrace : WordTrace (prefixWord ++ tailWord_825169) baseStart_825169 baseEnd_825169 := by
    simpa [prefixWord, tailWord_825169, baseEnd_825169] using wordTrace_append hprefix tailTrace_825169
  have hstable : (prefixWord ++ tailWord_825169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825169).length < 2 ^ (prefixWord ++ tailWord_825169).sum := by decide
  have hdescent : baseEnd_825169 < baseStart_825169 := by decide
  rcases family_descends (prefixWord ++ tailWord_825169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825175 : List Nat := [1, 1, 3, 2, 6, 1, 1, 3, 2]
def baseStart_825175 : Nat := 118140960795 + 825175 * 2 ^ 59
def prefixEnd_825175 : Nat := 4983230072969 + 3 ^ 40 * 825175 * 2
def baseEnd_825175 : Nat := 376632354732368206860085

theorem tailTrace_825175 : CollatzResearch.WordTrace tailWord_825175 prefixEnd_825175 376632354732368206860085 := by
  unfold tailWord_825175
  simp only [CollatzResearch.WordTrace]
  refine ⟨30096604785539378515204979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20064403190359585676803319 30096604785539378515204979)
  ·
    refine ⟨45144907178309067772807469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30096604785539378515204979 45144907178309067772807469)
    ·
      refine ⟨16929340191865900414802801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45144907178309067772807469 16929340191865900414802801)
      ·
        refine ⟨12697005143899425311102101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16929340191865900414802801 12697005143899425311102101)
        ·
          refine ⟨595172116120285561457911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12697005143899425311102101 595172116120285561457911)
          ·
            refine ⟨892758174180428342186867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595172116120285561457911 892758174180428342186867)
            ·
              refine ⟨1339137261270642513280301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892758174180428342186867 1339137261270642513280301)
              ·
                refine ⟨502176472976490942480113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1339137261270642513280301 502176472976490942480113)
                ·
                  refine ⟨376632354732368206860085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502176472976490942480113 376632354732368206860085)
                  ·
                    rfl

theorem cell20_825175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 2].length) (baseStart_825175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825175 prefixEnd_825175 := by exact prefixLift 825175
  have htrace : WordTrace (prefixWord ++ tailWord_825175) baseStart_825175 baseEnd_825175 := by
    simpa [prefixWord, tailWord_825175, baseEnd_825175] using wordTrace_append hprefix tailTrace_825175
  have hstable : (prefixWord ++ tailWord_825175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825175).length < 2 ^ (prefixWord ++ tailWord_825175).sum := by decide
  have hdescent : baseEnd_825175 < baseStart_825175 := by decide
  rcases family_descends (prefixWord ++ tailWord_825175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825186 : List Nat := [3, 3, 2, 1, 2, 3, 6]
def baseStart_825186 : Nat := 118140960795 + 825186 * 2 ^ 59
def prefixEnd_825186 : Nat := 4983230072969 + 3 ^ 40 * 825186 * 2
def baseEnd_825186 : Nat := 41848597270233450832597

theorem tailTrace_825186 : CollatzResearch.WordTrace tailWord_825186 prefixEnd_825186 41848597270233450832597 := by
  unfold tailWord_825186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524251497124881848463853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20064670658999684929236941 7524251497124881848463853)
  ·
    refine ⟨2821594311421830693173945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7524251497124881848463853 2821594311421830693173945)
    ·
      refine ⟨2116195733566373019880459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2821594311421830693173945 2116195733566373019880459)
      ·
        refine ⟨3174293600349559529820689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116195733566373019880459 3174293600349559529820689)
        ·
          refine ⟨2380720200262169647365517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3174293600349559529820689 2380720200262169647365517)
          ·
            refine ⟨892770075098313617762069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2380720200262169647365517 892770075098313617762069)
            ·
              refine ⟨41848597270233450832597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 892770075098313617762069 41848597270233450832597)
              ·
                rfl

theorem cell20_825186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 6].length) (baseStart_825186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825186 prefixEnd_825186 := by exact prefixLift 825186
  have htrace : WordTrace (prefixWord ++ tailWord_825186) baseStart_825186 baseEnd_825186 := by
    simpa [prefixWord, tailWord_825186, baseEnd_825186] using wordTrace_append hprefix tailTrace_825186
  have hstable : (prefixWord ++ tailWord_825186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825186).length < 2 ^ (prefixWord ++ tailWord_825186).sum := by decide
  have hdescent : baseEnd_825186 < baseStart_825186 := by decide
  rcases family_descends (prefixWord ++ tailWord_825186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825196 : List Nat := [2, 2, 1, 1, 4, 3, 3, 2, 2]
def baseStart_825196 : Nat := 118140960795 + 825196 * 2 ^ 59
def prefixEnd_825196 : Nat := 4983230072969 + 3 ^ 40 * 825196 * 2
def baseEnd_825196 : Nat := 376641939704585467159999

theorem tailTrace_825196 : CollatzResearch.WordTrace tailWord_825196 prefixEnd_825196 376641939704585467159999 := by
  unfold tailWord_825196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15048685359231649550859721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20064913812308866067812961 15048685359231649550859721)
  ·
    refine ⟨11286514019423737163144791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15048685359231649550859721 11286514019423737163144791)
    ·
      refine ⟨16929771029135605744717187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11286514019423737163144791 16929771029135605744717187)
      ·
        refine ⟨25394656543703408617075781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16929771029135605744717187 25394656543703408617075781)
        ·
          refine ⟨4761498101944389115701709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25394656543703408617075781 4761498101944389115701709)
          ·
            refine ⟨1785561788229145918388141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4761498101944389115701709 1785561788229145918388141)
            ·
              refine ⟨669585670585929719395553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1785561788229145918388141 669585670585929719395553)
              ·
                refine ⟨502189252939447289546665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669585670585929719395553 502189252939447289546665)
                ·
                  refine ⟨376641939704585467159999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502189252939447289546665 376641939704585467159999)
                  ·
                    rfl

theorem cell20_825196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_825196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825196 prefixEnd_825196 := by exact prefixLift 825196
  have htrace : WordTrace (prefixWord ++ tailWord_825196) baseStart_825196 baseEnd_825196 := by
    simpa [prefixWord, tailWord_825196, baseEnd_825196] using wordTrace_append hprefix tailTrace_825196
  have hstable : (prefixWord ++ tailWord_825196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825196).length < 2 ^ (prefixWord ++ tailWord_825196).sum := by decide
  have hdescent : baseEnd_825196 < baseStart_825196 := by decide
  rcases family_descends (prefixWord ++ tailWord_825196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825206 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_825206 : Nat := 118140960795 + 825206 * 2 ^ 59
def prefixEnd_825206 : Nat := 4983230072969 + 3 ^ 40 * 825206 * 2
def baseEnd_825206 : Nat := 376646503977069876826625

theorem tailTrace_825206 : CollatzResearch.WordTrace tailWord_825206 prefixEnd_825206 376646503977069876826625 := by
  unfold tailWord_825206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881108465526691925598967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20065156965618047206388981 1881108465526691925598967)
  ·
    refine ⟨2821662698290037888398451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1881108465526691925598967 2821662698290037888398451)
    ·
      refine ⟨4232494047435056832597677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821662698290037888398451 4232494047435056832597677)
      ·
        refine ⟨1587185267788146312224129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4232494047435056832597677 1587185267788146312224129)
        ·
          refine ⟨1190388950841109734168097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587185267788146312224129 1190388950841109734168097)
          ·
            refine ⟨892791713130832300626073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190388950841109734168097 892791713130832300626073)
            ·
              refine ⟨669593784848124225469555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892791713130832300626073 669593784848124225469555)
              ·
                refine ⟨1004390677272186338204333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669593784848124225469555 1004390677272186338204333)
                ·
                  refine ⟨376646503977069876826625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004390677272186338204333 376646503977069876826625)
                  ·
                    rfl

theorem cell20_825206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_825206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825206 prefixEnd_825206 := by exact prefixLift 825206
  have htrace : WordTrace (prefixWord ++ tailWord_825206) baseStart_825206 baseEnd_825206 := by
    simpa [prefixWord, tailWord_825206, baseEnd_825206] using wordTrace_append hprefix tailTrace_825206
  have hstable : (prefixWord ++ tailWord_825206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825206).length < 2 ^ (prefixWord ++ tailWord_825206).sum := by decide
  have hdescent : baseEnd_825206 < baseStart_825206 := by decide
  rcases family_descends (prefixWord ++ tailWord_825206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825221 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_825221 : Nat := 118140960795 + 825221 * 2 ^ 59
def prefixEnd_825221 : Nat := 4983230072969 + 3 ^ 40 * 825221 * 2
def baseEnd_825221 : Nat := 376653350385796491326563

theorem tailTrace_825221 : CollatzResearch.WordTrace tailWord_825221 prefixEnd_825221 376653350385796491326563 := by
  unfold tailWord_825221
  simp only [CollatzResearch.WordTrace]
  refine ⟨30098282543372728371379517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20065521695581818914253011 30098282543372728371379517)
  ·
    refine ⟨11286855953764773139267319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30098282543372728371379517 11286855953764773139267319)
    ·
      refine ⟨16930283930647159708900979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11286855953764773139267319 16930283930647159708900979)
      ·
        refine ⟨25395425895970739563351469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16930283930647159708900979 25395425895970739563351469)
        ·
          refine ⟨9523284710989027336256801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25395425895970739563351469 9523284710989027336256801)
          ·
            refine ⟨7142463533241770502192601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9523284710989027336256801 7142463533241770502192601)
            ·
              refine ⟨5356847649931327876644451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7142463533241770502192601 5356847649931327876644451)
              ·
                refine ⟨8035271474896991814966677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356847649931327876644451 8035271474896991814966677)
                ·
                  refine ⟨376653350385796491326563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8035271474896991814966677 376653350385796491326563)
                  ·
                    rfl

theorem cell20_825221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_825221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825221 prefixEnd_825221 := by exact prefixLift 825221
  have htrace : WordTrace (prefixWord ++ tailWord_825221) baseStart_825221 baseEnd_825221 := by
    simpa [prefixWord, tailWord_825221, baseEnd_825221] using wordTrace_append hprefix tailTrace_825221
  have hstable : (prefixWord ++ tailWord_825221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825221).length < 2 ^ (prefixWord ++ tailWord_825221).sum := by decide
  have hdescent : baseEnd_825221 < baseStart_825221 := by decide
  rcases family_descends (prefixWord ++ tailWord_825221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825269 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 3]
def baseStart_825269 : Nat := 118140960795 + 825269 * 2 ^ 59
def prefixEnd_825269 : Nat := 4983230072969 + 3 ^ 40 * 825269 * 2
def baseEnd_825269 : Nat := 376675258893721657726367

theorem tailTrace_825269 : CollatzResearch.WordTrace tailWord_825269 prefixEnd_825269 376675258893721657726367 := by
  unfold tailWord_825269
  simp only [CollatzResearch.WordTrace]
  refine ⟨30100033247198832569126861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20066688831465888379417907 30100033247198832569126861)
  ·
    refine ⟨11287512467699562213422573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30100033247198832569126861 11287512467699562213422573)
    ·
      refine ⟨4232817175387335830033465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11287512467699562213422573 4232817175387335830033465)
      ·
        refine ⟨3174612881540501872525099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4232817175387335830033465 3174612881540501872525099)
        ·
          refine ⟨4761919322310752808787649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174612881540501872525099 4761919322310752808787649)
          ·
            refine ⟨3571439491733064606590737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4761919322310752808787649 3571439491733064606590737)
            ·
              refine ⟨2678579618799798454943053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3571439491733064606590737 2678579618799798454943053)
              ·
                refine ⟨1004467357049924420603645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2678579618799798454943053 1004467357049924420603645)
                ·
                  refine ⟨376675258893721657726367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004467357049924420603645 376675258893721657726367)
                  ·
                    rfl

theorem cell20_825269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_825269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825269 prefixEnd_825269 := by exact prefixLift 825269
  have htrace : WordTrace (prefixWord ++ tailWord_825269) baseStart_825269 baseEnd_825269 := by
    simpa [prefixWord, tailWord_825269, baseEnd_825269] using wordTrace_append hprefix tailTrace_825269
  have hstable : (prefixWord ++ tailWord_825269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825269).length < 2 ^ (prefixWord ++ tailWord_825269).sum := by decide
  have hdescent : baseEnd_825269 < baseStart_825269 := by decide
  rcases family_descends (prefixWord ++ tailWord_825269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825304 : List Nat := [2, 1, 2, 2, 2, 2, 9]
def baseStart_825304 : Nat := 118140960795 + 825304 * 2 ^ 59
def prefixEnd_825304 : Nat := 4983230072969 + 3 ^ 40 * 825304 * 2
def baseEnd_825304 : Nat := 41854581538601899062173

theorem tailTrace_825304 : CollatzResearch.WordTrace tailWord_825304 prefixEnd_825304 41854581538601899062173 := by
  unfold tailWord_825304
  simp only [CollatzResearch.WordTrace]
  refine ⟨15050654901036016773325483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20067539868048022364433977 15050654901036016773325483)
  ·
    refine ⟨22575982351554025159988225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15050654901036016773325483 22575982351554025159988225)
    ·
      refine ⟨16931986763665518869991169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22575982351554025159988225 16931986763665518869991169)
      ·
        refine ⟨12698990072749139152493377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16931986763665518869991169 12698990072749139152493377)
        ·
          refine ⟨9524242554561854364370033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12698990072749139152493377 9524242554561854364370033)
          ·
            refine ⟨7143181915921390773277525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9524242554561854364370033 7143181915921390773277525)
            ·
              refine ⟨41854581538601899062173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7143181915921390773277525 41854581538601899062173)
              ·
                rfl

theorem cell20_825304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 9].length) (baseStart_825304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825304 prefixEnd_825304 := by exact prefixLift 825304
  have htrace : WordTrace (prefixWord ++ tailWord_825304) baseStart_825304 baseEnd_825304 := by
    simpa [prefixWord, tailWord_825304, baseEnd_825304] using wordTrace_append hprefix tailTrace_825304
  have hstable : (prefixWord ++ tailWord_825304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825304).length < 2 ^ (prefixWord ++ tailWord_825304).sum := by decide
  have hdescent : baseEnd_825304 < baseStart_825304 := by decide
  rcases family_descends (prefixWord ++ tailWord_825304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825328 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_825328 : Nat := 118140960795 + 825328 * 2 ^ 59
def prefixEnd_825328 : Nat := 4983230072969 + 3 ^ 40 * 825328 * 2
def baseEnd_825328 : Nat := 376702188101379674759459

theorem tailTrace_825328 : CollatzResearch.WordTrace tailWord_825328 prefixEnd_825328 376702188101379674759459 := by
  unfold tailWord_825328
  simp only [CollatzResearch.WordTrace]
  refine ⟨15051092576992542822762319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20068123435990057097016425 15051092576992542822762319)
  ·
    refine ⟨22576638865488814234143479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15051092576992542822762319 22576638865488814234143479)
    ·
      refine ⟨33864958298233221351215219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22576638865488814234143479 33864958298233221351215219)
      ·
        refine ⟨50797437447349832026822829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33864958298233221351215219 50797437447349832026822829)
        ·
          refine ⟨19049039042756187010058561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50797437447349832026822829 19049039042756187010058561)
          ·
            refine ⟨14286779282067140257543921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19049039042756187010058561 14286779282067140257543921)
            ·
              refine ⟨10715084461550355193157941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14286779282067140257543921 10715084461550355193157941)
              ·
                refine ⟨1004539168270345799358557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10715084461550355193157941 1004539168270345799358557)
                ·
                  refine ⟨376702188101379674759459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004539168270345799358557 376702188101379674759459)
                  ·
                    rfl

theorem cell20_825328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_825328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825328 prefixEnd_825328 := by exact prefixLift 825328
  have htrace : WordTrace (prefixWord ++ tailWord_825328) baseStart_825328 baseEnd_825328 := by
    simpa [prefixWord, tailWord_825328, baseEnd_825328] using wordTrace_append hprefix tailTrace_825328
  have hstable : (prefixWord ++ tailWord_825328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825328).length < 2 ^ (prefixWord ++ tailWord_825328).sum := by decide
  have hdescent : baseEnd_825328 < baseStart_825328 := by decide
  rcases family_descends (prefixWord ++ tailWord_825328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825334 : List Nat := [5, 1, 1, 1, 5, 1, 2, 4]
def baseStart_825334 : Nat := 118140960795 + 825334 * 2 ^ 59
def prefixEnd_825334 : Nat := 4983230072969 + 3 ^ 40 * 825334 * 2
def baseEnd_825334 : Nat := 125568308888290106853145

theorem tailTrace_825334 : CollatzResearch.WordTrace tailWord_825334 prefixEnd_825334 125568308888290106853145 := by
  unfold tailWord_825334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881400249497709291890191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20068269327975565780162037 1881400249497709291890191)
  ·
    refine ⟨2822100374246563937835287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1881400249497709291890191 2822100374246563937835287)
    ·
      refine ⟨4233150561369845906752931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822100374246563937835287 4233150561369845906752931)
      ·
        refine ⟨6349725842054768860129397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233150561369845906752931 6349725842054768860129397)
        ·
          refine ⟨595286797692634580637131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6349725842054768860129397 595286797692634580637131)
          ·
            refine ⟨892930196538951870955697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595286797692634580637131 892930196538951870955697)
            ·
              refine ⟨669697647404213903216773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892930196538951870955697 669697647404213903216773)
              ·
                refine ⟨125568308888290106853145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 669697647404213903216773 125568308888290106853145)
                ·
                  rfl

theorem cell20_825334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_825334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825334 prefixEnd_825334 := by exact prefixLift 825334
  have htrace : WordTrace (prefixWord ++ tailWord_825334) baseStart_825334 baseEnd_825334 := by
    simpa [prefixWord, tailWord_825334, baseEnd_825334] using wordTrace_append hprefix tailTrace_825334
  have hstable : (prefixWord ++ tailWord_825334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825334).length < 2 ^ (prefixWord ++ tailWord_825334).sum := by decide
  have hdescent : baseEnd_825334 < baseStart_825334 := by decide
  rcases family_descends (prefixWord ++ tailWord_825334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825387 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_825387 : Nat := 118140960795 + 825387 * 2 ^ 59
def prefixEnd_825387 : Nat := 4983230072969 + 3 ^ 40 * 825387 * 2
def baseEnd_825387 : Nat := 376729117309037691792551

theorem tailTrace_825387 : CollatzResearch.WordTrace tailWord_825387 prefixEnd_825387 376729117309037691792551 := by
  unfold tailWord_825387
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104337060771338721922415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20069558040514225814614943 30104337060771338721922415)
  ·
    refine ⟨45156505591157008082883623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30104337060771338721922415 45156505591157008082883623)
    ·
      refine ⟨67734758386735512124325435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45156505591157008082883623 67734758386735512124325435)
      ·
        refine ⟨101602137580103268186488153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67734758386735512124325435 101602137580103268186488153)
        ·
          refine ⟨76201603185077451139866115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101602137580103268186488153 76201603185077451139866115)
          ·
            refine ⟨114302404777616176709799173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76201603185077451139866115 114302404777616176709799173)
            ·
              refine ⟨21431700895803033133087345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114302404777616176709799173 21431700895803033133087345)
              ·
                refine ⟨16073775671852274849815509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21431700895803033133087345 16073775671852274849815509)
                ·
                  refine ⟨376729117309037691792551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16073775671852274849815509 376729117309037691792551)
                  ·
                    rfl

theorem cell20_825387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_825387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825387 prefixEnd_825387 := by exact prefixLift 825387
  have htrace : WordTrace (prefixWord ++ tailWord_825387) baseStart_825387 baseEnd_825387 := by
    simpa [prefixWord, tailWord_825387, baseEnd_825387] using wordTrace_append hprefix tailTrace_825387
  have hstable : (prefixWord ++ tailWord_825387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825387).length < 2 ^ (prefixWord ++ tailWord_825387).sum := by decide
  have hdescent : baseEnd_825387 < baseStart_825387 := by decide
  rcases family_descends (prefixWord ++ tailWord_825387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825449 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_825449 : Nat := 118140960795 + 825449 * 2 ^ 59
def prefixEnd_825449 : Nat := 4983230072969 + 3 ^ 40 * 825449 * 2
def baseEnd_825449 : Nat := 376757415798441031725631

theorem tailTrace_825449 : CollatzResearch.WordTrace tailWord_825449 prefixEnd_825449 376757415798441031725631 := by
  unfold tailWord_825449
  simp only [CollatzResearch.WordTrace]
  refine ⟨30106598386546723310679401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20071065591031148873786267 30106598386546723310679401)
  ·
    refine ⟨22579948789910042483009551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30106598386546723310679401 22579948789910042483009551)
    ·
      refine ⟨33869923184865063724514327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22579948789910042483009551 33869923184865063724514327)
      ·
        refine ⟨50804884777297595586771491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33869923184865063724514327 50804884777297595586771491)
        ·
          refine ⟨76207327165946393380157237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50804884777297595586771491 76207327165946393380157237)
          ·
            refine ⟨7144436921807474379389741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76207327165946393380157237 7144436921807474379389741)
            ·
              refine ⟨2679163845677802892271153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7144436921807474379389741 2679163845677802892271153)
              ·
                refine ⟨2009372884258352169203365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679163845677802892271153 2009372884258352169203365)
                ·
                  refine ⟨376757415798441031725631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009372884258352169203365 376757415798441031725631)
                  ·
                    rfl

theorem cell20_825449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_825449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825449 prefixEnd_825449 := by exact prefixLift 825449
  have htrace : WordTrace (prefixWord ++ tailWord_825449) baseStart_825449 baseEnd_825449 := by
    simpa [prefixWord, tailWord_825449, baseEnd_825449] using wordTrace_append hprefix tailTrace_825449
  have hstable : (prefixWord ++ tailWord_825449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825449).length < 2 ^ (prefixWord ++ tailWord_825449).sum := by decide
  have hdescent : baseEnd_825449 < baseStart_825449 := by decide
  rcases family_descends (prefixWord ++ tailWord_825449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825462 : List Nat := [5, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_825462 : Nat := 118140960795 + 825462 * 2 ^ 59
def prefixEnd_825462 : Nat := 4983230072969 + 3 ^ 40 * 825462 * 2
def baseEnd_825462 : Nat := 376763349352670764292245

theorem tailTrace_825462 : CollatzResearch.WordTrace tailWord_825462 prefixEnd_825462 376763349352670764292245 := by
  unfold tailWord_825462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881692033468726658181415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20071381690333084353935093 1881692033468726658181415)
  ·
    refine ⟨2822538050203089987272123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1881692033468726658181415 2822538050203089987272123)
    ·
      refine ⟨4233807075304634980908185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822538050203089987272123 4233807075304634980908185)
      ·
        refine ⟨3175355306478476235681139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4233807075304634980908185 3175355306478476235681139)
        ·
          refine ⟨4763032959717714353521709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175355306478476235681139 4763032959717714353521709)
          ·
            refine ⟨1786137359894142882570641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4763032959717714353521709 1786137359894142882570641)
            ·
              refine ⟨1339603019920607161927981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786137359894142882570641 1339603019920607161927981)
              ·
                refine ⟨502351132470227685722993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1339603019920607161927981 502351132470227685722993)
                ·
                  refine ⟨376763349352670764292245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502351132470227685722993 376763349352670764292245)
                  ·
                    rfl

theorem cell20_825462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_825462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825462 prefixEnd_825462 := by exact prefixLift 825462
  have htrace : WordTrace (prefixWord ++ tailWord_825462) baseStart_825462 baseEnd_825462 := by
    simpa [prefixWord, tailWord_825462, baseEnd_825462] using wordTrace_append hprefix tailTrace_825462
  have hstable : (prefixWord ++ tailWord_825462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825462).length < 2 ^ (prefixWord ++ tailWord_825462).sum := by decide
  have hdescent : baseEnd_825462 < baseStart_825462 := by decide
  rcases family_descends (prefixWord ++ tailWord_825462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825473 : List Nat := [1, 2, 4, 2, 3, 1, 7]
def baseStart_825473 : Nat := 118140960795 + 825473 * 2 ^ 59
def prefixEnd_825473 : Nat := 4983230072969 + 3 ^ 40 * 825473 * 2
def baseEnd_825473 : Nat := 41863152228044846102837

theorem tailTrace_825473 : CollatzResearch.WordTrace tailWord_825473 prefixEnd_825473 41863152228044846102837 := by
  unfold tailWord_825473
  simp only [CollatzResearch.WordTrace]
  refine ⟨30107473738459775409553073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20071649158973183606368715 30107473738459775409553073)
  ·
    refine ⟨22580605303844831557164805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30107473738459775409553073 22580605303844831557164805)
    ·
      refine ⟨4233863494470905916968401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22580605303844831557164805 4233863494470905916968401)
      ·
        refine ⟨3175397620853179437726301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4233863494470905916968401 3175397620853179437726301)
        ·
          refine ⟨1190774107819942289147363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3175397620853179437726301 1190774107819942289147363)
          ·
            refine ⟨1786161161729913433721045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190774107819942289147363 1786161161729913433721045)
            ·
              refine ⟨41863152228044846102837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1786161161729913433721045 41863152228044846102837)
              ·
                rfl

theorem cell20_825473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 7].length) (baseStart_825473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825473 prefixEnd_825473 := by exact prefixLift 825473
  have htrace : WordTrace (prefixWord ++ tailWord_825473) baseStart_825473 baseEnd_825473 := by
    simpa [prefixWord, tailWord_825473, baseEnd_825473] using wordTrace_append hprefix tailTrace_825473
  have hstable : (prefixWord ++ tailWord_825473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825473).length < 2 ^ (prefixWord ++ tailWord_825473).sum := by decide
  have hdescent : baseEnd_825473 < baseStart_825473 := by decide
  rcases family_descends (prefixWord ++ tailWord_825473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825524 : List Nat := [2, 5, 3, 1, 1, 2, 6]
def baseStart_825524 : Nat := 118140960795 + 825524 * 2 ^ 59
def prefixEnd_825524 : Nat := 4983230072969 + 3 ^ 40 * 825524 * 2
def baseEnd_825524 : Nat := 41865738649119344913925

theorem tailTrace_825524 : CollatzResearch.WordTrace tailWord_825524 prefixEnd_825524 41865738649119344913925 := by
  unfold tailWord_825524
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054666930637505559829813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20072889240850007413106417 15054666930637505559829813)
  ·
    refine ⟨1411375024747266146234045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15054666930637505559829813 1411375024747266146234045)
    ·
      refine ⟨529265634280224804837767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1411375024747266146234045 529265634280224804837767)
      ·
        refine ⟨793898451420337207256651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529265634280224804837767 793898451420337207256651)
        ·
          refine ⟨1190847677130505810884977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793898451420337207256651 1190847677130505810884977)
          ·
            refine ⟨893135757847879358163733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190847677130505810884977 893135757847879358163733)
            ·
              refine ⟨41865738649119344913925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 893135757847879358163733 41865738649119344913925)
              ·
                rfl

theorem cell20_825524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 6].length) (baseStart_825524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825524 prefixEnd_825524 := by exact prefixLift 825524
  have htrace : WordTrace (prefixWord ++ tailWord_825524) baseStart_825524 baseEnd_825524 := by
    simpa [prefixWord, tailWord_825524, baseEnd_825524] using wordTrace_append hprefix tailTrace_825524
  have hstable : (prefixWord ++ tailWord_825524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825524).length < 2 ^ (prefixWord ++ tailWord_825524).sum := by decide
  have hdescent : baseEnd_825524 < baseStart_825524 := by decide
  rcases family_descends (prefixWord ++ tailWord_825524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825538 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_825538 : Nat := 118140960795 + 825538 * 2 ^ 59
def prefixEnd_825538 : Nat := 4983230072969 + 3 ^ 40 * 825538 * 2
def baseEnd_825538 : Nat := 376798037823552277758601

theorem tailTrace_825538 : CollatzResearch.WordTrace tailWord_825538 prefixEnd_825538 376798037823552277758601 := by
  unfold tailWord_825538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7527461120806072877667317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20073229655482861007112845 7527461120806072877667317)
  ·
    refine ⟨705699480075569332281311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7527461120806072877667317 705699480075569332281311)
    ·
      refine ⟨1058549220113353998421967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705699480075569332281311 1058549220113353998421967)
      ·
        refine ⟨1587823830170030997632951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058549220113353998421967 1587823830170030997632951)
        ·
          refine ⟨2381735745255046496449427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587823830170030997632951 2381735745255046496449427)
          ·
            refine ⟨3572603617882569744674141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381735745255046496449427 3572603617882569744674141)
            ·
              refine ⟨1339726356705963654252803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3572603617882569744674141 1339726356705963654252803)
              ·
                refine ⟨2009589535058945481379205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339726356705963654252803 2009589535058945481379205)
                ·
                  refine ⟨376798037823552277758601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009589535058945481379205 376798037823552277758601)
                  ·
                    rfl

theorem cell20_825538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_825538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825538 prefixEnd_825538 := by exact prefixLift 825538
  have htrace : WordTrace (prefixWord ++ tailWord_825538) baseStart_825538 baseEnd_825538 := by
    simpa [prefixWord, tailWord_825538, baseEnd_825538] using wordTrace_append hprefix tailTrace_825538
  have hstable : (prefixWord ++ tailWord_825538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825538).length < 2 ^ (prefixWord ++ tailWord_825538).sum := by decide
  have hdescent : baseEnd_825538 < baseStart_825538 := by decide
  rcases family_descends (prefixWord ++ tailWord_825538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825548 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 3]
def baseStart_825548 : Nat := 118140960795 + 825548 * 2 ^ 59
def prefixEnd_825548 : Nat := 4983230072969 + 3 ^ 40 * 825548 * 2
def baseEnd_825548 : Nat := 376802602096036687425227

theorem tailTrace_825548 : CollatzResearch.WordTrace tailWord_825548 prefixEnd_825548 376802602096036687425227 := by
  unfold tailWord_825548
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055104606594031609266649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20073472808792042145688865 15055104606594031609266649)
  ·
    refine ⟨11291328454945523706949987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15055104606594031609266649 11291328454945523706949987)
    ·
      refine ⟨16936992682418285560424981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11291328454945523706949987 16936992682418285560424981)
      ·
        refine ⟨793921531988357135644921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16936992682418285560424981 793921531988357135644921)
        ·
          refine ⟨595441148991267851733691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793921531988357135644921 595441148991267851733691)
          ·
            refine ⟨893161723486901777600537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595441148991267851733691 893161723486901777600537)
            ·
              refine ⟨669871292615176333200403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893161723486901777600537 669871292615176333200403)
              ·
                refine ⟨1004806938922764499800605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669871292615176333200403 1004806938922764499800605)
                ·
                  refine ⟨376802602096036687425227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004806938922764499800605 376802602096036687425227)
                  ·
                    rfl

theorem cell20_825548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_825548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825548 prefixEnd_825548 := by exact prefixLift 825548
  have htrace : WordTrace (prefixWord ++ tailWord_825548) baseStart_825548 baseEnd_825548 := by
    simpa [prefixWord, tailWord_825548, baseEnd_825548] using wordTrace_append hprefix tailTrace_825548
  have hstable : (prefixWord ++ tailWord_825548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825548).length < 2 ^ (prefixWord ++ tailWord_825548).sum := by decide
  have hdescent : baseEnd_825548 < baseStart_825548 := by decide
  rcases family_descends (prefixWord ++ tailWord_825548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825580 : List Nat := [2, 2, 1, 1, 2, 3, 2, 5, 2]
def baseStart_825580 : Nat := 118140960795 + 825580 * 2 ^ 59
def prefixEnd_825580 : Nat := 4983230072969 + 3 ^ 40 * 825580 * 2
def baseEnd_825580 : Nat := 376817207767986798358429

theorem tailTrace_825580 : CollatzResearch.WordTrace tailWord_825580 prefixEnd_825580 376817207767986798358429 := by
  unfold tailWord_825580
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055688174536066341849097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20074250899381421789132129 15055688174536066341849097)
  ·
    refine ⟨11291766130902049756386823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15055688174536066341849097 11291766130902049756386823)
    ·
      refine ⟨16937649196353074634580235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11291766130902049756386823 16937649196353074634580235)
      ·
        refine ⟨25406473794529611951870353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16937649196353074634580235 25406473794529611951870353)
        ·
          refine ⟨19054855345897208963902765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25406473794529611951870353 19054855345897208963902765)
          ·
            refine ⟨7145570754711453361463537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19054855345897208963902765 7145570754711453361463537)
            ·
              refine ⟨5359178066033590021097653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7145570754711453361463537 5359178066033590021097653)
              ·
                refine ⟨502422943690649064477905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5359178066033590021097653 502422943690649064477905)
                ·
                  refine ⟨376817207767986798358429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502422943690649064477905 376817207767986798358429)
                  ·
                    rfl

theorem cell20_825580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_825580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825580 prefixEnd_825580 := by exact prefixLift 825580
  have htrace : WordTrace (prefixWord ++ tailWord_825580) baseStart_825580 baseEnd_825580 := by
    simpa [prefixWord, tailWord_825580, baseEnd_825580] using wordTrace_append hprefix tailTrace_825580
  have hstable : (prefixWord ++ tailWord_825580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825580).length < 2 ^ (prefixWord ++ tailWord_825580).sum := by decide
  have hdescent : baseEnd_825580 < baseStart_825580 := by decide
  rcases family_descends (prefixWord ++ tailWord_825580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825594 : List Nat := [3, 1, 1, 1, 1, 5, 1, 4, 3]
def baseStart_825594 : Nat := 118140960795 + 825594 * 2 ^ 59
def prefixEnd_825594 : Nat := 4983230072969 + 3 ^ 40 * 825594 * 2
def baseEnd_825594 : Nat := 376823597749464971891705

theorem tailTrace_825594 : CollatzResearch.WordTrace tailWord_825594 prefixEnd_825594 376823597749464971891705 := by
  unfold tailWord_825594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7527971742755353268676959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20074591314014275383138557 7527971742755353268676959)
  ·
    refine ⟨11291957614133029903015439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7527971742755353268676959 11291957614133029903015439)
    ·
      refine ⟨16937936421199544854523159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11291957614133029903015439 16937936421199544854523159)
      ·
        refine ⟨25406904631799317281784739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16937936421199544854523159 25406904631799317281784739)
        ·
          refine ⟨38110356947698975922677109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25406904631799317281784739 38110356947698975922677109)
          ·
            refine ⟨3572845963846778992750979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38110356947698975922677109 3572845963846778992750979)
            ·
              refine ⟨5359268945770168489126469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3572845963846778992750979 5359268945770168489126469)
              ·
                refine ⟨1004862927331906591711213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5359268945770168489126469 1004862927331906591711213)
                ·
                  refine ⟨376823597749464971891705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004862927331906591711213 376823597749464971891705)
                  ·
                    rfl

theorem cell20_825594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_825594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825594 prefixEnd_825594 := by exact prefixLift 825594
  have htrace : WordTrace (prefixWord ++ tailWord_825594) baseStart_825594 baseEnd_825594 := by
    simpa [prefixWord, tailWord_825594, baseEnd_825594] using wordTrace_append hprefix tailTrace_825594
  have hstable : (prefixWord ++ tailWord_825594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825594).length < 2 ^ (prefixWord ++ tailWord_825594).sum := by decide
  have hdescent : baseEnd_825594 < baseStart_825594 := by decide
  rcases family_descends (prefixWord ++ tailWord_825594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825601 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_825601 : Nat := 118140960795 + 825601 * 2 ^ 59
def prefixEnd_825601 : Nat := 4983230072969 + 3 ^ 40 * 825601 * 2
def baseEnd_825601 : Nat := 376826792740204058658343

theorem tailTrace_825601 : CollatzResearch.WordTrace tailWord_825601 prefixEnd_825601 376826792740204058658343 := by
  unfold tailWord_825601
  simp only [CollatzResearch.WordTrace]
  refine ⟨30112142281996053270212657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20074761521330702180141771 30112142281996053270212657)
  ·
    refine ⟨22584106711497039952659493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30112142281996053270212657 22584106711497039952659493)
    ·
      refine ⟨4234520008405694991123655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22584106711497039952659493 4234520008405694991123655)
      ·
        refine ⟨6351780012608542486685483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234520008405694991123655 6351780012608542486685483)
        ·
          refine ⟨9527670018912813730028225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351780012608542486685483 9527670018912813730028225)
          ·
            refine ⟨7145752514184610297521169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9527670018912813730028225 7145752514184610297521169)
            ·
              refine ⟨5359314385638457723140877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7145752514184610297521169 5359314385638457723140877)
              ·
                refine ⟨2009742894614421646177829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5359314385638457723140877 2009742894614421646177829)
                ·
                  refine ⟨376826792740204058658343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2009742894614421646177829 376826792740204058658343)
                  ·
                    rfl

theorem cell20_825601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_825601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825601 prefixEnd_825601 := by exact prefixLift 825601
  have htrace : WordTrace (prefixWord ++ tailWord_825601) baseStart_825601 baseEnd_825601 := by
    simpa [prefixWord, tailWord_825601, baseEnd_825601] using wordTrace_append hprefix tailTrace_825601
  have hstable : (prefixWord ++ tailWord_825601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825601).length < 2 ^ (prefixWord ++ tailWord_825601).sum := by decide
  have hdescent : baseEnd_825601 < baseStart_825601 := by decide
  rcases family_descends (prefixWord ++ tailWord_825601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825604 : List Nat := [2, 3, 2, 2, 3, 2, 1, 5]
def baseStart_825604 : Nat := 118140960795 + 825604 * 2 ^ 59
def prefixEnd_825604 : Nat := 4983230072969 + 3 ^ 40 * 825604 * 2
def baseEnd_825604 : Nat := 125609387340649793852777

theorem tailTrace_825604 : CollatzResearch.WordTrace tailWord_825604 prefixEnd_825604 125609387340649793852777 := by
  unfold tailWord_825604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15056125850492592391285933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20074834467323456521714577 15056125850492592391285933)
  ·
    refine ⟨5646047193934722146732225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15056125850492592391285933 5646047193934722146732225)
    ·
      refine ⟨4234535395451041610049169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5646047193934722146732225 4234535395451041610049169)
      ·
        refine ⟨3175901546588281207536877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4234535395451041610049169 3175901546588281207536877)
        ·
          refine ⟨1190963079970605452826329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3175901546588281207536877 1190963079970605452826329)
          ·
            refine ⟨893222309977954089619747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190963079970605452826329 893222309977954089619747)
            ·
              refine ⟨1339833464966931134429621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893222309977954089619747 1339833464966931134429621)
              ·
                refine ⟨125609387340649793852777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1339833464966931134429621 125609387340649793852777)
                ·
                  rfl

theorem cell20_825604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_825604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825604 prefixEnd_825604 := by exact prefixLift 825604
  have htrace : WordTrace (prefixWord ++ tailWord_825604) baseStart_825604 baseEnd_825604 := by
    simpa [prefixWord, tailWord_825604, baseEnd_825604] using wordTrace_append hprefix tailTrace_825604
  have hstable : (prefixWord ++ tailWord_825604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825604).length < 2 ^ (prefixWord ++ tailWord_825604).sum := by decide
  have hdescent : baseEnd_825604 < baseStart_825604 := by decide
  rcases family_descends (prefixWord ++ tailWord_825604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825645 : List Nat := [1, 5, 3, 1, 2, 2, 1, 2, 3]
def baseStart_825645 : Nat := 118140960795 + 825645 * 2 ^ 59
def prefixEnd_825645 : Nat := 4983230072969 + 3 ^ 40 * 825645 * 2
def baseEnd_825645 : Nat := 376846875539135461191497

theorem tailTrace_825645 : CollatzResearch.WordTrace tailWord_825645 prefixEnd_825645 376846875539135461191497 := by
  unfold tailWord_825645
  simp only [CollatzResearch.WordTrace]
  refine ⟨30113747093836648784814389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20075831395891099189876259 30113747093836648784814389)
  ·
    refine ⟨2823163790047185823576349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30113747093836648784814389 2823163790047185823576349)
    ·
      refine ⟨1058686421267694683841131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2823163790047185823576349 1058686421267694683841131)
      ·
        refine ⟨1588029631901542025761697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058686421267694683841131 1588029631901542025761697)
        ·
          refine ⟨1191022223926156519321273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1588029631901542025761697 1191022223926156519321273)
          ·
            refine ⟨893266667944617389490955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1191022223926156519321273 893266667944617389490955)
            ·
              refine ⟨1339900001916926084236433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893266667944617389490955 1339900001916926084236433)
              ·
                refine ⟨1004925001437694563177325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339900001916926084236433 1004925001437694563177325)
                ·
                  refine ⟨376846875539135461191497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004925001437694563177325 376846875539135461191497)
                  ·
                    rfl

theorem cell20_825645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_825645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825645 prefixEnd_825645 := by exact prefixLift 825645
  have htrace : WordTrace (prefixWord ++ tailWord_825645) baseStart_825645 baseEnd_825645 := by
    simpa [prefixWord, tailWord_825645, baseEnd_825645] using wordTrace_append hprefix tailTrace_825645
  have hstable : (prefixWord ++ tailWord_825645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825645).length < 2 ^ (prefixWord ++ tailWord_825645).sum := by decide
  have hdescent : baseEnd_825645 < baseStart_825645 := by decide
  rcases family_descends (prefixWord ++ tailWord_825645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825656 : List Nat := [2, 1, 2, 1, 3, 1, 4, 4, 2]
def baseStart_825656 : Nat := 118140960795 + 825656 * 2 ^ 59
def prefixEnd_825656 : Nat := 4983230072969 + 3 ^ 40 * 825656 * 2
def baseEnd_825656 : Nat := 376851896238868311824785

theorem tailTrace_825656 : CollatzResearch.WordTrace tailWord_825656 prefixEnd_825656 376851896238868311824785 := by
  unfold tailWord_825656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15057074148398398831732411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20076098864531198442309881 15057074148398398831732411)
  ·
    refine ⟨22585611222597598247598617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15057074148398398831732411 22585611222597598247598617)
    ·
      refine ⟨16939208416948198685698963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22585611222597598247598617 16939208416948198685698963)
      ·
        refine ⟨25408812625422298028548445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16939208416948198685698963 25408812625422298028548445)
        ·
          refine ⟨9528304734533361760705667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25408812625422298028548445 9528304734533361760705667)
          ·
            refine ⟨14292457101800042641058501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528304734533361760705667 14292457101800042641058501)
            ·
              refine ⟨2679835706587507995198469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14292457101800042641058501 2679835706587507995198469)
              ·
                refine ⟨502469194985157749099713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2679835706587507995198469 502469194985157749099713)
                ·
                  refine ⟨376851896238868311824785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502469194985157749099713 376851896238868311824785)
                  ·
                    rfl

theorem cell20_825656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_825656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825656 prefixEnd_825656 := by exact prefixLift 825656
  have htrace : WordTrace (prefixWord ++ tailWord_825656) baseStart_825656 baseEnd_825656 := by
    simpa [prefixWord, tailWord_825656, baseEnd_825656] using wordTrace_append hprefix tailTrace_825656
  have hstable : (prefixWord ++ tailWord_825656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825656).length < 2 ^ (prefixWord ++ tailWord_825656).sum := by decide
  have hdescent : baseEnd_825656 < baseStart_825656 := by decide
  rcases family_descends (prefixWord ++ tailWord_825656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825725 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 3]
def baseStart_825725 : Nat := 118140960795 + 825725 * 2 ^ 59
def prefixEnd_825725 : Nat := 4983230072969 + 3 ^ 40 * 825725 * 2
def baseEnd_825725 : Nat := 376883389719010738524503

theorem tailTrace_825725 : CollatzResearch.WordTrace tailWord_825725 prefixEnd_825725 376883389719010738524503 := by
  unfold tailWord_825725
  simp only [CollatzResearch.WordTrace]
  refine ⟨30116664933546822447726629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20077776622364548298484419 30116664933546822447726629)
  ·
    refine ⟨5646874675040029208948743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30116664933546822447726629 5646874675040029208948743)
    ·
      refine ⟨8470312012560043813423115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5646874675040029208948743 8470312012560043813423115)
      ·
        refine ⟨12705468018840065720134673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8470312012560043813423115 12705468018840065720134673)
        ·
          refine ⟨9529101014130049290101005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12705468018840065720134673 9529101014130049290101005)
          ·
            refine ⟨3573412880298768483787877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9529101014130049290101005 3573412880298768483787877)
            ·
              refine ⟨670014915056019090710227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3573412880298768483787877 670014915056019090710227)
              ·
                refine ⟨1005022372584028636065341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670014915056019090710227 1005022372584028636065341)
                ·
                  refine ⟨376883389719010738524503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1005022372584028636065341 376883389719010738524503)
                  ·
                    rfl

theorem cell20_825725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_825725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825725 prefixEnd_825725 := by exact prefixLift 825725
  have htrace : WordTrace (prefixWord ++ tailWord_825725) baseStart_825725 baseEnd_825725 := by
    simpa [prefixWord, tailWord_825725, baseEnd_825725] using wordTrace_append hprefix tailTrace_825725
  have hstable : (prefixWord ++ tailWord_825725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825725).length < 2 ^ (prefixWord ++ tailWord_825725).sum := by decide
  have hdescent : baseEnd_825725 < baseStart_825725 := by decide
  rcases family_descends (prefixWord ++ tailWord_825725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825773 : List Nat := [1, 5, 2, 2, 3, 1, 1, 5]
def baseStart_825773 : Nat := 118140960795 + 825773 * 2 ^ 59
def prefixEnd_825773 : Nat := 4983230072969 + 3 ^ 40 * 825773 * 2
def baseEnd_825773 : Nat := 125635099408978634974769

theorem tailTrace_825773 : CollatzResearch.WordTrace tailWord_825773 prefixEnd_825773 125635099408978634974769 := by
  unfold tailWord_825773
  simp only [CollatzResearch.WordTrace]
  refine ⟨30118415637372926645473973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20078943758248617763649315 30118415637372926645473973)
  ·
    refine ⟨2823601466003711873013185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30118415637372926645473973 2823601466003711873013185)
    ·
      refine ⟨2117701099502783904759889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2823601466003711873013185 2117701099502783904759889)
      ·
        refine ⟨1588275824627087928569917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2117701099502783904759889 1588275824627087928569917)
        ·
          refine ⟨595603434235157973213719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1588275824627087928569917 595603434235157973213719)
          ·
            refine ⟨893405151352736959820579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595603434235157973213719 893405151352736959820579)
            ·
              refine ⟨1340107727029105439730869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893405151352736959820579 1340107727029105439730869)
              ·
                refine ⟨125635099408978634974769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1340107727029105439730869 125635099408978634974769)
                ·
                  rfl

theorem cell20_825773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5].length) (baseStart_825773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_825773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_825773 prefixEnd_825773 := by exact prefixLift 825773
  have htrace : WordTrace (prefixWord ++ tailWord_825773) baseStart_825773 baseEnd_825773 := by
    simpa [prefixWord, tailWord_825773, baseEnd_825773] using wordTrace_append hprefix tailTrace_825773
  have hstable : (prefixWord ++ tailWord_825773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825773).length < 2 ^ (prefixWord ++ tailWord_825773).sum := by decide
  have hdescent : baseEnd_825773 < baseStart_825773 := by decide
  rcases family_descends (prefixWord ++ tailWord_825773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
